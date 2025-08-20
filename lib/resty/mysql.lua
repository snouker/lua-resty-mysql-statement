-- Copyright (C) Yichun Zhang (agentzh)


local bit = require "bit"
local resty_sha256 = require "resty.sha256"
local sub = string.sub
local tcp = ngx.socket.tcp
local strbyte = string.byte
local strchar = string.char
local strfind = string.find
local format = string.format
local strrep = string.rep
local null = ngx.null
local band = bit.band
local bxor = bit.bxor
local bor = bit.bor
local lshift = bit.lshift
local rshift = bit.rshift
local tohex = bit.tohex
local sha1 = ngx.sha1_bin
local concat = table.concat
local setmetatable = setmetatable
local error = error
local tonumber = tonumber
local to_int = math.floor

local has_rsa, resty_rsa = pcall(require, "resty.rsa")

local statement_cache = {} -- statement缓存

if not ngx.config then
    error("ngx_lua 0.9.11+ or ngx_stream_lua required")
end

if (not ngx.config.subsystem
    or ngx.config.subsystem == "http") -- subsystem is http
   and (not ngx.config.ngx_lua_version
        or ngx.config.ngx_lua_version < 9011) -- old version
then
    error("ngx_lua 0.9.11+ required")
end


local ok, new_tab = pcall(require, "table.new")
if not ok then
    new_tab = function (narr, nrec) return {} end
end


local _M = { _VERSION = '0.27' }


-- constants

local STATE_CONNECTED = 1
local STATE_COMMAND_SENT = 2

local COM_QUIT = 0x01
local COM_QUERY = 0x03

-- refer to https://dev.mysql.com/doc/internals/en/capability-flags.html#packet-Protocol::CapabilityFlags
-- CLIENT_LONG_PASSWORD | CLIENT_FOUND_ROWS | CLIENT_LONG_FLAG
-- | CLIENT_CONNECT_WITH_DB | CLIENT_ODBC | CLIENT_LOCAL_FILES
-- | CLIENT_IGNORE_SPACE | CLIENT_PROTOCOL_41 | CLIENT_INTERACTIVE
-- | CLIENT_IGNORE_SIGPIPE | CLIENT_TRANSACTIONS | CLIENT_RESERVED
-- | CLIENT_SECURE_CONNECTION | CLIENT_MULTI_STATEMENTS | CLIENT_MULTI_RESULTS
local DEFAULT_CLIENT_FLAGS = 0x3f7cf
local CLIENT_SSL = 0x00000800
local CLIENT_PLUGIN_AUTH = 0x00080000
local CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA = 0x00200000
local DEFAULT_AUTH_PLUGIN = "mysql_native_password"

local SERVER_MORE_RESULTS_EXISTS = 8

local RESP_OK = "OK"
local RESP_AUTHMOREDATA = "AUTHMOREDATA"
local RESP_LOCALINFILE = "LOCALINFILE"
local RESP_EOF = "EOF"
local RESP_ERR = "ERR"
local RESP_DATA = "DATA"

local MY_RND_MAX_VAL = 0x3FFFFFFF
local MIN_PROTOCOL_VER = 10

local LEN_NATIVE_SCRAMBLE = 20
local LEN_OLD_SCRAMBLE = 8

-- 16MB - 1, the default max allowed packet size used by libmysqlclient
local FULL_PACKET_SIZE = 16777215

-- the following charset map is generated from the following mysql query:
--   SELECT CHARACTER_SET_NAME, ID
--   FROM information_schema.collations
--   WHERE IS_DEFAULT = 'Yes' ORDER BY id;
local CHARSET_MAP = {
    _default  = 0,
    big5      = 1,
    dec8      = 3,
    cp850     = 4,
    hp8       = 6,
    koi8r     = 7,
    latin1    = 8,
    latin2    = 9,
    swe7      = 10,
    ascii     = 11,
    ujis      = 12,
    sjis      = 13,
    hebrew    = 16,
    tis620    = 18,
    euckr     = 19,
    koi8u     = 22,
    gb2312    = 24,
    greek     = 25,
    cp1250    = 26,
    gbk       = 28,
    latin5    = 30,
    armscii8  = 32,
    utf8      = 33,
    ucs2      = 35,
    cp866     = 36,
    keybcs2   = 37,
    macce     = 38,
    macroman  = 39,
    cp852     = 40,
    latin7    = 41,
    utf8mb4   = 45,
    cp1251    = 51,
    utf16     = 54,
    utf16le   = 56,
    cp1256    = 57,
    cp1257    = 59,
    utf32     = 60,
    binary    = 63,
    geostd8   = 92,
    cp932     = 95,
    eucjpms   = 97,
    gb18030   = 248
}

local mt = { __index = _M }


-- mysql field value type converters
local converters = new_tab(0, 9)

for i = 0x01, 0x05 do
    -- tiny, short, long, float, double
    converters[i] = tonumber
end
converters[0x00] = tonumber  -- decimal
-- converters[0x08] = tonumber  -- long long
converters[0x09] = tonumber  -- int24
converters[0x0d] = tonumber  -- year
converters[0xf6] = tonumber  -- newdecimal


local function _get_byte2(data, i)
    local a, b = strbyte(data, i, i + 1)
    return bor(a, lshift(b, 8)), i + 2
end


local function _get_byte3(data, i)
    local a, b, c = strbyte(data, i, i + 2)
    return bor(a, lshift(b, 8), lshift(c, 16)), i + 3
end


local function _get_byte4(data, i)
    local a, b, c, d = strbyte(data, i, i + 3)
    return bor(a, lshift(b, 8), lshift(c, 16), lshift(d, 24)), i + 4
end


local function _get_byte8(data, i)
    local a, b, c, d, e, f, g, h = strbyte(data, i, i + 7)

    -- XXX workaround for the lack of 64-bit support in bitop:
    -- XXX return results in the range of signed 32 bit numbers
    local lo = bor(a, lshift(b, 8), lshift(c, 16))
    local hi = bor(e, lshift(f, 8), lshift(g, 16), lshift(h, 24))
    return lo + 16777216 * d + hi * 4294967296, i + 8

    -- return bor(a, lshift(b, 8), lshift(c, 16), lshift(d, 24), lshift(e, 32),
               -- lshift(f, 40), lshift(g, 48), lshift(h, 56)), i + 8
end


local function _set_byte2(n)
    return strchar(band(n, 0xff), band(rshift(n, 8), 0xff))
end


local function _set_byte3(n)
    return strchar(band(n, 0xff),
                   band(rshift(n, 8), 0xff),
                   band(rshift(n, 16), 0xff))
end


local function _set_byte4(n)
    return strchar(band(n, 0xff),
                   band(rshift(n, 8), 0xff),
                   band(rshift(n, 16), 0xff),
                   band(rshift(n, 24), 0xff))
end


local function _from_cstring(data, i)
    local last = strfind(data, "\0", i, true)
    if not last then
        return nil, nil
    end

    return sub(data, i, last - 1), last + 1
end


local function _to_cstring(data)
    return data .. "\0"
end


local function _dump(data)
    local len = #data
    local bytes = new_tab(len, 0)
    for i = 1, len do
        bytes[i] = format("%x", strbyte(data, i))
    end
    return concat(bytes, " ")
end


local function _dumphex(data)
    local len = #data
    local bytes = new_tab(len, 0)
    for i = 1, len do
        bytes[i] = tohex(strbyte(data, i), 2)
    end
    return concat(bytes, " ")
end


local function _pwd_hash(password)
    local add = 7

    local hash1 = 1345345333
    local hash2 = 0x12345671

    local len = #password
    for i = 1, len do
        -- skip spaces and tabs in password
        local byte = strbyte(password, i)
        if byte ~= 32 and byte ~= 9 then -- not ' ' or '\t'
            hash1 = bxor(hash1, (band(hash1, 63) + add) * byte
                                + lshift(hash1, 8))

            hash2 = bxor(lshift(hash2, 8), hash1) + hash2

            add = add + byte
        end
    end

    -- remove sign bit (1<<31)-1)
    return band(hash1, 0x7FFFFFFF), band(hash2, 0x7FFFFFFF)
end


local function _random_byte(seed1, seed2)
    seed1 = (seed1 * 3 + seed2) % MY_RND_MAX_VAL
    seed2 = (seed1 + seed2 + 33) % MY_RND_MAX_VAL

    return to_int(seed1 * 31 / MY_RND_MAX_VAL), seed1, seed2
end


local function _compute_old_token(password, scramble)
    if password == "" then
        return ""
    end

    scramble = sub(scramble, 1, LEN_OLD_SCRAMBLE)

    local hash_pw1, hash_pw2 = _pwd_hash(password)
    local hash_sc1, hash_sc2 = _pwd_hash(scramble)

    local seed1 = bxor(hash_pw1, hash_sc1) % MY_RND_MAX_VAL
    local seed2 = bxor(hash_pw2, hash_sc2) % MY_RND_MAX_VAL
    local rand_byte

    local bytes = new_tab(LEN_OLD_SCRAMBLE, 0)
    for i = 1, LEN_OLD_SCRAMBLE do
        rand_byte, seed1, seed2 = _random_byte(seed1, seed2)
        bytes[i] = rand_byte + 64
    end

    rand_byte = _random_byte(seed1, seed2)
    for i = 1, LEN_OLD_SCRAMBLE do
        bytes[i] = strchar(bxor(bytes[i], rand_byte))
    end

    return _to_cstring(concat(bytes))
end


local function _compute_sha256_token(password, scramble)
    if password == "" then
        return ""
    end

    local sha256 = resty_sha256:new()
    if not sha256 then
        return nil, "failed to create the sha256 object"
    end

    if not sha256:update(password) then
        return nil, "failed to update string to sha256"
    end

    local message1 = sha256:final()

    sha256:reset()

    if not sha256:update(message1) then
        return nil, "failed to update string to sha256"
    end

    local message1_hash = sha256:final()

    sha256:reset()

    if not sha256:update(message1_hash) then
        return nil, "failed to update string to sha256"
    end

    if not sha256:update(scramble) then
        return nil, "failed to update string to sha256"
    end

    local message2 = sha256:final()

    local n = #message2
    local bytes = new_tab(n, 0)
    for i = 1, n do
        bytes[i] = strchar(bxor(strbyte(message1, i), strbyte(message2, i)))
    end

    return concat(bytes)
end


local function _compute_token(password, scramble)
    if password == "" then
        return ""
    end

    scramble = sub(scramble, 1, LEN_NATIVE_SCRAMBLE)

    local stage1 = sha1(password)
    local stage2 = sha1(stage1)
    local stage3 = sha1(scramble .. stage2)
    local n = #stage1
    local bytes = new_tab(n, 0)
    for i = 1, n do
        bytes[i] = strchar(bxor(strbyte(stage3, i), strbyte(stage1, i)))
    end

    return concat(bytes)
end


local function _send_packet(self, req, size)
    local sock = self.sock

    if self.packet_no == nil then
        self.packet_no = 0
    end

    self.packet_no = self.packet_no + 1

    -- print("packet no: ", self.packet_no)

    local packet = _set_byte3(size) .. strchar(band(self.packet_no, 255)) .. req

    -- print("sending packet: ", _dump(packet))

    -- print("sending packet... of size " .. #packet)

    return sock:send(packet)
end


local function _recv_packet(self)
    local sock = self.sock

    local data, err = sock:receive(4) -- packet header
    if not data then
        return nil, nil, "failed to receive packet header: " .. err
    end

    --print("packet header: ", _dump(data))

    local len, pos = _get_byte3(data, 1)

    --print("packet length: ", len)

    if len == 0 then
        return nil, nil, "empty packet"
    end

    if len > self._max_packet_size then
        return nil, nil, "packet size too big: " .. len
    end

    local num = strbyte(data, pos)

    --print("recv packet: packet no: ", num)

    self.packet_no = num

    data, err = sock:receive(len)

    --print("receive returned")

    if not data then
        return nil, nil, "failed to read packet content: " .. err
    end

    --print("packet content: ", _dump(data))
    --print("packet content (ascii): ", data)

    local field_count = strbyte(data, 1)

    local typ
    if field_count == 0x00 then
        typ = RESP_OK
    elseif field_count == 0x01 then
        typ = RESP_AUTHMOREDATA
    elseif field_count == 0xfb then
        typ = RESP_LOCALINFILE
    elseif field_count == 0xfe then
        typ = RESP_EOF
    elseif field_count == 0xff then
        typ = RESP_ERR
    else
        typ = RESP_DATA
    end

    return data, typ
end


local function _from_length_coded_bin(data, pos)
    local first = strbyte(data, pos)

    --print("LCB: first: ", first)

    if not first then
        return nil, pos
    end

    if first >= 0 and first <= 250 then
        return first, pos + 1
    end

    if first == 251 then
        return null, pos + 1
    end

    if first == 252 then
        pos = pos + 1
        return _get_byte2(data, pos)
    end

    if first == 253 then
        pos = pos + 1
        return _get_byte3(data, pos)
    end

    if first == 254 then
        pos = pos + 1
        return _get_byte8(data, pos)
    end

    return nil, pos + 1
end


local function _from_length_coded_str(data, pos)
    local len
    len, pos = _from_length_coded_bin(data, pos)
    if not len or len == null then
        return null, pos
    end

    return sub(data, pos, pos + len - 1), pos + len
end


local function _parse_ok_packet(packet)
    local res = new_tab(0, 5)
    local pos

    res.affected_rows, pos = _from_length_coded_bin(packet, 2)

    --print("affected rows: ", res.affected_rows, ", pos:", pos)

    res.insert_id, pos = _from_length_coded_bin(packet, pos)

    --print("insert id: ", res.insert_id, ", pos:", pos)

    res.server_status, pos = _get_byte2(packet, pos)

    --print("server status: ", res.server_status, ", pos:", pos)

    res.warning_count, pos = _get_byte2(packet, pos)

    --print("warning count: ", res.warning_count, ", pos: ", pos)

    local message = _from_length_coded_str(packet, pos)
    if message and message ~= null then
        res.message = message
    end

    --print("message: ", res.message, ", pos:", pos)

    return res
end


local function _parse_eof_packet(packet)
    local pos = 2

    local warning_count, pos = _get_byte2(packet, pos)
    local status_flags = _get_byte2(packet, pos)

    return warning_count, status_flags
end


local function _parse_err_packet(packet)
    local errno, pos = _get_byte2(packet, 2)
    local marker = sub(packet, pos, pos)
    local sqlstate
    if marker == '#' then
        -- with sqlstate
        pos = pos + 1
        sqlstate = sub(packet, pos, pos + 5 - 1)
        pos = pos + 5
    end

    local message = sub(packet, pos)
    return errno, message, sqlstate
end


local function _parse_result_set_header_packet(packet)
    local field_count, pos = _from_length_coded_bin(packet, 1)

    local extra
    extra = _from_length_coded_bin(packet, pos)

    return field_count, extra
end


local function _parse_field_packet(data)
    local col = new_tab(0, 2)
    local catalog, db, table, orig_table, orig_name, charsetnr, length
    local pos
    catalog, pos = _from_length_coded_str(data, 1)

    --print("catalog: ", col.catalog, ", pos:", pos)

    db, pos = _from_length_coded_str(data, pos)
    table, pos = _from_length_coded_str(data, pos)
    orig_table, pos = _from_length_coded_str(data, pos)
    col.name, pos = _from_length_coded_str(data, pos)

    orig_name, pos = _from_length_coded_str(data, pos)

    pos = pos + 1 -- ignore the filler

    charsetnr, pos = _get_byte2(data, pos)

    length, pos = _get_byte4(data, pos)

    col.type = strbyte(data, pos)

    --[[
    pos = pos + 1

    col.flags, pos = _get_byte2(data, pos)

    col.decimals = strbyte(data, pos)
    pos = pos + 1

    local default = sub(data, pos + 2)
    if default and default ~= "" then
        col.default = default
    end
    --]]

    return col
end


local function _parse_row_data_packet(data, cols, compact)
    local pos = 1
    local ncols = #cols
    local row
    if compact then
        row = new_tab(ncols, 0)
    else
        row = new_tab(0, ncols)
    end
    for i = 1, ncols do
        local value
        value, pos = _from_length_coded_str(data, pos)
        local col = cols[i]
        local typ = col.type
        local name = col.name

        --print("row field value: ", value, ", type: ", typ)

        if value ~= null then
            local conv = converters[typ]
            if conv then
                value = conv(value)
            end
        end

        if compact then
            row[i] = value

        else
            row[name] = value
        end
    end

    return row
end


local function _recv_field_packet(self)
    local packet, typ, err = _recv_packet(self)
    if not packet then
        return nil, err
    end

    if typ == RESP_ERR then
        local errno, msg, sqlstate = _parse_err_packet(packet)
        return nil, msg, errno, sqlstate
    end

    if typ ~= RESP_DATA then
        return nil, "bad field packet type: " .. typ
    end

    -- typ == RESP_DATA

    return _parse_field_packet(packet)
end


-- refer to https://dev.mysql.com/doc/internals/en/connection-phase-packets.html
local function _read_hand_shake_packet(self)
    local packet, typ, err = _recv_packet(self)
    if not packet then
        return nil, nil, err
    end

    if typ == RESP_ERR then
        local errno, msg, sqlstate = _parse_err_packet(packet)
        return nil, nil, msg, errno, sqlstate
    end

    local protocol_ver = tonumber(strbyte(packet))
    if not protocol_ver then
        return nil, nil,
            "bad handshake initialization packet: bad protocol version"
    end

    if protocol_ver < MIN_PROTOCOL_VER then
        return nil, nil, "unsupported protocol version " .. protocol_ver
                         .. ", version " .. MIN_PROTOCOL_VER
                         .. " or higher is required"
    end

    self.protocol_ver = protocol_ver

    local server_ver, pos = _from_cstring(packet, 2)
    if not server_ver then
        return nil, nil,
            "bad handshake initialization packet: bad server version"
    end

    self._server_ver = server_ver

    local thread_id, pos = _get_byte4(packet, pos)
    self.thread_id = thread_id -- 用于记录statement所属连接

    local scramble = sub(packet, pos, pos + 8 - 1)
    if not scramble then
        return nil, nil, "1st part of scramble not found"
    end

    pos = pos + 9 -- skip filler(8 + 1)

    -- two lower bytes
    local capabilities  -- server capabilities
    capabilities, pos = _get_byte2(packet, pos)

    self._server_lang = strbyte(packet, pos)
    pos = pos + 1

    self._server_status, pos = _get_byte2(packet, pos)

    local more_capabilities
    more_capabilities, pos = _get_byte2(packet, pos)

    self.capabilities = bor(capabilities, lshift(more_capabilities, 16))

    pos = pos + 11 -- skip length of auth-plugin-data(1) and reserved(10)

    -- follow official Python library uses the fixed length 12
    -- and the 13th byte is "\0 byte
    local scramble_part2 = sub(packet, pos, pos + 12 - 1)
    if not scramble_part2 then
        return nil, nil, "2nd part of scramble not found"
    end

    pos = pos + 13

    local plugin, _
    if band(self.capabilities, CLIENT_PLUGIN_AUTH) > 0 then
        plugin, _ = _from_cstring(packet, pos)
        if not plugin then
            -- EOF if version (>= 5.5.7 and < 5.5.10) or (>= 5.6.0 and < 5.6.2)
            -- \NUL otherwise
            plugin = sub(packet, pos)
        end

    else
        plugin = DEFAULT_AUTH_PLUGIN
    end

    return scramble .. scramble_part2, plugin
end


local function _append_auth_length(self, data)
    local n = #data

    if n <= 250 then
        data = strchar(n) .. data
        return data, 1 + n
    end

    self.DEFAULT_CLIENT_FLAGS = bor(self.DEFAULT_CLIENT_FLAGS,
                            CLIENT_PLUGIN_AUTH_LENENC_CLIENT_DATA)

    if n <= 0xffff then
        data = strchar(0xfc, band(n, 0xff), band(rshift(n, 8), 0xff)) .. data
        return data, 3 + n
    end

    if n <= 0xffffff then
        data = strchar(0xfd,
                       band(n, 0xff),
                       band(rshift(n, 8), 0xff),
                       band(rshift(n, 16), 0xff))
               .. data
        return data, 4 + n
    end

    data = strchar(0xfe,
                   band(n, 0xff),
                   band(rshift(n, 8), 0xff),
                   band(rshift(n, 16), 0xff),
                   band(rshift(n, 24), 0xff),
                   band(rshift(n, 32), 0xff),
                   band(rshift(n, 40), 0xff),
                   band(rshift(n, 48), 0xff),
                   band(rshift(n, 56), 0xff))
           .. data
    return data, 9 + n
end


local function _write_hand_shake_response(self, auth_resp, plugin)
    local append_auth, len = _append_auth_length(self, auth_resp)

    if self.use_ssl then
        if band(self.capabilities, CLIENT_SSL) == 0 then
            return "ssl disabled on server"
        end

        -- send a SSL Request Packet
        local req = _set_byte4(bor(self.DEFAULT_CLIENT_FLAGS, CLIENT_SSL))
                    .. _set_byte4(self._max_packet_size)
                    .. strchar(self.charset)
                    .. strrep("\0", 23)

        local packet_len = 4 + 4 + 1 + 23
        local bytes, err = _send_packet(self, req, packet_len)
        if not bytes then
            return "failed to send client authentication packet: " .. err
        end

        local sock = self.sock

        local ok, err = sock:sslhandshake(false, nil, self.ssl_verify)
        if not ok then
            return "failed to do ssl handshake: " .. (err or "")
        end
    end

    local req = _set_byte4(self.DEFAULT_CLIENT_FLAGS)
                .. _set_byte4(self._max_packet_size)
                .. strchar(self.charset)
                .. strrep("\0", 23)
                .. _to_cstring(self.user)
                .. append_auth
                .. _to_cstring(self.database)
                .. _to_cstring(plugin)

    local packet_len = 4 + 4 + 1 + 23 + #self.user + 1
        + len + #self.database + 1 + #plugin + 1

    local bytes, err = _send_packet(self, req, packet_len)
    if not bytes then
        return "failed to send client authentication packet: " .. err
    end

    return nil
end


local function _read_auth_result(self, old_auth_data, plugin)
    local packet, typ, err = _recv_packet(self)
    if not packet then
        return nil, nil, "failed to receive the result packet: " .. err
    end

    if typ == RESP_OK then
        return RESP_OK, ""
    end

    if typ == RESP_AUTHMOREDATA then
        return sub(packet, 2), ""
    end

    if typ == RESP_EOF then
        if #packet == 1 then -- old pre-4.1 authentication protocol
            return nil, "mysql_old_password"
        end

        local pos

        plugin, pos = _from_cstring(packet, 2)
        if not plugin then
            return nil, nil, "malformed packet"
        end

        return sub(packet, pos), plugin
    end

    if typ == RESP_ERR then
        local errno, msg, sqlstate = _parse_err_packet(packet)
        return errno, sqlstate, msg
    end

    return nil, nil, "bad packet type: " .. typ
end


local function _read_ok_result(self)
    local packet, typ, err = _recv_packet(self)
    if not packet then
        return "failed to receive the result packet: " .. err
    end

    if typ == RESP_ERR then
        local errno, msg, sqlstate = _parse_err_packet(packet)
        return msg, errno, sqlstate
    end

    if typ ~= RESP_OK then
        return "bad packet type: " .. typ
    end
end


local function _encrypt_password(self, auth_data, public_key)
    if not has_rsa then
        error("auth plugin caching_sha2_password or sha256_password are not" ..
              " supported because resty.rsa is not installed", 2)
    end

    local password = _to_cstring(self.password)
    local n = #password
    local l = #auth_data
    local bytes = new_tab(n, 0)

    for i = 1, n do
        local j = i % l
        bytes[i] = strchar(bxor(strbyte(password, i), strbyte(auth_data, j)))
    end

    local pub, err = resty_rsa:new({
        public_key = public_key,
        key_type = resty_rsa.KEY_TYPE.PKCS8,
        padding = resty_rsa.PADDING.RSA_PKCS1_OAEP_PADDING,
        algorithm = "sha1",
    })
    if not pub then
        return nil, "new rsa err: " .. err
    end

    local enc, err = pub:encrypt(concat(bytes))
    if not enc then
        return nil, "encode password packet: " .. err
    end

    return enc
end


local function _write_encode_password(self, auth_data, public_key)
    local enc, err = _encrypt_password(self, auth_data, public_key)

    local bytes, err = _send_packet(self, enc, #enc)
    if not bytes then
        return "failed to send encode password packet: " .. err
    end
end


local function _auth(self, auth_data, plugin)
    local password = self.password

    if plugin == "caching_sha2_password" then
        local auth_resp, err = _compute_sha256_token(password, auth_data)
        if err then
            return nil, "failed to compute sha256 token: " .. err
        end

        return auth_resp
    end

    if plugin == "mysql_old_password" then
        return _compute_old_token(password, auth_data)
    end

    if plugin == "mysql_clear_password" then
        return _to_cstring(password)
    end

    if plugin == "mysql_native_password" then
        return _compute_token(password, auth_data)
    end

    if plugin == "sha256_password" then
        if self.is_unix or self.use_ssl or #password == 0 then
            return _to_cstring(password)
        end

        local public_key = self.public_key
        if public_key then
            return _encrypt_password(self, auth_data, public_key)
        end

        return "\1" -- request public key from server
    end

    return nil, "unknown plugin: " .. plugin
end


local function _handle_auth_result(self, old_auth_data, plugin)
    local auth_data, new_plugin, err = _read_auth_result(self, old_auth_data,
                                                         plugin)

    if err ~= nil then
        local errno, sqlstate = auth_data, new_plugin
        return err, errno, sqlstate
    end

    if auth_data == RESP_OK then
        return
    end

    if new_plugin ~= "" then
        if not auth_data then
            auth_data = old_auth_data
        else
            old_auth_data = auth_data
        end

        plugin = new_plugin

        local auth_resp, err = _auth(self, auth_data, plugin)
        if not auth_resp then
            return err
        end

        local bytes, err = _send_packet(self, auth_resp, #auth_resp)
        if not bytes then
            return "failed to send client authentication packet: " .. err
        end

        auth_data, new_plugin, err = _read_auth_result(self, old_auth_data,
                                                       plugin)

        if err ~= nil then
            local errno, sqlstate = auth_data, new_plugin
            return err, errno, sqlstate
        end

        if auth_data == RESP_OK then
            return
        end

        if new_plugin ~= "" then
            return "malformed packet"
        end
    end

    if plugin == "caching_sha2_password" then
        local len = #auth_data
        if len == 0 then
            return
        end

        if len == 1 then
            local status = strbyte(auth_data)
            -- caching_sha2_password fast auth success
            if status == 3 then
                return _read_ok_result(self)
            end

            -- caching_sha2_password perform full authentication
            if status == 4 then
                if self.is_unix or self.use_ssl then
                    local bytes, err = _send_packet(self,
                                                    _to_cstring(self.password),
                                                    #self.password + 1)

                    if not bytes then
                        return "failed to send cleartext auth packet: "
                            .. err
                    end

                else
                    local public_key = self.public_key
                    if not public_key then
                        -- caching_sha2_password request public_key
                        local bytes, err = _send_packet(self, "\2", 1)
                        if not bytes then
                            return "failed to send password request packet: "
                                .. err
                        end

                        local packet, _, err = _recv_packet(self)
                        if not packet then
                            return "failed to receive the result packet: "
                                .. err
                        end

                        public_key = sub(packet, 2)
                    end

                    err = _write_encode_password(self, old_auth_data,
                                                 public_key)

                    if err then
                        return err
                    end

                    self.public_key = public_key
                end

                return _read_ok_result(self)
            end
        end

        return "malformed packet"
    end

    if plugin == "sha256_password" then
        if #auth_data ~= 0 then
            local enc, err = _write_encode_password(self, old_auth_data,
                                                    auth_data)

            if err then
                return err
            end

            return _read_ok_result(self)
        end
    end
end


function _M.new()
    local sock, err = tcp()
    if not sock then
        return nil, err
    end
    return setmetatable({ sock = sock }, mt)
end


function _M.set_timeout(self, timeout)
    local sock = self.sock
    if not sock then
        return nil, "not initialized"
    end

    return sock:settimeout(timeout)
end


function _M.connect(self, opts)
    local sock = self.sock
    if not sock then
        return nil, "not initialized"
    end

    local max_packet_size = opts.max_packet_size
    if not max_packet_size then
        max_packet_size = 1024 * 1024 -- default 1 MB
    end
    self._max_packet_size = max_packet_size

    local ok, err

    self.compact = opts.compact_arrays

    self.database = opts.database or ""
    self.user = opts.user or ""

    self.charset = CHARSET_MAP[opts.charset or "_default"]
    if not self.charset then
        return nil, "charset '" .. opts.charset .. "' is not supported"
    end

    local pool = opts.pool

    self.ssl_verify = opts.ssl_verify
    self.use_ssl = opts.ssl or opts.ssl_verify

    self.password = opts.password or ""

    local host = opts.host
    if host then
        local port = opts.port or 3306
        if not pool then
            pool = self.user .. ":" .. self.database .. ":" .. host .. ":"
                   .. port
        end

        ok, err = sock:connect(host, port, { pool = pool,
                               pool_size = opts.pool_size,
                               backlog = opts.backlog })

    else
        local path = opts.path
        if not path then
            return nil, 'neither "host" nor "path" options are specified'
        end

        if not pool then
            pool = self.user .. ":" .. self.database .. ":" .. path
        end

        self.is_unix = true
        ok, err = sock:connect("unix:" .. path, { pool = pool,
                               pool_size = opts.pool_size,
                               backlog = opts.backlog })
    end

    if not ok then
        return nil, 'failed to connect: ' .. err
    end

    local reused = sock:getreusedtimes()

    if reused and reused > 0 then
        self.state = STATE_CONNECTED
        return 1
    end

    self.DEFAULT_CLIENT_FLAGS = bor(DEFAULT_CLIENT_FLAGS, CLIENT_PLUGIN_AUTH)

    local auth_data, plugin, err, errno, sqlstate
        = _read_hand_shake_packet(self)

    if err ~= nil then
        return nil, err
    end

    local auth_resp, err = _auth(self, auth_data, plugin)
    if not auth_resp then
        return nil, err
    end

    err = _write_hand_shake_response(self, auth_resp, plugin)
    if err ~= nil then
        return nil, err
    end

    local err, errno, sqlstate = _handle_auth_result(self, auth_data, plugin)
    if err ~= nil then
        return nil, err, errno, sqlstate
    end

    self.state = STATE_CONNECTED

    return 1
end


---LRU淘汰连接缓存
---@param pool_cache table 缓存
---@param limit integer 限制大小
---@param count integer? 当前大小
local function _evict_lru_thread_id(pool_cache, limit, count)
    local sort_cache = new_tab(count or (limit * 2))
    local i = 1
    for k, v in pairs(pool_cache) do
        sort_cache[i] = { k, v.last_used }
    end
    table.sort(sort_cache, function(a, b)
        if a and b and a[2] > b[2] then
            return true
        else
            return false
        end
    end)
    for i = limit, #sort_cache do
        pool_cache[sort_cache[i][1]] = nil
    end
end


function _M.set_keepalive(self, ...)
    local sock = self.sock
    if not sock then
        return nil, "not initialized"
    end

    if self.state ~= STATE_CONNECTED then
        return nil, "cannot be reused in the current connection state: "
                    .. (self.state or "nil")
    end

    -- 检查并执行LRU淘汰
    local pool_cache = statement_cache[self.pool]
    if self.thread_id and pool_cache and table.nkeys(pool_cache) > self.sockArg.pool_size * 2 then
        _evict_lru_thread_id(pool_cache, self.sockArg.pool_size)
    end


    self.state = nil
    return sock:setkeepalive(...)
end


function _M.get_reused_times(self)
    local sock = self.sock
    if not sock then
        return nil, "not initialized"
    end

    return sock:getreusedtimes()
end


function _M.close(self)
    local sock = self.sock
    if not sock then
        return nil, "not initialized"
    end

    self.state = nil

    local bytes, err = _send_packet(self, strchar(COM_QUIT), 1)
    if not bytes then
        return nil, err
    end

    return sock:close()
end


function _M.server_ver(self)
    return self._server_ver
end


local function send_query(self, query)
    if self.state ~= STATE_CONNECTED then
        return nil, "cannot send query in the current context: "
                    .. (self.state or "nil")
    end

    local sock = self.sock
    if not sock then
        return nil, "not initialized"
    end

    self.packet_no = -1

    local cmd_packet = strchar(COM_QUERY) .. query
    local packet_len = 1 + #query

    local bytes, err = _send_packet(self, cmd_packet, packet_len)
    if not bytes then
        return nil, err
    end

    self.state = STATE_COMMAND_SENT

    --print("packet sent ", bytes, " bytes")

    return bytes
end
_M.send_query = send_query


local function read_result(self, est_nrows)
    if self.state ~= STATE_COMMAND_SENT then
        return nil, "cannot read result in the current context: "
                    .. (self.state or "nil")
    end

    local sock = self.sock
    if not sock then
        return nil, "not initialized"
    end

    local packet, typ, err = _recv_packet(self)
    if not packet then
        return nil, err
    end

    if typ == RESP_ERR then
        self.state = STATE_CONNECTED

        local errno, msg, sqlstate = _parse_err_packet(packet)
        return nil, msg, errno, sqlstate
    end

    if typ == RESP_OK then
        local res = _parse_ok_packet(packet)
        if res and band(res.server_status, SERVER_MORE_RESULTS_EXISTS) ~= 0 then
            return res, "again"
        end

        self.state = STATE_CONNECTED
        return res
    end

    if typ == RESP_LOCALINFILE then
        self.state = STATE_CONNECTED

        return nil, "packet type " .. typ .. " not supported"
    end

    -- typ == RESP_DATA or RESP_AUTHMOREDATA(also mean RESP_DATA here)

    --print("read the result set header packet")

    local field_count, extra = _parse_result_set_header_packet(packet)

    --print("field count: ", field_count)

    local cols = new_tab(field_count, 0)
    for i = 1, field_count do
        local col, err, errno, sqlstate = _recv_field_packet(self)
        if not col then
            return nil, err, errno, sqlstate
        end

        cols[i] = col
    end

    local packet, typ, err = _recv_packet(self)
    if not packet then
        return nil, err
    end

    if typ ~= RESP_EOF then
        return nil, "unexpected packet type " .. typ .. " while eof packet is "
            .. "expected"
    end

    -- typ == RESP_EOF

    local compact = self.compact

    local rows = new_tab(est_nrows or 4, 0)
    local i = 0
    while true do
        --print("reading a row")

        packet, typ, err = _recv_packet(self)
        if not packet then
            return nil, err
        end

        if typ == RESP_EOF then
            local warning_count, status_flags = _parse_eof_packet(packet)

            --print("status flags: ", status_flags)

            if band(status_flags, SERVER_MORE_RESULTS_EXISTS) ~= 0 then
                return rows, "again"
            end

            break
        end

        if typ == RESP_ERR then
            self.state = STATE_CONNECTED
            local errno, msg, sqlstate = _parse_err_packet(packet)
            return nil, msg, errno, sqlstate
        end

        local row = _parse_row_data_packet(packet, cols, compact)
        i = i + 1
        rows[i] = row
    end

    self.state = STATE_CONNECTED

    return rows
end
_M.read_result = read_result


function _M.query(self, query, est_nrows)
    local bytes, err = send_query(self, query)
    if not bytes then
        return nil, "failed to send query: " .. err
    end

    return read_result(self, est_nrows)
end


function _M.set_compact_arrays(self, value)
    self.compact = value
end


---[[
---这里是prepare和statement(新增),部分代码来自https://github.com/iresty/lua-resty-mysql/tree/feature/prepare_statement
---由Gemini修改,本人进行纠正.
---]]

-- MySQL 命令常量
local COM_STMT_PREPARE = 0x16
local COM_STMT_EXECUTE = 0x17
local COM_STMT_CLOSE = 0x19

-- MySQL 类型常量，用于参数绑定
-- 参考: https://dev.mysql.com/doc/internals/en/binary-protocol-value.html
local MYSQL_TYPE_DECIMAL = 0
local MYSQL_TYPE_TINY = 1
local MYSQL_TYPE_SHORT = 2
local MYSQL_TYPE_LONG = 3
local MYSQL_TYPE_FLOAT = 4
local MYSQL_TYPE_DOUBLE = 5
local MYSQL_TYPE_NULL = 6
local MYSQL_TYPE_TIMESTAMP = 7
local MYSQL_TYPE_LONGLONG = 8
local MYSQL_TYPE_INT24 = 9
local MYSQL_TYPE_DATE = 10
local MYSQL_TYPE_TIME = 11
local MYSQL_TYPE_DATETIME = 12
local MYSQL_TYPE_YEAR = 13
local MYSQL_TYPE_NEWDATE = 14
local MYSQL_TYPE_VARCHAR = 15
local MYSQL_TYPE_BIT = 16
local MYSQL_TYPE_TIMESTAMP2 = 17
local MYSQL_TYPE_DATETIME2 = 18
local MYSQL_TYPE_TIME2 = 19
local MYSQL_TYPE_JSON = 245
local MYSQL_TYPE_NEWDECIMAL = 246
local MYSQL_TYPE_ENUM = 247
local MYSQL_TYPE_SET = 248
local MYSQL_TYPE_TINY_BLOB = 249
local MYSQL_TYPE_MEDIUM_BLOB = 250
local MYSQL_TYPE_LONG_BLOB = 251
local MYSQL_TYPE_BLOB = 252
local MYSQL_TYPE_VAR_STRING = 253
local MYSQL_TYPE_STRING = 254

-- FFI 用于高效处理浮点数到字节的转换
local ffi = require("ffi")
ffi.cdef [[
    typedef union { float value; char bytes[4]; } float_u;
    typedef union { double value; char bytes[8]; } double_u;
]]
local c_float_u = ffi.new("float_u")
local c_double_u = ffi.new("double_u")


--- 发送一个带命令头的通用数据包
---@param self Connection 链接实例
---@param data string|table 要发送的数据
---@param cmd_type integer 命令类型 (例如 COM_STMT_PREPARE)
---@return integer? 发送的字节数
---@return string? 错误信息
---@return integer? 错误代码
---@return string? 标准错误码
local function _send_com_packet(self, data, cmd_type)
    if self.state ~= STATE_CONNECTED then
        return nil, "cannot send command in the current context: " .. (self.state or "nil")
    end

    local sock = self.sock
    if not sock then
        return nil, "not initialized"
    end

    self.packet_no = -1
    local packet_len
    local cmd_packet
    if type(data) == "table" then
        cmd_packet = { strchar(cmd_type) }
        packet_len = 1
        for i = 1, #data do
            local part = data[i]
            packet_len = packet_len + #part
            cmd_packet[#cmd_packet + 1] = part
        end
    else
        cmd_packet = strchar(cmd_type) .. data
        packet_len = 1 + #data
    end

    local bytes, err = _send_packet(self, cmd_packet, packet_len)
    if not bytes then
        return nil, err
    end

    self.state = STATE_COMMAND_SENT
    return bytes
end


--- 读取并解析 COM_STMT_PREPARE 的响应
---@param self Connection 链接实例
---@return table? statement 描述表
---@return string? 错误信息
---@return integer? 错误码
---@return string? SQLSTATE
local function _read_prepare_response(self)
    if self.state ~= STATE_COMMAND_SENT then
        return nil, "cannot read result in the current context: " .. (self.state or "nil")
    end

    -- 1. 读取 PREPARE OK Packet
    local packet, typ, err = _recv_packet(self)
    if not packet then
        self.state = STATE_CONNECTED
        return nil, err
    end

    if typ == RESP_ERR then
        self.state = STATE_CONNECTED
        local errno, msg, sqlstate = _parse_err_packet(packet)
        return nil, msg, errno, sqlstate
    end

    if strbyte(packet, 1) ~= 0x00 then
        self.state = STATE_CONNECTED
        return nil, "bad prepare response packet type: " .. typ
    end

    local stmt = new_tab(0, 5)
    local pos
    -- 跳过包头 (1 byte 0x00)
    stmt.statement_id, pos = _get_byte4(packet, 2)
    stmt.columns, pos = _get_byte2(packet, pos)
    stmt.parameters, pos = _get_byte2(packet, pos)
    -- 跳过 filler (1 byte)
    pos = pos + 1
    stmt.warnings, pos = _get_byte2(packet, pos)

    -- 2. 如果有参数，读取参数定义，直到 EOF
    if stmt.parameters > 0 then
        for _ = 1, stmt.parameters do
            packet, typ, err = _recv_packet(self)
            if not packet then
                self.state = STATE_CONNECTED
                return nil, "failed to read parameter definition: " .. err
            end
        end
        -- 读取 EOF
        packet, typ, err = _recv_packet(self)
        if not packet or typ ~= RESP_EOF then
            self.state = STATE_CONNECTED
            return nil, "expected EOF packet after parameters, but got " .. (typ or "nil")
        end
    end

    -- 3. 如果有结果列，读取列定义，直到 EOF
    if stmt.columns > 0 then
        local cols = new_tab(stmt.columns, 0)
        for i = 1, stmt.columns do
            local col, err, errno, sqlstate = _recv_field_packet(self)
            if not col then
                self.state = STATE_CONNECTED
                return nil, err, errno, sqlstate
            end
            cols[i] = col
        end
        stmt.cols = cols
        -- 读取 EOF
        packet, typ, err = _recv_packet(self)
        if not packet or typ ~= RESP_EOF then
            self.state = STATE_CONNECTED
            return nil, "expected EOF packet after columns, but got " .. (typ or "nil")
        end
    end

    self.state = STATE_CONNECTED
    return stmt
end

--- 将长度编码为二进到字符串 (内部函数)
---@param s string
---@return string
local function _to_binary_coded_string(s)
    local len = #s
    if len < 251 then
        return strchar(len) .. s
    end
    if len < 65536 then -- 2^16
        return strchar(252) .. _set_byte2(len) .. s
    end
    if len < 16777216 then -- 2^24
        return strchar(253) .. _set_byte3(len) .. s
    end
    -- 对于更大的值，需要8字节镶度，这里暂不完整支持
    return strchar(254) .. _set_byte4(len) .. _set_byte4(0) .. s
end

--- 将Lua类型的值编码为MySQL二进制协议格式
---@param value any 要编码的值
---@return string 二进制字符串
---@return integer MySQL类型代码
local function _encode_value(value)
    local t = type(value)
    if value == null or t == "nil" then
        return "", MYSQL_TYPE_NULL
    elseif t == "number" then
        if math.floor(value) == value then
            return _set_byte4(value), MYSQL_TYPE_LONG
        else
            c_double_u.value = value
            return ffi.string(c_double_u.bytes, 8), MYSQL_TYPE_DOUBLE
        end
    elseif t == "string" then
        return _to_binary_coded_string(value), MYSQL_TYPE_STRING
    else -- boolean, table, etc.
        return _to_binary_coded_string(tostring(value)), MYSQL_TYPE_STRING
    end
end

--- 解析二进制协议的结果行
---@param data string 行数据包
---@param cols table 列定义信息
---@param compact boolean 是否返回紧凑数组
---@return table? 解析后的行数据
---@return string? 错误信息
local function _parse_binary_row_data_packet(data, cols, compact) -- 标准query返回文本结果,但是statement似乎是二进制结果,所以不可复用.
    -- 跳过包头 (1 byte 0x00)
    local pos = 2

    -- 解析 NULL-bitmap
    local num_cols = #cols
    -- 根据MySQL二进制协议，NULL-bitmap的长度计算应包含2-bit的偏移量
    local null_bitmap_len = to_int((num_cols + 7 + 2) / 8)
    if pos + null_bitmap_len > #data + 1 then
        return nil, "invalid null-bitmap length"
    end
    local null_bitmap = sub(data, pos, pos + null_bitmap_len - 1)
    pos = pos + null_bitmap_len

    local row
    if compact then
        row = new_tab(num_cols, 0)
    else
        row = new_tab(0, num_cols)
    end

    for i = 1, num_cols do
        local value
        -- 检查NULL-bitmap中对应的位，需要考虑-1bit + 2-bit的偏移
        local bit_offset = i + 1 -- i - 1 + 2
        local byte_idx = to_int(bit_offset / 8) + 1
        local bit_idx = bit_offset % 8
        if band(rshift(strbyte(null_bitmap, byte_idx), bit_idx), 1) == 1 then
            value = null
        else
            -- 根据列类型解析二进制数据
            local col_type = cols[i].type

            if col_type == MYSQL_TYPE_STRING or col_type == MYSQL_TYPE_VARCHAR or
                col_type == MYSQL_TYPE_VAR_STRING or col_type == MYSQL_TYPE_ENUM or
                col_type == MYSQL_TYPE_SET or col_type == MYSQL_TYPE_LONG_BLOB or
                col_type == MYSQL_TYPE_MEDIUM_BLOB or col_type == MYSQL_TYPE_BLOB or
                col_type == MYSQL_TYPE_TINY_BLOB or col_type == MYSQL_TYPE_JSON or
                col_type == MYSQL_TYPE_NEWDECIMAL or col_type == MYSQL_TYPE_BIT then
                value, pos = _from_length_coded_str(data, pos)
            elseif col_type == MYSQL_TYPE_LONGLONG then
                value, pos = _get_byte8(data, pos)
            elseif col_type == MYSQL_TYPE_LONG or col_type == MYSQL_TYPE_INT24 then
                value, pos = _get_byte4(data, pos)
            elseif col_type == MYSQL_TYPE_SHORT or col_type == MYSQL_TYPE_YEAR then
                value, pos = _get_byte2(data, pos)
            elseif col_type == MYSQL_TYPE_TINY then
                value = strbyte(data, pos)
                pos = pos + 1
            elseif col_type == MYSQL_TYPE_DOUBLE then
                c_double_u.value = ffi.cast("double", sub(data, pos, pos + 7))
                value = c_double_u.value
                pos = pos + 8
            elseif col_type == MYSQL_TYPE_FLOAT then
                c_float_u.value = ffi.cast("float", sub(data, pos, pos + 3))
                value = c_float_u.value
                pos = pos + 4
            else
                -- 对于未明确处理的日期、时间等类型，作为字符串安全读取
                value, pos = _from_length_coded_str(data, pos)
            end
        end

        if compact then
            row[i] = value
        else
            row[cols[i].name] = value
        end
    end
    return row
end

--- 读取二进制结果集
---@param self Connection 链接实例
---@param stmt table statement句柄
---@return table? 结果表
---@return string? 错误信息
---@return integer? 错误代码
---@return string? 标准错误码
local function _read_binary_result(self, stmt)
    local packet, typ, err = _recv_packet(self)
    if not packet then
        return nil, err
    end

    if typ == RESP_ERR then
        self.state = STATE_CONNECTED
        local errno, msg, sqlstate = _parse_err_packet(packet)
        return nil, msg, errno, sqlstate
    end

    if typ == RESP_OK then
        self.state = STATE_CONNECTED
        return _parse_ok_packet(packet)
    end

    -- 1. 读取结果头 (列数量)
    local field_count, _ = _parse_result_set_header_packet(packet)

    -- 2. 列定义在prepare阶段已获取(stmt.cols)，直接跳过
    for _ = 1, field_count do
        _recv_packet(self)
    end
    _recv_packet(self) -- EOF

    -- 3. 读取行数据
    local rows = new_tab(4, 0)
    local i = 0
    while true do
        packet, typ, err = _recv_packet(self)
        if not packet then
            return nil, err
        end

        if typ == RESP_EOF then
            local _, status_flags = _parse_eof_packet(packet)
            if band(status_flags, SERVER_MORE_RESULTS_EXISTS) ~= 0 then
                return rows, "again"
            end
            break
        end

        if typ == RESP_ERR then
            self.state = STATE_CONNECTED
            local errno, msg, sqlstate = _parse_err_packet(packet)
            return nil, msg, errno, sqlstate
        end

        i = i + 1
        rows[i] = _parse_binary_row_data_packet(packet, stmt.cols, self.compact)
    end

    self.state = STATE_CONNECTED
    return rows
end

--- 预处理SQL语句
---@param self Connection 链接实例
---@param sql string 要预处理的SQL语句
---@return table? statement句柄
---@return string? 错误信息
---@return integer? 错误代码
---@return string? 标准错误码
function _M.prepare(self, sql)
    local function do_prepare()
        -- 1. 发送预编译指令
        local _, err, errno, sqlstate = _send_com_packet(self, sql, COM_STMT_PREPARE)
        if not _ then
            return nil, "failed to send prepare command: " .. err, errno, sqlstate
        end
        -- 2. 读取预编译结果
        return _read_prepare_response(self)
    end

    local pool_key = self.pool
    if not pool_key then
        -- 不属于任何池的连接，直接执行prepare
        return do_prepare()
    end

    local thread_id, err, errno, sqlstate = self:get_connection_id()
    if not thread_id then
        -- 无法获取连接ID，无法使用缓存，直接执行prepare
        return do_prepare()
    end

    -- 查找或创建缓存表
    local pool_cache = statement_cache[pool_key]
    if not pool_cache then
        pool_cache = {}
        statement_cache[pool_key] = pool_cache
    end
    local conn_cache = pool_cache[thread_id]
    if not conn_cache then
        conn_cache = { last_used = ngx.now(), stmts = {} }
        pool_cache[thread_id] = conn_cache
    end

    -- 检查缓存命中
    local cached = conn_cache.stmts[sql]
    if cached then
        conn_cache.last_used = ngx.now()
        return cached.stmt
    end

    -- 缓存未命中，执行原始prepare
    local stmt, err, errno, sqlstate = do_prepare()
    if not stmt then
        return nil, err, errno, sqlstate
    end

    -- 存入缓存
    conn_cache.stmts[sql] = { stmt = stmt }
    conn_cache.last_used = ngx.now()

    return stmt
end

--- 执行一个预处理语句
---@param self Connection 链接实例
---@param stmt table `prepare`函数返回的statement句柄
---@param ... unknown 绑定的参数
---@return table? 结果
---@return string? 错误信息
function _M.execute(self, stmt, ...)
    local args = { ... }
    local n_params = #args

    if n_params ~= stmt.parameters then
        return nil, "incorrect number of arguments: expected " .. stmt.parameters .. ", got " .. n_params
    end

    -- 1. 构建包体
    local packet_parts = new_tab(5, 0)
    packet_parts[1] = _set_byte4(stmt.statement_id) -- statement-id
    packet_parts[2] = strchar(0)                    -- flags (0 = CURSOR_TYPE_NO_CURSOR)
    packet_parts[3] = _set_byte4(1)                 -- iteration-count (always 1)

    if n_params > 0 then
        -- NULL-bitmap
        local null_bitmap_len = to_int((n_params + 7) / 8)
        local null_bitmap = new_tab(null_bitmap_len, 0)
        for i = 1, null_bitmap_len do null_bitmap[i] = 0 end

        local types = new_tab(n_params * 2, 0)
        local values = new_tab(n_params, 0)

        for i = 1, n_params do
            local val_str, val_type = _encode_value(args[i])
            if val_type == MYSQL_TYPE_NULL then
                local byte_idx = to_int((i - 1) / 8) + 1
                local bit_idx = (i - 1) % 8
                null_bitmap[byte_idx] = bor(null_bitmap[byte_idx], lshift(1, bit_idx))
            end
            types[#types + 1] = strchar(val_type, 0) -- type + unused byte
            values[#values + 1] = val_str
        end

        local null_bitmap_str = new_tab(#null_bitmap, 0)
        for i = 1, #null_bitmap do null_bitmap_str[i] = strchar(null_bitmap[i]) end
        packet_parts[4] = concat(null_bitmap_str)

        packet_parts[5] = strchar(1) -- new-params-bound-flag (1 = true)
        packet_parts[6] = concat(types)
        packet_parts[7] = concat(values)
    end

    -- 2. 发送 COM_STMT_EXECUTE 包
    local _, err = _send_com_packet(self, packet_parts, COM_STMT_EXECUTE)
    if err then
        return nil, err
    end

    -- 3. 读取结果
    if stmt.columns > 0 then
        return _read_binary_result(self, stmt)
    else
        -- 对于没有返回结果的(INSERT, UPDATE, DELETE), 读取OK包
        return read_result(self)
    end
end

--- 关闭一个预处理语句
---@param self Connection 链接实例
---@param stmt table|number 要关闭的statement句柄或ID
---@return integer? 关闭的句柄
---@return string? 错误信息
---@return integer? 错误代码
---@return string? 标准错误码
function _M.close_statement(self, stmt)
    local stmt_id
    if type(stmt) == "table" then
        stmt_id = stmt.statement_id
    else
        stmt_id = stmt
    end

    local packet = _set_byte4(stmt_id)
    -- close命令没有响应
    return _send_com_packet(self, packet, COM_STMT_CLOSE)
end

---获取当前连接在MySQL服务器中的线程ID
---此方法会发起一次 `SELECT CONNECTION_ID()` 查询来获取实时的线程ID。
---这对于验证从连接池中取出的连接是否为预期的连接非常有用。
---@param self Connection 连接实例
---@return number? 线程ID
---@return string? 错误信息
---@return integer? 错误代码
---@return string? 标准错误码
function _M.get_connection_id(self)
    if self.thread_id then
        return self.thread_id
    end
    if self.state ~= STATE_CONNECTED then
        return nil, "cannot send query in the current context: "
            .. (self.state or "nil")
    end
    local sock = self.sock
    if not sock then
        return nil, "not initialized"
    end
    -- 警告：直接发送原始包，您需要自行确保包序号同步的正确性
    local bytes, err = sock:send({ _set_byte3(23), strchar(0), strchar(COM_QUERY), "SELECT CONNECTION_ID()" })
    if not bytes then
        return nil, err
    end
    self.state = STATE_COMMAND_SENT

    -- 读取结果
    local data
    local row_data                  -- 用于存储行数据包
    for i = 1, 4 do
        data, err = sock:receive(4) -- 读取包头
        if not data then
            self.state = STATE_CONNECTED; return nil, "recv header failed: " .. (err or "closed")
        end
        local len, pos = _get_byte3(data, 1)
        if len > 0 then
            data, err = sock:receive(len)
            if not data then
                self.state = STATE_CONNECTED; return nil, "recv body failed: " .. (err or "closed")
            end
        else
            data = ""
        end
        if i == 4 then
            row_data = data -- 保存第4个包（行数据）
        end
    end

    -- 消耗掉最后一个EOF包
    data, err = sock:receive(4)
    if data then
        local len, pos = _get_byte3(data, 1)
        if len and len > 0 then
            sock:receive(len)
        end
    end

    self.state = STATE_CONNECTED -- 恢复连接状态

    if not row_data then
        return nil, "did not receive row data packet"
    end

    -- 从保存的行数据中解析
    local thread_id_str, _ = _from_length_coded_str(row_data, 1)

    if thread_id_str and thread_id_str ~= null then
        local thread_id = tonumber(thread_id_str)
        if thread_id then
            self.thread_id = thread_id
            return thread_id
        end
    end

    return nil, "failed to parse connection_id from result"
end

-- statement end.

return _M
