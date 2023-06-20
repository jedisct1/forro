const std = @import("std");
const builtin = @import("builtin");
const math = std.math;
const mem = std.mem;
const assert = std.debug.assert;
const testing = std.testing;
const maxInt = math.maxInt;
const Poly1305 = std.crypto.onetimeauth.Poly1305;
const AuthenticationError = std.crypto.errors.AuthenticationError;

/// Forro14 stream cipher.
pub const Forro14 = Forro(14);

/// Forro14 stream cipher, reduced to 6 rounds.
pub const Forro6 = Forro(6);

/// Forro14 stream cipher.
pub const Forro14With64BitNonce = ForroWith64BitNonce(14);

/// Forro14 stream cipher, reduced to 6 rounds.
pub const Forro6With64BitNonce = ForroWith64BitNonce(6);

/// Forro14 stream cipher.
pub const XForro14 = XForro(14);

/// XForro14 stream cipher, reduced to 6 rounds.
pub const XForro6 = XForro(6);

/// Forro14-Poly1305 authenticated cipher, as designed for TLS
pub const Forro14Poly1305 = ForroPoly1305(14);

/// Forro14-Poly1305 authenticated cipher, reduced to 6 rounds
/// Reduced-rounds versions are faster than the full-round version, but have a lower security margin.
/// However, Forro is still believed to have a comfortable security margin even with only with 6 rounds.
pub const Forro6Poly1305 = ForroPoly1305(6);

/// XForro14-Poly1305 authenticated cipher
pub const XForro14Poly1305 = XForroPoly1305(14);

/// XForro14-Poly1305 authenticated cipher
/// Reduced-rounds versions are faster than the full-round version, but have a lower security margin.
/// However, Forro is still believed to have a comfortable security margin even with only with 6 rounds.
pub const XForro6Poly1305 = XForroPoly1305(6);

// Non-vectorized implementation of the core function
fn ForroNonVecImpl(comptime rounds_nb: usize) type {
    return struct {
        const BlockVec = [16]u32;

        fn initContext(key: [8]u32, d: [4]u32) BlockVec {
            const c = "voltadaasabranca";
            const constant_le = comptime [4]u32{
                mem.readIntLittle(u32, c[0..4]),
                mem.readIntLittle(u32, c[4..8]),
                mem.readIntLittle(u32, c[8..12]),
                mem.readIntLittle(u32, c[12..16]),
            };
            return BlockVec{
                key[0], key[1], key[2],         key[3],
                d[0],   d[1],   constant_le[0], constant_le[1],
                key[4], key[5], key[6],         key[7],
                d[2],   d[3],   constant_le[2], constant_le[3],
            };
        }

        const QuarterRound = struct {
            a: usize,
            b: usize,
            c: usize,
            d: usize,
            e: usize,
        };

        fn Rp(a: usize, b: usize, c: usize, d: usize, e: usize) QuarterRound {
            return QuarterRound{
                .a = a,
                .b = b,
                .c = c,
                .d = d,
                .e = e,
            };
        }

        inline fn forro14Core(x: *BlockVec, input: BlockVec) void {
            x.* = input;

            const rounds = comptime [_]QuarterRound{
                Rp(0, 4, 8, 12, 3),
                Rp(1, 5, 9, 13, 0),
                Rp(2, 6, 10, 14, 1),
                Rp(3, 7, 11, 15, 2),
                Rp(0, 5, 10, 15, 3),
                Rp(1, 6, 11, 12, 0),
                Rp(2, 7, 8, 13, 1),
                Rp(3, 4, 9, 14, 2),
            };

            comptime var j: usize = 0;
            inline while (j < rounds_nb) : (j += 2) {
                inline for (rounds) |r| {
                    x[r.d] +%= x[r.e];
                    x[r.c] ^= x[r.d];
                    x[r.b] = math.rotl(u32, x[r.b] +% x[r.c], 10);
                    x[r.a] +%= x[r.b];
                    x[r.e] ^= x[r.a];
                    x[r.d] = math.rotl(u32, x[r.d] +% x[r.e], 27);
                    x[r.c] +%= x[r.d];
                    x[r.b] ^= x[r.c];
                    x[r.a] = math.rotl(u32, x[r.a] +% x[r.b], 8);
                }
            }
        }

        inline fn hashToBytes(out: *[64]u8, x: BlockVec) void {
            for (0..4) |i| {
                mem.writeIntLittle(u32, out[16 * i + 0 ..][0..4], x[i * 4 + 0]);
                mem.writeIntLittle(u32, out[16 * i + 4 ..][0..4], x[i * 4 + 1]);
                mem.writeIntLittle(u32, out[16 * i + 8 ..][0..4], x[i * 4 + 2]);
                mem.writeIntLittle(u32, out[16 * i + 12 ..][0..4], x[i * 4 + 3]);
            }
        }

        inline fn contextFeedback(x: *BlockVec, ctx: BlockVec) void {
            for (0..16) |i| {
                x[i] +%= ctx[i];
            }
        }

        fn forro14Xor(out: []u8, in: []const u8, key: [8]u32, counter_and_nonce: [4]u32, comptime count64: bool) void {
            var ctx = initContext(key, counter_and_nonce);
            var x: BlockVec = undefined;
            var buf: [64]u8 = undefined;
            var i: usize = 0;
            while (i + 64 <= in.len) : (i += 64) {
                forro14Core(x[0..], ctx);
                contextFeedback(&x, ctx);
                hashToBytes(buf[0..], x);

                var xout = out[i..];
                const xin = in[i..];
                for (0..64) |j| {
                    xout[j] = xin[j];
                }
                for (0..64) |j| {
                    xout[j] ^= buf[j];
                }
                if (count64) {
                    const next = @addWithOverflow(ctx[12], 1);
                    ctx[12] = next[0];
                    ctx[13] +%= next[1];
                } else {
                    ctx[12] +%= 1;
                }
            }
            if (i < in.len) {
                forro14Core(x[0..], ctx);
                contextFeedback(&x, ctx);
                hashToBytes(buf[0..], x);

                var xout = out[i..];
                const xin = in[i..];
                for (0..in.len % 64) |j| {
                    xout[j] = xin[j] ^ buf[j];
                }
            }
        }

        fn forro14Stream(out: []u8, key: [8]u32, counter_and_nonce: [4]u32, comptime count64: bool) void {
            var ctx = initContext(key, counter_and_nonce);
            var x: BlockVec = undefined;
            var i: usize = 0;
            while (i + 64 <= out.len) : (i += 64) {
                forro14Core(x[0..], ctx);
                contextFeedback(&x, ctx);
                hashToBytes(out[i..][0..64], x);
                if (count64) {
                    const next = @addWithOverflow(ctx[4], 1);
                    ctx[4] = next[0];
                    ctx[5] +%= next[1];
                } else {
                    ctx[4] +%= 1;
                }
            }
            if (i < out.len) {
                forro14Core(x[0..], ctx);
                contextFeedback(&x, ctx);

                var buf: [64]u8 = undefined;
                hashToBytes(buf[0..], x);
                @memcpy(out[i..], buf[0 .. out.len - i]);
            }
        }

        fn hforro14(input: [16]u8, key: [32]u8) [32]u8 {
            var c: [4]u32 = undefined;
            for (c, 0..) |_, i| {
                c[i] = mem.readIntLittle(u32, input[4 * i ..][0..4]);
            }
            const ctx = initContext(keyToWords(key), c);
            var x: BlockVec = undefined;
            forro14Core(x[0..], ctx);
            var out: [32]u8 = undefined;
            mem.writeIntLittle(u32, out[0..4], x[6]);
            mem.writeIntLittle(u32, out[4..8], x[7]);
            mem.writeIntLittle(u32, out[8..12], x[14]);
            mem.writeIntLittle(u32, out[12..16], x[15]);
            mem.writeIntLittle(u32, out[16..20], x[4]);
            mem.writeIntLittle(u32, out[20..24], x[5]);
            mem.writeIntLittle(u32, out[24..28], x[12]);
            mem.writeIntLittle(u32, out[28..32], x[13]);
            return out;
        }
    };
}

fn ForroImpl(comptime rounds_nb: usize) type {
    return ForroNonVecImpl(rounds_nb);
}

fn keyToWords(key: [32]u8) [8]u32 {
    var k: [8]u32 = undefined;
    for (0..8) |i| {
        k[i] = mem.readIntLittle(u32, key[i * 4 ..][0..4]);
    }
    return k;
}

fn extend(key: [32]u8, nonce: [24]u8, comptime rounds_nb: usize) struct { key: [32]u8, nonce: [12]u8 } {
    var subnonce: [12]u8 = undefined;
    @memset(subnonce[0..4], 0);
    subnonce[4..].* = nonce[16..24].*;
    return .{
        .key = ForroImpl(rounds_nb).hforro14(nonce[0..16].*, key),
        .nonce = subnonce,
    };
}

fn Forro(comptime rounds_nb: usize) type {
    return struct {
        /// Nonce length in bytes.
        pub const nonce_length = 12;
        /// Key length in bytes.
        pub const key_length = 32;
        /// Block length in bytes.
        pub const block_length = 64;

        /// Add the output of the Forro14 stream cipher to `in` and stores the result into `out`.
        /// WARNING: This function doesn't provide authenticated encryption.
        /// Using the AEAD or one of the `box` versions is usually preferred.
        pub fn xor(out: []u8, in: []const u8, counter: u32, key: [key_length]u8, nonce: [nonce_length]u8) void {
            assert(in.len == out.len);
            assert(in.len <= 64 * (@as(u39, 1 << 32) - counter));

            var d: [4]u32 = undefined;
            d[0] = counter;
            d[1] = mem.readIntLittle(u32, nonce[0..4]);
            d[2] = mem.readIntLittle(u32, nonce[4..8]);
            d[3] = mem.readIntLittle(u32, nonce[8..12]);
            ForroImpl(rounds_nb).forro14Xor(out, in, keyToWords(key), d, false);
        }

        /// Write the output of the Forro14 stream cipher into `out`.
        pub fn stream(out: []u8, counter: u32, key: [key_length]u8, nonce: [nonce_length]u8) void {
            assert(out.len <= 64 * (@as(u39, 1 << 32) - counter));

            var d: [4]u32 = undefined;
            d[0] = counter;
            d[1] = mem.readIntLittle(u32, nonce[0..4]);
            d[2] = mem.readIntLittle(u32, nonce[4..8]);
            d[3] = mem.readIntLittle(u32, nonce[8..12]);
            ForroImpl(rounds_nb).forro14Stream(out, keyToWords(key), d, false);
        }
    };
}

fn ForroWith64BitNonce(comptime rounds_nb: usize) type {
    return struct {
        /// Nonce length in bytes.
        pub const nonce_length = 8;
        /// Key length in bytes.
        pub const key_length = 32;
        /// Block length in bytes.
        pub const block_length = 64;

        /// Add the output of the Forro14 stream cipher to `in` and stores the result into `out`.
        /// WARNING: This function doesn't provide authenticated encryption.
        /// Using the AEAD or one of the `box` versions is usually preferred.
        pub fn xor(out: []u8, in: []const u8, counter: u64, key: [key_length]u8, nonce: [nonce_length]u8) void {
            assert(in.len == out.len);
            assert(in.len <= 64 * (@as(u71, 1 << 64) - counter));

            const k = keyToWords(key);
            var c: [4]u32 = undefined;
            c[0] = @truncate(u32, counter);
            c[1] = @truncate(u32, counter >> 32);
            c[2] = mem.readIntLittle(u32, nonce[0..4]);
            c[3] = mem.readIntLittle(u32, nonce[4..8]);
            ForroImpl(rounds_nb).forro14Xor(out, in, k, c, true);
        }

        /// Write the output of the Forro14 stream cipher into `out`.
        pub fn stream(out: []u8, counter: u32, key: [key_length]u8, nonce: [nonce_length]u8) void {
            assert(out.len <= 64 * (@as(u71, 1 << 64) - counter));

            const k = keyToWords(key);
            var c: [4]u32 = undefined;
            c[0] = @truncate(u32, counter);
            c[1] = @truncate(u32, counter >> 32);
            c[2] = mem.readIntLittle(u32, nonce[0..4]);
            c[3] = mem.readIntLittle(u32, nonce[4..8]);
            ForroImpl(rounds_nb).forro14Stream(out, k, c, true);
        }
    };
}

fn XForro(comptime rounds_nb: usize) type {
    return struct {
        /// Nonce length in bytes.
        pub const nonce_length = 24;
        /// Key length in bytes.
        pub const key_length = 32;
        /// Block length in bytes.
        pub const block_length = 64;

        /// Add the output of the XForro14 stream cipher to `in` and stores the result into `out`.
        /// WARNING: This function doesn't provide authenticated encryption.
        /// Using the AEAD or one of the `box` versions is usually preferred.
        pub fn xor(out: []u8, in: []const u8, counter: u32, key: [key_length]u8, nonce: [nonce_length]u8) void {
            const extended = extend(key, nonce, rounds_nb);
            Forro(rounds_nb).xor(out, in, counter, extended.key, extended.nonce);
        }

        /// Write the output of the XForro14 stream cipher into `out`.
        pub fn stream(out: []u8, counter: u32, key: [key_length]u8, nonce: [nonce_length]u8) void {
            const extended = extend(key, nonce, rounds_nb);
            Forro(rounds_nb).xor(out, counter, extended.key, extended.nonce);
        }
    };
}

fn ForroPoly1305(comptime rounds_nb: usize) type {
    return struct {
        pub const tag_length = 16;
        pub const nonce_length = 12;
        pub const key_length = 32;

        /// c: ciphertext: output buffer should be of size m.len
        /// tag: authentication tag: output MAC
        /// m: message
        /// ad: Associated Data
        /// npub: public nonce
        /// k: private key
        pub fn encrypt(c: []u8, tag: *[tag_length]u8, m: []const u8, ad: []const u8, npub: [nonce_length]u8, k: [key_length]u8) void {
            assert(c.len == m.len);
            assert(m.len <= 64 * (@as(u39, 1 << 32) - 1));

            var polyKey = [_]u8{0} ** 32;
            Forro(rounds_nb).xor(polyKey[0..], polyKey[0..], 0, k, npub);

            Forro(rounds_nb).xor(c[0..m.len], m, 1, k, npub);

            var mac = Poly1305.init(polyKey[0..]);
            mac.update(ad);
            if (ad.len % 16 != 0) {
                const zeros = [_]u8{0} ** 16;
                const padding = 16 - (ad.len % 16);
                mac.update(zeros[0..padding]);
            }
            mac.update(c[0..m.len]);
            if (m.len % 16 != 0) {
                const zeros = [_]u8{0} ** 16;
                const padding = 16 - (m.len % 16);
                mac.update(zeros[0..padding]);
            }
            var lens: [16]u8 = undefined;
            mem.writeIntLittle(u64, lens[0..8], ad.len);
            mem.writeIntLittle(u64, lens[8..16], m.len);
            mac.update(lens[0..]);
            mac.final(tag);
        }

        /// m: message: output buffer should be of size c.len
        /// c: ciphertext
        /// tag: authentication tag
        /// ad: Associated Data
        /// npub: public nonce
        /// k: private key
        /// NOTE: the check of the authentication tag is currently not done in constant time
        pub fn decrypt(m: []u8, c: []const u8, tag: [tag_length]u8, ad: []const u8, npub: [nonce_length]u8, k: [key_length]u8) AuthenticationError!void {
            assert(c.len == m.len);

            var polyKey = [_]u8{0} ** 32;
            Forro(rounds_nb).xor(polyKey[0..], polyKey[0..], 0, k, npub);

            var mac = Poly1305.init(polyKey[0..]);

            mac.update(ad);
            if (ad.len % 16 != 0) {
                const zeros = [_]u8{0} ** 16;
                const padding = 16 - (ad.len % 16);
                mac.update(zeros[0..padding]);
            }
            mac.update(c);
            if (c.len % 16 != 0) {
                const zeros = [_]u8{0} ** 16;
                const padding = 16 - (c.len % 16);
                mac.update(zeros[0..padding]);
            }
            var lens: [16]u8 = undefined;
            mem.writeIntLittle(u64, lens[0..8], ad.len);
            mem.writeIntLittle(u64, lens[8..16], c.len);
            mac.update(lens[0..]);
            var computedTag: [16]u8 = undefined;
            mac.final(computedTag[0..]);

            var acc: u8 = 0;
            for (computedTag, 0..) |_, i| {
                acc |= computedTag[i] ^ tag[i];
            }
            if (acc != 0) {
                return error.AuthenticationFailed;
            }
            Forro(rounds_nb).xor(m[0..c.len], c, 1, k, npub);
        }
    };
}

fn XForroPoly1305(comptime rounds_nb: usize) type {
    return struct {
        pub const tag_length = 16;
        pub const nonce_length = 24;
        pub const key_length = 32;

        /// c: ciphertext: output buffer should be of size m.len
        /// tag: authentication tag: output MAC
        /// m: message
        /// ad: Associated Data
        /// npub: public nonce
        /// k: private key
        pub fn encrypt(c: []u8, tag: *[tag_length]u8, m: []const u8, ad: []const u8, npub: [nonce_length]u8, k: [key_length]u8) void {
            const extended = extend(k, npub, rounds_nb);
            return ForroPoly1305(rounds_nb).encrypt(c, tag, m, ad, extended.nonce, extended.key);
        }

        /// m: message: output buffer should be of size c.len
        /// c: ciphertext
        /// tag: authentication tag
        /// ad: Associated Data
        /// npub: public nonce
        /// k: private key
        pub fn decrypt(m: []u8, c: []const u8, tag: [tag_length]u8, ad: []const u8, npub: [nonce_length]u8, k: [key_length]u8) AuthenticationError!void {
            const extended = extend(k, npub, rounds_nb);
            return ForroPoly1305(rounds_nb).decrypt(m, c, tag, ad, extended.nonce, extended.key);
        }
    };
}

test "forro14 AEAD API" {
    const aeads = [_]type{ Forro14Poly1305, XForro14Poly1305 };
    const m = "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
    const ad = "Additional data";

    inline for (aeads) |aead| {
        const key = [_]u8{69} ** aead.key_length;
        const nonce = [_]u8{42} ** aead.nonce_length;
        var c: [m.len]u8 = undefined;
        var tag: [aead.tag_length]u8 = undefined;
        var out: [m.len]u8 = undefined;

        aead.encrypt(c[0..], tag[0..], m, ad, nonce, key);
        try aead.decrypt(out[0..], c[0..], tag, ad[0..], nonce, key);
        try testing.expectEqualSlices(u8, out[0..], m);
        c[0] +%= 1;
        try testing.expectError(error.AuthenticationFailed, aead.decrypt(out[0..], c[0..], tag, ad[0..], nonce, key));
    }
}

test "crypto.forro14 test vector sunscreen" {
    const expected_result_hex = "94171856b0ee898e4414c828b224ac98c7eaf5cd5322d433f0fecda7803c28f9195b78b8c41c3c8418d6b95c53071e12122b16bf5931b9bc01180f665eca76b9ad4282fa511e7ac5f1bc17c8817c5acb603adce792d6a056cec2b4ae2993960ef445f1703e64006eee31c45a0fb62793dd88";
    var expected_result: [expected_result_hex.len / 2]u8 = undefined;
    _ = try std.fmt.hexToBytes(&expected_result, expected_result_hex);
    const m = "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
    var result: [114]u8 = undefined;
    const key = [_]u8{
        0,  1,  2,  3,  4,  5,  6,  7,
        8,  9,  10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23,
        24, 25, 26, 27, 28, 29, 30, 31,
    };
    const nonce = [_]u8{
        0, 0, 0, 0,
        0, 0, 0, 0x4a,
        0, 0, 0, 0,
    };

    Forro14.xor(result[0..], m[0..], 1, key, nonce);
    try testing.expectEqualSlices(u8, &expected_result, &result);

    var m2: [114]u8 = undefined;
    Forro14.xor(m2[0..], result[0..], 1, key, nonce);
    try testing.expect(mem.order(u8, m, &m2) == .eq);
}
