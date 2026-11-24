-- Prove2me | Definitions.Def_Poly1305Boringssl_Rfc8439
-- name    : Poly1305Boringssl_Rfc8439
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-24T09:35:45.628527+00:00
-- url     : https://prove2.me/theorems/bc7ff14e-a331-4a74-bcf4-84f748f90b55
-- title:
--   RFC 8439's Poly1305 (poly1305_mac) on byte lists
-- statement:
--   RFC 8439, §2.5.1, p. 16, transcribed with natural numbers and lists of bytes:
--
--         clamp(r): r &= 0x0ffffffc0ffffffc0ffffffc0fffffff
--         poly1305_mac(msg, key):
--            r = le_bytes_to_num(key[0..15])
--            clamp(r)
--            s = le_bytes_to_num(key[16..31])
--            a = 0  /* a is the accumulator */
--            p = (1<<130)-5
--            for i=1 upto ceil(msg length in bytes / 16)
--               n = le_bytes_to_num(msg[((i-1)*16)..(i*16)] | [0x01])
--               a += n
--               a = (r * a) % p
--               end
--            a += s
--            return num_to_16_le_bytes(a)
--            end
--
--   - `p1305` is $p = 2^{130} - 5$; `leBytesToNum bs` is $\sum_j b_j 256^j$ for the bytes $b_0, b_1, \dots$ of `bs` (`le_bytes_to_num`); `numTo16LeBytes a` is the 16 bytes $\lfloor a / 256^i \rfloor \bmod 256$, $i = 0, \dots, 15$ (`num_to_16_le_bytes`: the low 128 bits of $a$, little-endian); `clamp r` is the bitwise AND of $r$ with `0x0ffffffc0ffffffc0ffffffc0fffffff`.
--   - `accumulate r a msg` is the loop started from the accumulator value $a$: for $i = 0, \dots, \lceil |msg|/16 \rceil - 1$, with $n$ the value of the bytes $16i, \dots, \min(16i + 15, |msg| - 1)$ of `msg` followed by the byte `0x01`, the accumulator becomes $r(a + n) \bmod p$.
--   - `poly1305Mac msg key` is `numTo16LeBytes` of `accumulate` $r$ $0$ `msg` $+ s$, with $r$ = `clamp` of the first 16 bytes of `key` and $s$ the value of bytes 16–31. Note the argument order `msg, key`, as in the pseudocode.
--
--   **Slices.** The pseudocode writes byte ranges with `..` but not consistently: `key[0..15]` and `key[16..31]` are 16 bytes each only when read inclusively, and `msg[((i-1)*16)..(i*16)]` is 16 bytes only when read with the upper end excluded. The transcription takes each as 16 bytes, the reading §2.5 fixes in prose: the 32-byte key “is partitioned into two parts, called "r" and "s"”, and the message is divided “into 16-byte blocks. The last one might be shorter”. So $r$ is bytes 0–15 of the key, $s$ bytes 16–31, and block $i$ (from $1$) is bytes $16(i-1), \dots, 16i - 1$ of the message, cut at its end.
-- source:
--   Y. Nir and A. Langley, ChaCha20 and Poly1305 for IETF Protocols, RFC 8439, June 2018 (https://doi.org/10.17487/RFC8439), §2.5.1 (p. 16), the pseudocode of clamp and poly1305_mac

/-!
# RFC 8439's Poly1305 (`poly1305_mac`)

The pseudocode of Y. Nir and A. Langley, *ChaCha20 and Poly1305 for IETF Protocols*, RFC 8439,
§2.5.1, as functions on natural numbers and lists of bytes.
-/

namespace Poly1305Boringssl

/-- The prime `p = (1<<130)-5`. -/
def p1305 : Nat := 2 ^ 130 - 5

/-- `le_bytes_to_num`: the little-endian value of a byte list. -/
def leBytesToNum (bs : List (BitVec 8)) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- `num_to_16_le_bytes`: the 16 least significant bytes of `a`, in little-endian order. -/
def numTo16LeBytes (a : Nat) : List (BitVec 8) :=
  (List.range 16).map fun i => BitVec.ofNat 8 (a / 256 ^ i)

/-- `clamp(r): r &= 0x0ffffffc0ffffffc0ffffffc0fffffff`. -/
def clamp (r : Nat) : Nat := r &&& 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- The loop of `poly1305_mac`, from the accumulator value `a`: for `i = 1` up to
`ceil(msg length in bytes / 16)`, `n = le_bytes_to_num(msg[((i-1)*16)..(i*16)] | [0x01])`,
`a += n`, `a = (r * a) % p`. The slice is the 16 bytes from offset `(i-1)*16`, or the bytes to
the end of `msg` for the last, shorter block; `| [0x01]` appends the byte `0x01`. -/
def accumulate (r a : Nat) (msg : List (BitVec 8)) : Nat :=
  (List.range ((msg.length + 15) / 16)).foldl
    (fun a i => r * (a + leBytesToNum ((msg.drop (16 * i)).take 16 ++ [1#8])) % p1305) a

/-- `poly1305_mac(msg, key)`: `r = le_bytes_to_num(key[0..15])` clamped,
`s = le_bytes_to_num(key[16..31])`, the loop from `a = 0`, then `a += s` and
`num_to_16_le_bytes(a)`. -/
def poly1305Mac (msg key : List (BitVec 8)) : List (BitVec 8) :=
  numTo16LeBytes
    (accumulate (clamp (leBytesToNum (key.take 16))) 0 msg + leBytesToNum ((key.drop 16).take 16))

end Poly1305Boringssl


