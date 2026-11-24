-- Prove2me | Definitions.Def_Poly1305Bernstein
-- name    : Poly1305Bernstein
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-24T07:38:59.586127+00:00
-- url     : https://prove2.me/theorems/784129d0-46ff-4fd0-a142-ea70160dcb6f
-- title:
--   Poly1305 (Bernstein 2005) — messages, keys, padding, the authenticator and H_r
-- statement:
--   Definitions from Bernstein, *The Poly1305-AES message-authentication code* (FSE 2005), in the namespace `Poly1305`.
--
--   - **Bytes and messages** (p. 4): “A **message** is any sequence of bytes $m[0], m[1], \dots, m[\ell - 1]$; a **byte** is any element of $\{0, 1, \dots, 255\}$. The length $\ell$ can be any nonnegative integer”. `Byte` is `Fin 256`, `Message` a list of bytes, and `Str16` a 16-byte string `Fin 16 → Byte`.
--   - **The integer $r$** (p. 4): “a 16-byte string $r[0], r[1], \dots, r[15]$. The second part of the key represents a 128-bit integer $r$ in unsigned little-endian form: i.e., $r = r[0] + 2^8 r[1] + \dots + 2^{120} r[15]$.” `leVal` is this value of a 16-byte string; `toStr16 n` is the 16-byte unsigned little-endian representation of $n \bmod 2^{128}$.
--   - **The conditions on $r$** (p. 4): “$r[3], r[7], r[11], r[15]$ are required to have their top four bits clear (i.e., to be in $\{0, 1, \dots, 15\}$), and $r[4], r[8], r[12]$ are required to have their bottom two bits clear (i.e., to be in $\{0, 4, 8, \dots, 252\}$).” This is `IsClamped`, a predicate on 16-byte strings kept separate from the functions below, which, like the sample code, accept any $r$.
--   - **The key, the nonce and $\mathrm{AES}_k(n)$** (p. 4): “The key has two parts: first, a 16-byte AES key $k$; second, a 16-byte string $r[0], r[1], \dots, r[15]$”; “Poly1305-AES requires each message to be accompanied by a 16-byte **nonce**, i.e., a unique message number. Poly1305-AES feeds each nonce $n$ through $\mathrm{AES}_k$ to obtain the 16-byte string $\mathrm{AES}_k(n)$. There is nothing special about AES here. One can replace AES with an arbitrary keyed function from an arbitrary set of nonces to 16-byte strings.” No AES, key $k$ or nonce is defined: wherever the paper writes $\mathrm{AES}_k(n)$, the definitions take an arbitrary 16-byte string $s$.
--   - **$q$ and $c_i$** (p. 4): “Let $m[0], m[1], \dots, m[\ell - 1]$ be a message. Write $q = \lceil \ell/16 \rceil$. Define integers $c_1, c_2, \dots, c_q \in \{1, 2, 3, \dots, 2^{129}\}$ as follows: if $1 \le i \le \lfloor \ell/16 \rfloor$ then $c_i = m[16i - 16] + 2^8 m[16i - 15] + 2^{16} m[16i - 14] + \dots + 2^{120} m[16i - 1] + 2^{128}$; if $\ell$ is not a multiple of 16 then $c_q = m[16q - 16] + 2^8 m[16q - 15] + \dots + 2^{8(\ell \bmod 16) - 8} m[\ell - 1] + 2^{8(\ell \bmod 16)}$.” `numChunks m` is $q$, written $(\ell + 15)/16$ in natural-number division; `chunk m i` is $c_i$ by the two formulas, for $1 \le i \le q$ (its value elsewhere is never used). The range claim is milestone `chunk_mem_Icc`.
--   - **The prime** (p. 5, in the definition and the sample code): $2^{130} - 5$ is `p1305`.
--   - **The authenticator** (p. 5): “$\mathrm{Poly1305}_r(m, \mathrm{AES}_k(n))$, the Poly1305-AES authenticator of a message $m$ with nonce $n$ under secret key $(k, r)$, is defined as the 16-byte unsigned little-endian representation of $(((c_1 r^q + c_2 r^{q-1} + \dots + c_q r^1) \bmod 2^{130} - 5) + \mathrm{AES}_k(n)) \bmod 2^{128}$. Here the 16-byte string $\mathrm{AES}_k(n)$ is treated as an unsigned little-endian integer”. `poly1305 r m s` is this formula with $s$ for $\mathrm{AES}_k(n)$ and $r$ any natural number: the key's conditions on $r$ are not assumed (they are `IsClamped`).
--   - **The sample code** (p. 5): “The following C++ code reads $k$ from `k[0]`, `k[1]`, …, `k[15]`, reads $r$ from `r[0]`, `r[1]`, …, `r[15]`, reads $\mathrm{AES}_k(n)$ from `s[0]`, `s[1]`, …, `s[15]`, reads $m$ from `m[0]`, `m[1]`, …, `m[l-1]`, and places $\mathrm{Poly1305}_r(m, \mathrm{AES}_k(n))$ into `out[0]`, `out[1]`, …, `out[15]`”. `gmpLoop` is its `while (l > 0)` loop and `gmpOut` its output, the bytes $\lfloor h/2^{8j} \rfloor \bmod 256$ of the final $h$ (the code's `h % 256; h >>= 8` loop in closed form).
--   - **The polynomial of a message** (p. 7): “For each message $m$, write $\underline{m}$ for the polynomial $c_1 x^q + c_2 x^{q-1} + \dots + c_q x^1$, where $q, c_1, c_2, \dots, c_q$ are defined as in Section 2.” `poly m` is this polynomial with integer coefficients.
--   - **$H_r$** (p. 7): “Define $H_r(m)$ as the 16-byte unsigned little-endian representation of $(\underline{m}(r) \bmod 2^{130} - 5) \bmod 2^{128}$”. `H r m` takes an integer $r$, with mod the least nonnegative residue.
--   - **Addition of 16-byte strings** (p. 8): “Define a group operation $+$ on 16-byte strings as addition modulo $2^{128}$, where each 16-byte string is viewed as the unsigned little-endian representation of an integer in $\{0, 1, 2, \dots, 2^{128} - 1\}$.” This is `add16`.
--   - **$p_1$ and $p_2$** (p. 8, proof of Theorem 3.1): “Define $p_1 = (2^{130} - 6)/1517314646$ and $p_2 = (p_1 - 1)/222890620702$.” `p1` and `p2` are these natural-number quotients; that both divisions are exact is part of milestones `prime_p1` and `prime_p2`.
-- source:
--   Bernstein, D. J., The Poly1305-AES message-authentication code, in: Fast Software Encryption (FSE 2005), Lecture Notes in Computer Science 3557, Springer, 2005, 32–49, https://doi.org/10.1007/11502760_3 (author's version of 2005-03-29: https://cr.yp.to/mac/poly1305-20050329.pdf), pp. 4–8, messages, keys and the conditions on r (§2, p. 4), conversion and padding (§2, p. 4), the authenticator and the sample code (§2, p. 5), the polynomial of a message and H_r (§3, p. 7), addition of 16-byte strings (§3, p. 8), p₁ and p₂ (proof of Theorem 3.1, p. 8)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Poly1305 (Bernstein 2005)

Definitions from D. J. Bernstein, *The Poly1305-AES message-authentication code* (FSE 2005):
messages and 16-byte strings (§2, p. 4), the prime `2^130 − 5`, the conditions on `r` (§2, p. 4),
the integers `c_1, …, c_q` of a message (§2, p. 4), the authenticator `Poly1305_r(m, s)` (§2,
p. 5), the sample code (§2, p. 5), the polynomial of a message and `H_r` (§3, p. 7), addition of
16-byte strings (§3, p. 8), and the numbers `p_1`, `p_2` of the proof of Theorem 3.1 (§3, p. 8).
-/

namespace Poly1305

open Polynomial

/-- A byte: an element of `{0, 1, …, 255}` (§2, p. 4). -/
abbrev Byte : Type := Fin 256

/-- A message: a finite sequence of bytes `m[0], …, m[ℓ − 1]` (§2, p. 4). -/
abbrev Message : Type := List Byte

/-- A 16-byte string `s[0], …, s[15]`. -/
abbrev Str16 : Type := Fin 16 → Byte

/-- The prime `2^130 − 5` (§2, p. 5). -/
def p1305 : ℕ := 2 ^ 130 - 5

/-- The integer a 16-byte string represents in unsigned little-endian form,
`s[0] + 2^8 s[1] + … + 2^120 s[15]` (§2, p. 4). -/
def leVal (s : Str16) : ℕ := ∑ j : Fin 16, 2 ^ (8 * (j : ℕ)) * (s j : ℕ)

/-- The 16-byte unsigned little-endian representation of `n mod 2^128`: byte `j` is
`⌊n / 2^(8j)⌋ mod 256`. -/
def toStr16 (n : ℕ) : Str16 := fun j => ⟨n / 2 ^ (8 * (j : ℕ)) % 256, Nat.mod_lt _ (by norm_num)⟩

/-- The conditions on the second key part `r[0], …, r[15]` (§2, p. 4): `r[3], r[7], r[11], r[15]`
have their top four bits clear (lie in `{0, 1, …, 15}`), and `r[4], r[8], r[12]` have their bottom
two bits clear (lie in `{0, 4, 8, …, 252}`). -/
def IsClamped (r : Str16) : Prop :=
  (r 3 : ℕ) < 16 ∧ (r 7 : ℕ) < 16 ∧ (r 11 : ℕ) < 16 ∧ (r 15 : ℕ) < 16 ∧
  (r 4 : ℕ) % 4 = 0 ∧ (r 8 : ℕ) % 4 = 0 ∧ (r 12 : ℕ) % 4 = 0

/-- The byte `m[k]` of a message as a number (`0` past the end, where it is never used). -/
def byteAt (m : Message) (k : ℕ) : ℕ := ((m.getD k 0 : Byte) : ℕ)

/-- `q = ⌈ℓ/16⌉` for a message of `ℓ` bytes (§2, p. 4). -/
def numChunks (m : Message) : ℕ := (m.length + 15) / 16

/-- The integer `c_i` of a message (§2, p. 4), for `1 ≤ i ≤ q`: if `i ≤ ⌊ℓ/16⌋`,
`c_i = m[16i − 16] + 2^8 m[16i − 15] + … + 2^120 m[16i − 1] + 2^128`; otherwise (`i = q` and `ℓ`
not a multiple of 16), `c_q = m[16q − 16] + … + 2^(8(ℓ mod 16) − 8) m[ℓ − 1] + 2^(8(ℓ mod 16))`. -/
def chunk (m : Message) (i : ℕ) : ℕ :=
  if i ≤ m.length / 16 then
    (∑ j ∈ Finset.range 16, 2 ^ (8 * j) * byteAt m (16 * i - 16 + j)) + 2 ^ 128
  else
    (∑ j ∈ Finset.range (m.length % 16), 2 ^ (8 * j) * byteAt m (16 * i - 16 + j)) +
      2 ^ (8 * (m.length % 16))

/-- `Poly1305_r(m, s)` (§2, p. 5), with the 16-byte string `s` in the place of `AES_k(n)`: the
16-byte unsigned little-endian representation of
`(((c_1 r^q + c_2 r^(q−1) + ⋯ + c_q r^1) mod 2^130 − 5) + s) mod 2^128`. -/
def poly1305 (r : ℕ) (m : Message) (s : Str16) : Str16 :=
  toStr16 (((∑ i ∈ Finset.Icc 1 (numChunks m), chunk m i * r ^ (numChunks m + 1 - i)) % p1305 +
    leVal s) % 2 ^ 128)

/-! ## The sample code (§2, p. 5) -/

/-- The `while (l > 0)` loop of the sample code `poly1305_gmpxx`, with `rbar` the integer `r̄` and
`h` the accumulator: it reads `j = min(16, l)` bytes into `c = m[0] + 2^8 m[1] + … + 2^(8j − 8)
m[j − 1] + 2^(8j)`, advances past them, and sets `h = ((h + c) · r̄) mod p`. Returns the final
`h`. -/
def gmpLoop (rbar : ℕ) : ℕ → Message → ℕ
  | h, [] => h
  | h, b :: bs =>
    let blk := (b :: bs).take 16
    let c := (∑ j ∈ Finset.range blk.length, 2 ^ (8 * j) * byteAt blk j) + 2 ^ (8 * blk.length)
    gmpLoop rbar ((h + c) * rbar % p1305) ((b :: bs).drop 16)
termination_by _ m => m.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- The output of the sample code `poly1305_gmpxx(out, r, s, m, l)`: with `r̄ = r[0] + 2^8 r[1] +
⋯ + 2^120 r[15]`, run the loop from `h = 0`, add `s[0] + 2^8 s[1] + ⋯ + 2^120 s[15]` to `h`, then
for `j = 0, …, 15` write `out[j] = h mod 256` and shift `h` right by 8 bits; so `out[j]` is
`⌊h / 2^(8j)⌋ mod 256` for the final `h`. -/
def gmpOut (r : Str16) (s : Str16) (m : Message) : Str16 :=
  let h := gmpLoop (leVal r) 0 m + leVal s
  fun j => ⟨h / 2 ^ (8 * (j : ℕ)) % 256, Nat.mod_lt _ (by norm_num)⟩

/-! ## §3 -/

/-- The polynomial `m = c_1 x^q + c_2 x^(q−1) + ⋯ + c_q x^1` of a message (§3, p. 7). -/
noncomputable def poly (m : Message) : ℤ[X] :=
  ∑ i ∈ Finset.Icc 1 (numChunks m), C (chunk m i : ℤ) * X ^ (numChunks m + 1 - i)

/-- `H_r(m)` (§3, p. 7): the 16-byte unsigned little-endian representation of
`(m(r) mod 2^130 − 5) mod 2^128`. -/
noncomputable def H (r : ℤ) (m : Message) : Str16 :=
  toStr16 ((((poly m).eval r % (p1305 : ℤ)).toNat) % 2 ^ 128)

/-- The group operation on 16-byte strings (§3, p. 8): addition modulo `2^128`, each string read
as the unsigned little-endian representation of an integer in `{0, 1, …, 2^128 − 1}`. -/
def add16 (a b : Str16) : Str16 := toStr16 ((leVal a + leVal b) % 2 ^ 128)

/-- `p_1 = (2^130 − 6)/1517314646` (proof of Theorem 3.1, p. 8). -/
def p1 : ℕ := (2 ^ 130 - 6) / 1517314646

/-- `p_2 = (p_1 − 1)/222890620702` (proof of Theorem 3.1, p. 8). -/
def p2 : ℕ := (p1 - 1) / 222890620702

end Poly1305


