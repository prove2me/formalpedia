-- Prove2me | Definitions.Def_X25519Dalek_Rfc7748
-- name    : X25519Dalek_Rfc7748
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T21:17:03.174508+00:00
-- url     : https://prove2.me/theorems/dbac9781-ab06-4af0-9d6e-d87601f69c5d
-- title:
--   X25519 of RFC 7748, with the field and edwards25519 vocabulary
-- statement:
--   RFC 7748's X25519 function on byte lists, with what it needs: arithmetic in $\mathbb{F}_p$, $p = 2^{255} - 19$, the edwards25519 curve's base point and scalar multiplication, and the $u$-coordinate of the birational map. The definitions are DeepMind's (google-deepmind/code-verification @ `8c8d371f`), copied with unchanged bodies into the namespace `X25519Dalek`. They need no Mathlib: field elements are natural numbers, reduced mod $p$ by each operation. Page numbers below are those of the mission's source excerpts.
--
--   **The field.** RFC 7748, §4.1 (p. 1): “For the ~128-bit security level, the prime 2^255 - 19 is recommended for performance on a wide range of architectures.” `p25519` is $2^{255} - 19$. `fpAdd`, `fpSub`, `fpNeg`, `fpMul`, `fpSq` compute mod $p$ and return a value below $p$. `fpPow a e` is $a^e \bmod p$ by square-and-multiply over 256 bits of $e$ (`modPow`). `fpInv a` is $a^{p-2} \bmod p$, which sends $0$ to $0$.
--
--   **curve25519 and edwards25519.** §4.1 (p. 1): “This prime is congruent to 1 mod 4, and the derivation procedure in Appendix A results in the following Montgomery curve v^2 = u^3 + A*u^2 + u, called "curve25519":”, with $A = 486662$; and of it: “This curve is birationally equivalent to a twisted Edwards curve -x^2 + y^2 = 1 + d*x^2*y^2, called "edwards25519"”. `edD` is the listed $d$; `EdPoint` an affine pair, `EdExtPoint` extended coordinates $(X : Y : Z : T)$; `edBasepoint` the listed base point $(X(P), Y(P))$; `edExtAdd` the addition formulas of RFC 8032 §5.1.4 in extended coordinates; `edSmul n P` the multiple computed by double-and-add over 256 bits of $n$ from $(0 : 1 : 1 : 0)$ with `edExtAdd`, returned in affine coordinates. `edOnCurve` is the curve's equation (with coordinates below $p$), and `montOnCurve` with `montRHS` is curve25519's, $v^2 = u^3 + 486662u^2 + u$. No group on either curve is defined, and no statement says that `edExtAdd` is the group law. §4.1: “The birational maps are: (u, v) = ((1+y)/(1-y), sqrt(-486664)*u/x)”; `edToMontU (x, y)` is $(1 + y)(1 - y)^{p-2} \bmod p$, the $u$-part.
--
--   **Bytes.** §5 (p. 2): “The u-coordinates are elements of the underlying field GF(2^255 - 19) or GF(2^448 - 2^224 - 1) and are encoded as an array of bytes, u, in little-endian order such that u[0] + 256*u[1] + 256^2*u[2] + ... + 256^(n-1)*u[n-1] is congruent to the value modulo p and u[n-1] is minimal. When receiving such an array, implementations of X25519 (but not X448) MUST mask the most significant bit in the final byte.” And: “Implementations MUST accept non-canonical values and process them as if they had been reduced modulo the field prime.” `leBytesToNat` reads a byte list as a little-endian integer, `natToLeBytes len n` writes the low `len` bytes of $n$, and `decodeU255` reads the first 32 bytes with the top bit masked; `x25519Ladder` reduces the result mod $p$. §5 (p. 2): “For X25519, in order to decode 32 random bytes as an integer scalar, set the three least significant bits of the first byte and the most significant bit of the last to zero, set the second most significant bit of the last byte to 1 and, finally, decode as little-endian.” `clampScalarBytes` does that on a list of 32 bytes, and `clampScalar` is the clamped first 32 bytes as an integer.
--
--   **X25519.** §5 (p. 3): “To implement the X25519(k, u) and X448(k, u) functions (where k is the scalar and u is the u-coordinate), first decode k and u and then perform the following procedure, which is taken from [curve25519] and based on formulas from [montgomery]. All calculations are performed in GF(p), i.e., they are performed modulo p. The constant a24 is (486662 - 2) / 4 = 121665 for curve25519/X25519”. `montDiffAddAndDouble` is one step of the procedure on two projective pairs, with its formulas and `a24` $= 121665$. `montLadderLoop fuel k u1 x0 x1` runs the steps over bits $\mathit{fuel} - 1, \dots, 0$ of $k$; on a set bit it swaps the two pairs before and after the step, where the RFC swaps conditionally on the XOR of consecutive bits. `x25519Ladder k u` runs 255 steps from $(1 : 0)$ and $(u \bmod p : 1)$ and returns $x_2 \cdot z_2^{p-2}$, the RFC's “Return x_2 * (z_2^(p - 2))” (p. 4); `x25519 k u` is that on the clamped scalar and the decoded $u$, then, as the RFC says, “encode the resulting value as 32 or 56 bytes in little-endian order” (p. 4). §6.1 (p. 6): “Alice generates 32 random bytes in a[0] to a[31] and transmits K_A = X25519(a, 9) to Bob, where 9 is the u-coordinate of the base point and is encoded as a byte with value 9, followed by 31 zero bytes.”; `x25519Basepoint` is the 32-byte encoding of $9$, and `x25519Pubkey k` is $\mathrm{X25519}(k, 9)$.
--
--   **Five residues.** §6.1 (p. 6): “The check for the all-zero value results from the fact that the X25519 function produces that value if it operates on an input corresponding to a point with small order, where the order divides the cofactor of the curve”. `lowOrderUs` is the list $0$, $1$, two further constants and $p - 1$ that the all-zero milestone uses in place of that description; that they are the $u$-coordinates of points of small order is not stated in Lean.
--
--   Inputs of any length are accepted: `x25519` and `clampScalar` read the first 32 bytes, with missing bytes read as zero (and, for a list shorter than 32 bytes, the clamped top byte placed at its end rather than at index 31).
-- source:
--   A. Langley, M. Hamburg and S. Turner, Elliptic Curves for Security, RFC 7748, January 2016, https://doi.org/10.17487/RFC7748, §4.1 (curve25519, edwards25519 and the birational map, p. 1 of the excerpts), §5 (the X25519 function: decoding, clamping, the ladder, pp. 2–4) and §6.1 (the public key X25519(a, 9), p. 6)

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (dbenbenn/x25519-dalek-aarch64): definitions collected from
google-deepmind/code-verification @ 8c8d371f, the files
`arm64-semantics/VerifiedLibraries/Common/Spec/Curve25519.lean` (namespace
`VerifiedLibraries.Common`), `LibsignalBinary/Specifications/CryptoGames/DH/X25519.lean` (namespace
`CryptoGames.RFC7748`) and `LibsignalBinary/Proofs/HookDischarge/CryptoX25519/{Shared51/Math/Birational,
X25519Ref}.lean` (`edToMontU`, `montRHS`, `lowOrderUs`). Only the definitions the mission's statements
use are kept, in the namespace `X25519Dalek`, as a plain (non-`module`) file; their bodies are
unchanged. `montOnCurve` is new (curve25519's equation, with `montRHS`).
The `List.Vector` wrappers `x25519Ref` and `x25519PubFromSecretRef`, which need DeepMind's
`CryptoGames.Ratchet`, are dropped. Docstrings are shortened to what each definition is.
-/

/-!
# X25519 (RFC 7748) on byte lists, with the field and Edwards-curve vocabulary it needs

The prime field `F_p`, `p = 2^255 − 19`, as natural-number arithmetic mod `p`; the twisted Edwards
curve edwards25519 `−x² + y² = 1 + d x² y²` (RFC 7748 §4.1, RFC 8032 §5.1) with its base point and
scalar multiplication; little-endian byte encodings and scalar clamping; RFC 7748 §5's `X25519`
function (decoding, clamping, the Montgomery ladder, the final inversion) and §6.1's public key
`X25519(a, 9)`; the map `u = (1 + y)/(1 − y)` of RFC 7748 §4.1; and five residues mod `p`.
-/

namespace X25519Dalek

/-! ## The field `F_p` -/

/-- `p = 2^255 − 19` (RFC 7748 §4.1). -/
abbrev p25519 : Nat := 2 ^ 255 - 19

/-- `(acc * base ^ exp) % m` by square-and-multiply on the bits of `exp`, for at most `fuel`
bits. -/
def modPowLoop : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m, acc => acc % m
  | fuel + 1, base, exp, m, acc =>
    if exp == 0 then acc % m
    else
      let acc' := if exp % 2 == 1 then (acc * base) % m else acc
      modPowLoop fuel ((base * base) % m) (exp / 2) m acc'

/-- `base ^ exp % m` for exponents below `2^256`. -/
def modPow (base exp m : Nat) : Nat :=
  modPowLoop 256 (base % m) exp m 1

/-- Addition in `F_p`: `(a + b) mod p`. -/
def fpAdd (a b : Nat) : Nat := (a + b) % p25519

/-- Subtraction in `F_p`: `(a − b) mod p`. -/
def fpSub (a b : Nat) : Nat := (a + p25519 - (b % p25519)) % p25519

/-- Negation in `F_p`: `(−a) mod p`. -/
def fpNeg (a : Nat) : Nat := (p25519 - (a % p25519)) % p25519

/-- Multiplication in `F_p`: `(a · b) mod p`. -/
def fpMul (a b : Nat) : Nat := ((a % p25519) * (b % p25519)) % p25519

/-- Squaring in `F_p`. -/
def fpSq (a : Nat) : Nat := fpMul a a

/-- Exponentiation in `F_p`: `a ^ e mod p`. -/
def fpPow (a e : Nat) : Nat := modPow a e p25519

/-- `a ^ (p − 2) mod p`, the inverse of `a` in `F_p` for `a ≢ 0`, and `0` for `a ≡ 0`. -/
def fpInv (a : Nat) : Nat := fpPow a (p25519 - 2)

/-! ## edwards25519 -/

/-- The constant `d` of edwards25519 (RFC 7748 §4.1). -/
def edD : Nat :=
  37095705934669439343138083508754565189542113879843219016388785533085940283555

/-- `2d mod p`. -/
def edD2 : Nat :=
  fpAdd edD edD

/-- An affine point `(x, y)` (coordinates as natural numbers). -/
structure EdPoint where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

/-- A point `(X : Y : Z : T)` in extended coordinates: `x = X/Z`, `y = Y/Z`, `xy = T/Z`
(RFC 8032 §5.1.4). -/
structure EdExtPoint where
  X : Nat
  Y : Nat
  Z : Nat
  T : Nat
  deriving DecidableEq, Repr

/-- The point `(0 : 1 : 1 : 0)`. -/
def edExtZero : EdExtPoint := ⟨0, 1, 1, 0⟩

/-- `(x, y) ↦ (x mod p : y mod p : 1 : xy mod p)`. -/
def edExtOfAffine (P : EdPoint) : EdExtPoint :=
  let x := P.x % p25519
  let y := P.y % p25519
  ⟨x, y, 1, fpMul x y⟩

/-- `(X : Y : Z : T) ↦ (X Z^(p−2) mod p, Y Z^(p−2) mod p)`. -/
def edExtToAffine (P : EdExtPoint) : EdPoint :=
  let zInv := fpInv P.Z
  ⟨fpMul P.X zInv, fpMul P.Y zInv⟩

/-- The base point `(X(P), Y(P))` of edwards25519 (RFC 7748 §4.1). -/
def edBasepoint : EdPoint :=
  ⟨15112221349535400772501151409588531511454012693041857206046113283949847762202,
   46316835694926478169428394003475163141307993866256225615783033603165251855960⟩

/-- `(x, y)` has coordinates below `p` and satisfies `−x² + y² ≡ 1 + d x² y² (mod p)`, the equation
of edwards25519 (RFC 7748 §4.1). -/
def edOnCurve (P : EdPoint) : Bool :=
  P.x < p25519 && P.y < p25519 &&
  fpAdd (fpNeg (fpSq P.x)) (fpSq P.y) ==
    fpAdd 1 (fpMul edD (fpMul (fpSq P.x) (fpSq P.y)))

/-- `u³ + 486662 u² + u mod p`, the right-hand side of curve25519 `v² = u³ + A u² + u`
(RFC 7748 §4.1). -/
def montRHS (u : Nat) : Nat :=
  fpAdd (fpAdd (fpMul (fpSq u) u) (fpMul 486662 (fpSq u))) u

/-- `(u, v)` has coordinates below `p` and satisfies `v² ≡ u³ + 486662 u² + u (mod p)`, the
equation of curve25519 (RFC 7748 §4.1). -/
def montOnCurve (u v : Nat) : Bool :=
  u < p25519 && v < p25519 && fpSq v == montRHS u

/-- The addition formulas of RFC 8032 §5.1.4 in extended coordinates (with `k = 2d`). -/
def edExtAdd (P Q : EdExtPoint) : EdExtPoint :=
  let A := fpMul (fpSub P.Y P.X) (fpSub Q.Y Q.X)
  let B := fpMul (fpAdd P.Y P.X) (fpAdd Q.Y Q.X)
  let C := fpMul P.T (fpMul edD2 Q.T)
  let D := fpMul P.Z (fpAdd Q.Z Q.Z)
  let E := fpSub B A
  let F := fpSub D C
  let G := fpAdd D C
  let H := fpAdd B A
  ⟨fpMul E F, fpMul G H, fpMul F G, fpMul E H⟩

/-- `acc + n·P` by double-and-add with `edExtAdd` on the bits of `n`, least significant first, for
at most `fuel` bits. -/
def edExtSmulLoop : Nat → Nat → EdExtPoint → EdExtPoint → EdExtPoint
  | 0, _, _, acc => acc
  | fuel + 1, n, P, acc =>
    if n == 0 then acc
    else
      let acc' := if n % 2 == 1 then edExtAdd acc P else acc
      edExtSmulLoop fuel (n / 2) (edExtAdd P P) acc'

/-- `n·P` for `n < 2^256`, computed with `edExtSmulLoop` from `(0 : 1 : 1 : 0)` and returned in
affine coordinates. -/
def edSmul (n : Nat) (P : EdPoint) : EdPoint :=
  edExtToAffine (edExtSmulLoop 256 n (edExtOfAffine P) edExtZero)

/-- The map `(x, y) ↦ (1 + y)(1 − y)^(p−2) mod p`, the `u`-coordinate of RFC 7748 §4.1's birational
map `u = (1 + y)/(1 − y)` (it sends `y = 1` to `0`). -/
def edToMontU (P : EdPoint) : Nat :=
  fpMul (fpAdd 1 P.y) (fpInv (fpSub 1 P.y))

/-! ## Byte strings and clamping -/

/-- The little-endian value `∑ᵢ bᵢ 256^i` of a byte list. -/
def leBytesToNat (bs : List (BitVec 8)) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The `len` little-endian bytes of `n mod 256^len`. -/
def natToLeBytes (len n : Nat) : List (BitVec 8) :=
  (List.range len).map fun i => BitVec.ofNat 8 ((n / (256 ^ i)) % 256)

/-- Clamping of a 32-byte scalar (RFC 7748 §5 `decodeScalar25519`): clear the low three bits of
byte 0, clear bit 7 of byte 31 and set its bit 6. -/
def clampScalarBytes (bs : List (BitVec 8)) : List (BitVec 8) :=
  let b0 := (bs.getD 0 0#8) &&& 0xf8#8
  let b31 := ((bs.getD 31 0#8) &&& 0x7f#8) ||| 0x40#8
  [b0] ++ (bs.drop 1).take 30 ++ [b31]

/-- The clamped scalar of the first 32 bytes of `bs`, as an integer. -/
def clampScalar (bs : List (BitVec 8)) : Nat :=
  leBytesToNat (clampScalarBytes (bs.take 32))

/-! ## RFC 7748 §5: the X25519 function -/

/-- `a24 = (486662 − 2)/4 = 121665` (RFC 7748 §5). -/
abbrev a24 : Nat := 121665

/-- RFC 7748 §5 `decodeUCoordinate(u, 255)`: the little-endian value of the first 32 bytes with
the most significant bit masked. -/
def decodeU255 (bs : List (BitVec 8)) : Nat :=
  leBytesToNat (bs.take 32) % (2 ^ 255)

/-- A pair `(U : W)` of projective coordinates on the Montgomery `u`-line. -/
structure MontProjPoint where
  U : Nat
  W : Nat
  deriving DecidableEq, Repr

/-- One step of RFC 7748 §5's ladder on `(x_2 : z_2)` and `(x_3 : z_3)` with `x_1 = u1`: the
formulas `A, AA, B, BB, E, C, D, DA, CB` and the new pairs `(AA·BB : E·(AA + a24·E))` and
`((DA + CB)² : x_1·(DA − CB)²)`, in `F_p`. -/
def montDiffAddAndDouble (u1 : Nat) (P Q : MontProjPoint) :
    MontProjPoint × MontProjPoint :=
  let A := fpAdd P.U P.W
  let AA := fpSq A
  let B := fpSub P.U P.W
  let BB := fpSq B
  let E := fpSub AA BB
  let C := fpAdd Q.U Q.W
  let D := fpSub Q.U Q.W
  let DA := fpMul D A
  let CB := fpMul C B
  let U2 := fpMul AA BB
  let W2 := fpMul E (fpAdd AA (fpMul a24 E))
  let U3 := fpSq (fpAdd DA CB)
  let W3 := fpMul u1 (fpSq (fpSub DA CB))
  (⟨U2, W2⟩, ⟨U3, W3⟩)

/-- The ladder loop (after RFC 7748 §5) over bits `fuel − 1, …, 1, 0` of `k`, most significant first: on bit
`1` the two pairs are swapped before and after the step. -/
def montLadderLoop : Nat → Nat → Nat → MontProjPoint → MontProjPoint → MontProjPoint
  | 0, _, _, x0, _ => x0
  | fuel + 1, k, u1, x0, x1 =>
    let bit := (k / (2 ^ fuel)) % 2
    let (p0, p1) := if bit == 1 then (x1, x0) else (x0, x1)
    let (q0, q1) := montDiffAddAndDouble u1 p0 p1
    let (x0', x1') := if bit == 1 then (q1, q0) else (q0, q1)
    montLadderLoop fuel k u1 x0' x1'

/-- RFC 7748 §5 on integers: `u mod p`, 255 ladder steps from `(1 : 0)` and `(u : 1)` over the bits
of `k`, then `x_2 · z_2^(p−2) mod p`. -/
def x25519Ladder (k u : Nat) : Nat :=
  let u1 := u % p25519
  let res := montLadderLoop 255 k u1 ⟨1, 0⟩ ⟨u1, 1⟩
  fpMul res.U (fpInv res.W)

/-- RFC 7748 §5's `X25519(k, u)` on byte lists: the clamped scalar, the decoded `u`-coordinate, the
ladder, and the result as 32 little-endian bytes. -/
def x25519 (scalar uBytes : List (BitVec 8)) : List (BitVec 8) :=
  natToLeBytes 32 (x25519Ladder (clampScalar scalar) (decodeU255 uBytes))

/-- The base point `u = 9` as 32 little-endian bytes (RFC 7748 §6.1). -/
def x25519Basepoint : List (BitVec 8) :=
  natToLeBytes 32 9

/-- The public key `X25519(a, 9)` of RFC 7748 §6.1. -/
def x25519Pubkey (secret : List (BitVec 8)) : List (BitVec 8) :=
  x25519 secret x25519Basepoint

/-- Five residues mod `p`: `0`, `1`, two further constants, and `p − 1`. -/
def lowOrderUs : List Nat :=
  [ 0,
    1,
    325606250916557431795983626356110631294008115727848805560023387167927233504,
    39382357235489614581723060781553021112529911719440698176882885853963445705823,
    p25519 - 1 ]

end X25519Dalek


