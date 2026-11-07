-- Prove2me | Definitions.Def_IterRoundDet_Oracles
-- name    : IterRoundDet_Oracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:35.354268+00:00
-- url     : https://prove2.me/theorems/be877f48-f791-49d8-82e1-a2fead830705
-- title:
--   The oracles for $\mathcal M$, $\mathcal N$ and $p$, the encodings, and the bit bounds
-- statement:
--   Theorem 1.1 has two access models for $p$:
--
--   1. the **value model**: an independence oracle for $\mathcal M$ and a value oracle, $z\in\mathbb Q^n\mapsto p(z)$;
--   2. the **coefficient model**: independence oracles for $\mathcal M$ and for the support matroid $\mathcal N$, and a coefficient oracle, $S\mapsto c_S$.
--
--   A rational is the pair (zigzag code of the numerator, denominator), and a set its characteristic word. An ill-formed query gets the all-zero answer of the right length.
--
--   The number $b$ bounds the bit length of each numerator and denominator of the coefficients (p.19). The predicate `AnswerBits` says the value oracle's answers have polynomial bit length: $p(z)$ in lowest terms has at most $2b+n+2\sum_i(\text{bits of } z_i)$ bits.
--
--   **Formalization Note** `AnswerBits` is implied by a common denominator $D<2^b$ with numerators below $2^b$, as the sanity file proves. This covers integer coefficients and $\det(\sum_i z_i v_iv_i^\top)$ with rational $v_i$. It is not known to follow from individually $b$-bit coefficients, as $p(\mathbf 1)$ can have exponentially many terms.
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Theorem 1.1 and footnote 2, p.2; §4, p.19

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Machine

set_option autoImplicit false

namespace IterRoundDet

/-!
# The oracles, the encodings and the bit bounds

Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…). Theorem 1.1, p.2: "an
independence oracle" for `M`; "a value oracle for `p`"; "a coefficient oracle for `p` and an independence
oracle for its support matroid `N`". §4, p.19: "Let `b` denote the maximum bit length of the coefficients
of `p`."

**Formalization Note.** A rational is the pair (zigzag code of the numerator, denominator); a set is its
characteristic word of length `n`. An oracle is total: an ill-formed query gets the all-zero answer of
the right length, which no well-formed answer equals in the rational case, since denominators are
positive.
-/

variable {n : ℕ}

/-- The zigzag code of an integer: `z ↦ 2z` for `z ≥ 0`, `z ↦ −2z − 1` for `z < 0`. -/
def zig (z : ℤ) : ℕ := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1

/-- The inverse of `zig`. -/
def unzig (m : ℕ) : ℤ := if m % 2 = 0 then ((m / 2 : ℕ) : ℤ) else -(((m + 1) / 2 : ℕ) : ℤ)

/-- A rational as a pair of cells, in lowest terms. -/
def ratCode (q : ℚ) : List ℕ := [zig q.num, q.den]

/-- A rational vector as `2n` cells. -/
def ratList (a : Fin n → ℚ) : List ℕ := (List.ofFn fun i => ratCode (a i)).flatten

/-- A set as its characteristic word of length `n`. -/
def setCode (S : Finset (Fin n)) : List ℕ := List.ofFn fun i => if i ∈ S then 1 else 0

/-- The set with a given characteristic word, if the list is one. -/
def decodeSet (q : List ℕ) : Option (Finset (Fin n)) :=
  if q.length = n ∧ ∀ m ∈ q, m ≤ 1 then
    some (Finset.univ.filter fun i => q.getD i 0 = 1)
  else none

/-- The rational vector with `2n` cells `(zig num_i, den_i)`, if the list is one (all `den_i > 0`,
not required to be in lowest terms). -/
def decodeRatVec (q : List ℕ) : Option (Fin n → ℚ) :=
  if q.length = 2 * n ∧ ∀ i : Fin n, 0 < q.getD (2 * i + 1) 0 then
    some fun i => (unzig (q.getD (2 * i) 0) : ℚ) / (q.getD (2 * i + 1) 0 : ℚ)
  else none

open Classical in
/-- The independence oracle for `M`: the word of `S` gets `[1]` if `S` is independent, else `[0]`. -/
noncomputable def indepAnswer (M : Matroid (Fin n)) (q : List ℕ) : List ℕ :=
  match (decodeSet q : Option (Finset (Fin n))) with
  | some S => if M.Indep (S : Set (Fin n)) then [1] else [0]
  | none => [0]

open Classical in
/-- The value oracle for `p`, on all of `ℚⁿ`: `z ↦ p(z)`. -/
noncomputable def valueAnswer (c : Finset (Fin n) → ℚ) (q : List ℕ) : List ℕ :=
  match (decodeRatVec q : Option (Fin n → ℚ)) with
  | some z => ratCode (pEval c z)
  | none => [0, 0]

open Classical in
/-- The independence oracle for the support matroid `N`: the word of `S` gets `[1]` if `S ⊆ T` for some
`T` with `c_T > 0`, else `[0]`. -/
noncomputable def supportAnswer (c : Finset (Fin n) → ℚ) (q : List ℕ) : List ℕ :=
  match (decodeSet q : Option (Finset (Fin n))) with
  | some S => if ∃ T, S ⊆ T ∧ 0 < c T then [1] else [0]
  | none => [0]

/-- The coefficient oracle for `p`: the word of `S` gets `c_S` (`0` when `|S| ≠ d`). -/
noncomputable def coeffAnswer (c : Finset (Fin n) → ℚ) (q : List ℕ) : List ℕ :=
  match (decodeSet q : Option (Finset (Fin n))) with
  | some S => ratCode (c S)
  | none => [0, 0]

/-- Theorem 1.1's value model: tag `0` is the independence oracle for `M`, tag `1` the value oracle for
`p`. Other tags answer `[0]`. -/
noncomputable def valueModel (M : Matroid (Fin n)) (c : Finset (Fin n) → ℚ) : Oracle :=
  fun tag q =>
    match tag with
    | 0 => indepAnswer M q
    | 1 => valueAnswer c q
    | _ => [0]

/-- Theorem 1.1's coefficient model: tag `0` is the independence oracle for `M`, tag `1` the independence
oracle for `N`, tag `2` the coefficient oracle for `p`. Other tags answer `[0]`. -/
noncomputable def coeffModel (M : Matroid (Fin n)) (c : Finset (Fin n) → ℚ) : Oracle :=
  fun tag q =>
    match tag with
    | 0 => indepAnswer M q
    | 1 => supportAnswer c q
    | 2 => coeffAnswer c q
    | _ => [0]

/-- §4, p.19: `b` bounds the bit length of the coefficients of `p`. -/
def BitBounded (b : ℕ) (c : Finset (Fin n) → ℚ) : Prop :=
  ∀ S, (c S).num.natAbs < 2 ^ b ∧ (c S).den < 2 ^ b

/-- The value oracle's answers have polynomial bit length: at every `z ∈ ℚⁿ`,
`|p(z)|` in lowest terms has at most `2b + n + 2 ∑_i (bits of z_i)` bits.

**Formalization Note.** The clause "a polynomial-time algorithm given a value oracle" presupposes this:
the time of a bit-counting algorithm includes reading the answers. It is implied by a common denominator
`D < 2^b` of the coefficients with numerators `< 2^b`, which covers integer coefficients (`D = 1`) and the
determinant `det(∑ z_i v_i v_i⊤)` with rational `v_i` (p.2: "can be evaluated exactly in polynomial
time"). Individually `b`-bit coefficients alone do not obviously imply it, as `p(1) = ∑ c_S` can have many
terms. -/
def AnswerBits (b : ℕ) (c : Finset (Fin n) → ℚ) : Prop :=
  ∀ z : Fin n → ℚ, bits (pEval c z).num.natAbs + bits (pEval c z).den ≤
    2 * b + n + 2 * ∑ i, (bits (z i).num.natAbs + bits (z i).den)

end IterRoundDet


