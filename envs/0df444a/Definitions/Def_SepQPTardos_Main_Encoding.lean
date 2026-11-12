-- Prove2me | Definitions.Def_SepQPTardos_Main_Encoding
-- name    : SepQPTardos_Main_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:28.464721+00:00
-- url     : https://prove2.me/theorems/20737ebb-8409-424e-9e05-ff1c4a9882b3
-- title:
--   Binary encoding lengths of integers, rationals, vectors and matrices
-- statement:
--   The paper measures inputs by their binary encoding length but fixes no convention. This definition fixes one:
--
--   1. an integer $z$ has length $\langle z\rangle=1+\operatorname{size}(|z|)$, where $\operatorname{size}(n)$ is the number of binary digits of $n$ (so $\langle 0\rangle=1$);
--   2. a rational $p/q$ in lowest terms with $q\ge1$ has length $\langle p/q\rangle=\langle p\rangle+\operatorname{size}(q)$;
--   3. a vector or matrix has the sum of the lengths of its entries; in particular $\langle A\rangle=\sum_{i,e}\langle A_{ie}\rangle$.
--
--   A real number **has encoding length at most** $B$ if it equals a rational of length at most $B$. All standard conventions agree with this one up to polynomial factors, which is all that the polynomial bounds of the mission use.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §1, p. 2 ("⟨A⟩ denotes the binary encoding length of A"); Theorem 1.1, p. 2; §4.5, p. 11

import Mathlib

namespace SepQPTardos.Main

/-!
# Binary encoding lengths

Cui–Li–Miao, STOC 2027 submission #829 (October 2026), §1, p. 2 ("⟨A⟩ denotes the binary
encoding length of A") and Theorem 1.1, p. 2 ("encoding length polynomial in the complete
input"); §4.5, p. 11. The paper fixes no convention; this file fixes one. All standard
conventions agree up to polynomial factors.

* an integer `z` has length `⟨z⟩ = 1 + size |z|` (a sign bit plus the binary digits of `|z|`;
  `⟨0⟩ = 1`);
* a rational in lowest terms `p/q` (`q ≥ 1`) has length `⟨p⟩ + size q`;
* a vector or matrix has the sum of the lengths of its entries.
-/

/-- Binary encoding length of an integer: `1 + Nat.size |z|`. -/
def intLen (z : ℤ) : ℕ := 1 + Nat.size z.natAbs

/-- Binary encoding length of a rational in lowest terms: numerator length plus the binary
length of the (positive) denominator. -/
def ratLen (x : ℚ) : ℕ := intLen x.num + Nat.size x.den

/-- Encoding length of a rational vector: the sum over its entries. -/
def vecLen {n : ℕ} (v : Fin n → ℚ) : ℕ := ∑ i, ratLen (v i)

/-- Encoding length `⟨A⟩` of an integer matrix: the sum over its entries. -/
def intMatLen {p n : ℕ} (A : Matrix (Fin p) (Fin n) ℤ) : ℕ := ∑ i, ∑ j, intLen (A i j)

/-- Encoding length of a rational matrix: the sum over its entries. -/
def ratMatLen {p n : ℕ} (M : Matrix (Fin p) (Fin n) ℚ) : ℕ := ∑ i, ∑ j, ratLen (M i j)

/-- The real number `x` is a rational of encoding length at most `B`. -/
def RealLenLe (x : ℝ) (B : ℕ) : Prop := ∃ p : ℚ, (p : ℝ) = x ∧ ratLen p ≤ B

end SepQPTardos.Main


