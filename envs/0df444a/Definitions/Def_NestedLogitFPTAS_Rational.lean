-- Prove2me | Definitions.Def_NestedLogitFPTAS_Rational
-- name    : NestedLogitFPTAS_Rational
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:24.72793+00:00
-- url     : https://prove2.me/theorems/2770284b-38d4-41ee-992f-de4afa7d98d6
-- title:
--   §1.3, p.6 — rational instances and the input size
-- statement:
--   A rational instance has the data of an instance in $\mathbb Q$. Its input size is
--   $$
--   n+M+\sum_{x}\mathrm{bitLen}(x),
--   $$
--   summed over all the numbers of the instance, where the bit length of a rational is the number of bits of its numerator and of its denominator, plus one for the sign.
--
--   This is the "input size" of Theorem 1.1, which needs a finite representation of the data.
--
--   **Formalization Note** The accuracy guarantee of the mission holds for real data; only the bound on the operation count is stated in the bit length of rational data.
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Theorem 1.1, p.6

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model

namespace NestedLogitFPTAS

/-- A rational instance: the data of `Instance` in `ℚ`. This is what has an input size.

**Formalization Note.** Theorem 1.1 bounds the running time in "the input size", which needs a
finite representation; the accuracy guarantee holds for real data as well. -/
structure RatInstance (n M : ℕ) where
  nest : Fin n → Fin M
  r : Fin n → ℚ
  w : Fin n → ℚ
  c : Fin n → ℚ
  w0 : ℚ
  w0n : Fin M → ℚ
  γ : Fin M → ℚ
  C : ℚ

/-- The real instance with the same data. -/
def RatInstance.toReal {n M : ℕ} (J : RatInstance n M) : Instance n M where
  nest := J.nest
  r := fun i => (J.r i : ℝ)
  w := fun i => (J.w i : ℝ)
  c := fun i => (J.c i : ℝ)
  w0 := (J.w0 : ℝ)
  w0n := fun m => (J.w0n m : ℝ)
  γ := fun m => (J.γ m : ℝ)
  C := (J.C : ℝ)

/-- The bit length of a rational: numerator and denominator in binary, plus a sign bit. -/
def bitLen (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den + 1

/-- The binary size of a rational instance: `n + M` and the bit lengths of all its numbers. -/
def RatInstance.inputSize {n M : ℕ} (J : RatInstance n M) : ℕ :=
  n + M + (∑ i, bitLen (J.r i)) + (∑ i, bitLen (J.w i)) + (∑ i, bitLen (J.c i)) + bitLen J.w0 +
    (∑ m, bitLen (J.w0n m)) + (∑ m, bitLen (J.γ m)) + bitLen J.C

end NestedLogitFPTAS


