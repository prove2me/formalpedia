-- Prove2me | Definitions.Def_LevyStochCalc_Probability_Charlier_F000
-- name    : LevyStochCalc_Probability_Charlier_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:39:29.624277+00:00
-- url     : https://prove2.me/theorems/057b1e7f-3cae-4746-98ad-f055e6c6a798
-- title:
--   Source declarations: LevyStochCalc.Probability.Charlier
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.Charlier. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_PoissonMoments_F001
import Mathlib.Topology.Algebra.Polynomial

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Charlier polynomials and their Poisson orthogonality

The Charlier polynomials with parameter `lam` are given by the recursion
`C_(s+1)(x) = x C_s(x - 1) - lam C_s(x)` from `C_0 = 1`, the backward-difference analogue of the
Hermite recursion `H_(n+1) = (x - v d/dx) H_n`; their exponential generating function is
`e^(-lam t) (1 + t) ^ x`. The forward difference plays the role the derivative plays there,
`C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)`, and the degree-two member is
`C_2(x; lam) = (x - lam) ^ 2 - x`. The parameter is the mean of the Poisson law that makes the
family orthogonal: under the Poisson law of mean `r` the family with parameter `r` satisfies
`E[C_s C_t] = δ_(s t) s! r ^ s`.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_succ` — the recursion at the level of values.
* `LevyStochCalc.Probability.charlierScaled_two` — `C_2(x; lam) = (x - lam) ^ 2 - x`.
* `LevyStochCalc.Probability.charlierScaled_forward_diff` —
  `C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)`.
* `LevyStochCalc.Probability.integral_charlierPoly_mul` — `E[C_s C_t] = δ_(s t) s! r ^ s`.
* `LevyStochCalc.Probability.integral_charlierPoly_sq` — `E[C_s ^ 2] = s! r ^ s`.
* `LevyStochCalc.Probability.integral_charlierPoly_eq_zero` — `E[C_s] = 0` for `s ≠ 0`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal Nat

/-- The Charlier polynomial `C_s(x; lam)` of degree `s` with parameter `lam`, the mean of the
Poisson law under which the family is orthogonal: `C_0 = 1` and
`C_(s+1)(x) = x C_s(x - 1) - lam C_s(x)`, so that `∑_s C_s(x; lam) t ^ s / s!` is
`e^(-lam t) (1 + t) ^ x`. -/
noncomputable def charlierPoly (lam : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | (s + 1) => X * (charlierPoly lam s).comp (X - C 1) - C lam * charlierPoly lam s
@[simp] theorem charlierPoly_zero (lam : ℝ) : charlierPoly lam 0 = 1 := rfl
theorem charlierPoly_succ (lam : ℝ) (s : ℕ) :
    charlierPoly lam (s + 1)
      = X * (charlierPoly lam s).comp (X - C 1) - C lam * charlierPoly lam s := rfl
/-- The value `C_s(x; lam)` of the Charlier polynomial of degree `s` with parameter `lam`. -/
noncomputable def charlierScaled (s : ℕ) (lam x : ℝ) : ℝ := (charlierPoly lam s).eval x
@[simp] theorem charlierScaled_zero (lam x : ℝ) : charlierScaled 0 lam x = 1 := by
  simp [charlierScaled]
theorem charlierScaled_succ (s : ℕ) (lam x : ℝ) :
    charlierScaled (s + 1) lam x
      = x * charlierScaled s lam (x - 1) - lam * charlierScaled s lam x := by
  simp [charlierScaled, charlierPoly_succ, eval_comp]
@[simp] theorem charlierScaled_one (lam x : ℝ) : charlierScaled 1 lam x = x - lam := by
  rw [charlierScaled_succ]; simp
/-- The Charlier polynomial of degree two, `C_2(x; lam) = (x - lam) ^ 2 - x`. -/
theorem charlierScaled_two (lam x : ℝ) : charlierScaled 2 lam x = (x - lam) ^ 2 - x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, charlierScaled_succ]
  simp only [charlierScaled_one]
  ring
/-- The Charlier polynomials are continuous in their argument. -/
theorem continuous_charlierScaled (s : ℕ) (lam : ℝ) : Continuous (charlierScaled s lam) :=
  (charlierPoly lam s).continuous
end LevyStochCalc.Probability


