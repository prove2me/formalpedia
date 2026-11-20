-- Prove2me | Definitions.Def_LevyStochCalc_Probability_Charlier_F002
-- name    : LevyStochCalc_Probability_Charlier_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:13:02.25331+00:00
-- url     : https://prove2.me/theorems/1908c0af-90ed-4fe8-a192-4da3b7e208ae
-- title:
--   LevyStochCalc source module: LevyStochCalc.Probability.Charlier
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Probability.Charlier in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Charlier_F000
import Definitions.Def_SourceProof_5e9757a88ef83b24bbaf0d97

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

/-- The `L²` norm of a Charlier polynomial under the Poisson law whose mean is its parameter,
`E[C_s ^ 2] = s! r ^ s`. -/
theorem integral_charlierPoly_sq (r : ℝ≥0) (s : ℕ) :
    ∫ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ) ^ 2 ∂poissonMeasure r
      = (s.factorial : ℝ) * (r : ℝ) ^ s := by
  simpa [pow_two] using _root_.Prove2MeSourceProof.h_5e9757a88ef83b24bbaf0d97 r s s
/-- A Charlier polynomial of positive degree is centred under the Poisson law whose mean is its
parameter. -/
theorem integral_charlierPoly_eq_zero (r : ℝ≥0) {s : ℕ} (hs : s ≠ 0) :
    ∫ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ) ∂poissonMeasure r = 0 := by
  simpa [hs] using _root_.Prove2MeSourceProof.h_5e9757a88ef83b24bbaf0d97 r s 0
end LevyStochCalc.Probability


