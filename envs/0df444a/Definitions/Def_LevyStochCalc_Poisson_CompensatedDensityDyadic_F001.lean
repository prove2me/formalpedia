-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityDyadic_F001
-- name    : LevyStochCalc_Poisson_CompensatedDensityDyadic_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:09:30.82671+00:00
-- url     : https://prove2.me/theorems/f506db1e-c49f-4795-8755-0f02aeb83dea
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityDyadic
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityDyadic. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityTruncation_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic time-discretisation of a mark-dependent integrand

The dyadic partition `tᵢ = i·T/2ⁿ` of `[0,T]`, the interval time-averages of a bounded
integrand `φ : Ω → ℝ → E → ℝ` with the mark carried as a parameter, and the piecewise-constant
evaluation `dyadicEval` built from them. For a bounded jointly measurable `φ`, the Lebesgue
density theorem gives almost-everywhere convergence of `dyadicEval` to `φ` in the time variable,
and dominated convergence upgrades it to convergence in `L²(P ⊗ ds ⊗ ν)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Dyadic time-discretisation (mark carried as a parameter)

The time direction is discretised by dyadic averaging, mirroring `Brownian/ItoDensity`,
but the integrand carries the mark `e`: the coefficient on the `k`-th dyadic interval is
the *previous*-interval time-average `(2ⁿ/T)∫_{tₖ₋₁}^{tₖ} φ(ω,u,e) du` (shifted left, so
it is `ℱ_{tₖ}`-measurable — adapted), evaluated as a function of `(ω, e)`. -/

/-- `closedBall ((a+b)/2) ((b-a)/2) = Icc a b`. -/
private lemma closedBall_eq_Icc (a b : ℝ) :
    Metric.closedBall ((a + b) / 2) ((b - a) / 2) = Set.Icc a b := by
  ext x
  simp only [Metric.mem_closedBall, Real.dist_eq, Set.mem_Icc]
  constructor
  · intro h
    have := abs_le.mp (show |x - (a + b) / 2| ≤ (b - a) / 2 from h)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro ⟨h1, h2⟩; rw [abs_le]; exact ⟨by linarith, by linarith⟩
end LevyStochCalc.Poisson.Compensated


