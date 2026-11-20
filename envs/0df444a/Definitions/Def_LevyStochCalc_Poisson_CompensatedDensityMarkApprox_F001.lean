-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F001
-- name    : LevyStochCalc_Poisson_CompensatedDensityMarkApprox_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:46:45.331853+00:00
-- url     : https://prove2.me/theorems/f1361a58-e58a-4058-8576-02c3dc6a7b21
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityMarkApprox
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityMarkApprox. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRectSimple_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark discretisation of the shifted dyadic eval

Approximation of the mark dependence of the adapted dyadic eval by finite mark-simple functions
`∑ₖ cₖ(ω) 𝟙_{Bₖ}(e)` with bounded, adapted coefficients, obtained by running the rectangle
density argument on each time piece over the trimmed product measure. Summing the per-piece
errors gives an `L²(P ⊗ ds ⊗ ν)` approximating sequence of adapted, mark-simple,
piecewise-constant-in-time integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Pulling a finite constant out of the nested `∫⁻ω∫⁻s∫⁻e` triple integral. -/
lemma lintegral_triple_const_mul
    {P : Measure Ω} {ν : Measure E} {T : ℝ} (c : ℝ≥0∞) (hc : c ≠ ⊤) (u : Ω → ℝ → E → ℝ≥0∞) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, c * u ω s e ∂ν ∂volume ∂P
      = c * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, u ω s e ∂ν ∂volume ∂P := by
  simp_rw [MeasureTheory.lintegral_const_mul' c _ hc]
end LevyStochCalc.Poisson.Compensated


