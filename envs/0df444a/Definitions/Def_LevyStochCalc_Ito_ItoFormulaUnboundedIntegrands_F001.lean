-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F001
-- name    : LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:49:13.087534+00:00
-- url     : https://prove2.me/theorems/3f06e264-99f3-4c05-8826-d74f95facfe5
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaUnboundedIntegrands. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands of the clamped approximation of a vector Itô process

For a function whose first and second derivatives are bounded, the drift integrals, the quadratic
variation terms and the diffusion integrands built from the coefficients clamped at a level growing
to infinity converge to the ones built from the original coefficients: the drift and quadratic
variation terms pathwise, the diffusion integrands in energy on a bounded window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Limits

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)

omit [IsProbabilityMeasure P] in
/-- Additivity of the window energy. -/
theorem lintegral_window_add {f g : Ω → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (f ω s + g ω s) ∂volume ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, g ω s ∂volume ∂P := by
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (f ω s + g ω s) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, g ω s ∂volume :=
    fun ω => MeasureTheory.lintegral_add_left (Measurable.of_uncurry_left hf) _
  simp_rw [hinner]
  exact MeasureTheory.lintegral_add_left hf.lintegral_prod_right' _
omit [IsProbabilityMeasure P] in
/-- Constants come out of the window energy. -/
theorem lintegral_window_const_mul {f : Ω → ℝ → ℝ≥0∞}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, c * f ω s ∂volume ∂P
      = c * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume ∂P := by
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, c * f ω s ∂volume
      = c * ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume :=
    fun ω => MeasureTheory.lintegral_const_mul' _ _ hc
  simp_rw [hinner]
  exact MeasureTheory.lintegral_const_mul' _ _ hc
end Limits

end Clamped

end LevyStochCalc.Brownian.Ito


