-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.brownian_constant_drift_density_unit_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:12:03.618649+00:00
-- url     : https://prove2.me/submissions/b28403a9-2736-4510-9229-47152bd16eed

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_density_unit_mean
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (t : ℝ≥0) (theta : ℝ) :
    (∫ ω, Real.exp (theta * W.W (t : ℝ) ω -
          (t : ℝ) * theta ^ 2 / 2) ∂P) = 1 := by
  let g : ℝ → ℝ :=
    fun x => Real.exp (theta * x - (t : ℝ) * theta ^ 2 / 2)
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hmeas := W.measurable_eval (t : ℝ)
  have hlaw := W.hasLaw_eval_readable t
  change (∫ ω, g (W.W (t : ℝ) ω) ∂P) = 1
  calc
    (∫ ω, g (W.W (t : ℝ) ω) ∂P) =
        ∫ x, g x ∂(P.map (W.W (t : ℝ))) := by
      exact (integral_map hmeas.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ x, g x ∂(gaussianReal 0 t) := by
      rw [hlaw.map_eq]
    _ = 1 := by
      exact AppliedSDE.SarkkaSolin.gaussian_esscher_density_unit_mean t theta
