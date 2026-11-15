-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.brownian_adjacent_increments_product_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:01:13.436924+00:00
-- url     : https://prove2.me/submissions/49dd894d-e40a-4236-be59-424184c8267f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasIndepIncrements_readable
import Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_increment_gaussian_law
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (r s t : ℝ≥0)
    (hrs : r ≤ s) (hst : s ≤ t) :
    HasLaw
      (fun ω => (W.W (s : ℝ) ω - W.W (r : ℝ) ω,
        W.W (t : ℝ) ω - W.W (s : ℝ) ω))
      ((gaussianReal 0 (s - r)).prod (gaussianReal 0 (t - s))) P := by
  have hleft :=
    AppliedSDE.SarkkaSolin.brownian_increment_gaussian_law W r s hrs
  have hright :=
    AppliedSDE.SarkkaSolin.brownian_increment_gaussian_law W s t hst
  have hindep : IndepFun
      (fun ω => W.W (s : ℝ) ω - W.W (r : ℝ) ω)
      (fun ω => W.W (t : ℝ) ω - W.W (s : ℝ) ω) P :=
    (W.hasIndepIncrements_readable).indepFun_sub_sub hrs hst
  exact hindep.hasLaw_prod hleft hright
