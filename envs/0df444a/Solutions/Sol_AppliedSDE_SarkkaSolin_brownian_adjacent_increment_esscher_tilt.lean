-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.brownian_adjacent_increment_esscher_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:12:36.372198+00:00
-- url     : https://prove2.me/submissions/e2848371-eee5-4802-8c5b-4f953813ac1c

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_adjacent_increments_product_gaussian
import Theorems.Thm_AppliedSDE_SarkkaSolin_joint_gaussian_increment_esscher_under_weighted_measure
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (r s t : ℝ≥0)
    (hrs : r < s) (hst : s < t) (theta : ℝ) :
    let X : Ω → ℝ := fun ω => W.W (s : ℝ) ω - W.W (r : ℝ) ω
    let Y : Ω → ℝ := fun ω => W.W (t : ℝ) ω - W.W (s : ℝ) ω
    (P.withDensity (fun ω =>
      ENNReal.ofReal
        (Real.exp (theta * X ω - ((s - r : ℝ≥0) : ℝ) * theta ^ 2 / 2)) *
      ENNReal.ofReal
        (Real.exp (theta * Y ω - ((t - s : ℝ≥0) : ℝ) * theta ^ 2 / 2)))).map
        (fun ω => (X ω, Y ω)) =
      (gaussianReal (((s - r : ℝ≥0) : ℝ) * theta) (s - r)).prod
        (gaussianReal (((t - s : ℝ≥0) : ℝ) * theta) (t - s)) := by
  let X : Ω → ℝ := fun ω => W.W (s : ℝ) ω - W.W (r : ℝ) ω
  let Y : Ω → ℝ := fun ω => W.W (t : ℝ) ω - W.W (s : ℝ) ω
  have hXY : HasLaw (fun ω => (X ω, Y ω))
      ((gaussianReal 0 (s - r)).prod (gaussianReal 0 (t - s))) P :=
    AppliedSDE.SarkkaSolin.brownian_adjacent_increments_product_gaussian
      W r s t hrs.le hst.le
  have hmeas : Measurable (fun ω : Ω => (X ω, Y ω)) :=
    ((W.measurable_eval _).sub (W.measurable_eval _)).prodMk
      ((W.measurable_eval _).sub (W.measurable_eval _))
  change (P.withDensity (fun ω =>
      ENNReal.ofReal
        (Real.exp (theta * X ω - ((s - r : ℝ≥0) : ℝ) * theta ^ 2 / 2)) *
      ENNReal.ofReal
        (Real.exp (theta * Y ω - ((t - s : ℝ≥0) : ℝ) * theta ^ 2 / 2)))).map
        (fun ω => (X ω, Y ω)) =
      (gaussianReal (((s - r : ℝ≥0) : ℝ) * theta) (s - r)).prod
        (gaussianReal (((t - s : ℝ≥0) : ℝ) * theta) (t - s))
  exact AppliedSDE.SarkkaSolin.joint_gaussian_increment_esscher_under_weighted_measure
    X Y (s - r) (t - s) (tsub_pos_iff_lt.mpr hrs) (tsub_pos_iff_lt.mpr hst) theta hmeas hXY
