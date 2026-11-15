-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.brownian_constant_drift_esscher_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:01:41.534212+00:00
-- url     : https://prove2.me/submissions/726a6980-8bd4-42e4-bc10-1e2450dd3a10

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_constant_drift_shifted_marginal
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
    (t : ℝ≥0) (ht : 0 < t) (theta : ℝ) :
    IsProbabilityMeasure
      (P.withDensity
        (fun ω => ENNReal.ofReal
          (Real.exp (theta * W.W (t : ℝ) ω -
            (t : ℝ) * theta ^ 2 / 2)))) := by
  let Q : Measure Ω := P.withDensity
    (fun ω => ENNReal.ofReal
      (Real.exp (theta * W.W (t : ℝ) ω -
        (t : ℝ) * theta ^ 2 / 2)))
  have hlaw : Q.map (W.W (t : ℝ)) =
      gaussianReal ((t : ℝ) * theta) t :=
    AppliedSDE.SarkkaSolin.brownian_constant_drift_shifted_marginal
      W t ht theta
  have hmeas : Measurable (W.W (t : ℝ)) := W.measurable_eval _
  change IsProbabilityMeasure Q
  refine ⟨?_⟩
  calc
    Q Set.univ = (Q.map (W.W (t : ℝ))) Set.univ := by
      rw [Measure.map_apply hmeas MeasurableSet.univ]
      simp
    _ = (gaussianReal ((t : ℝ) * theta) t) Set.univ := by
      rw [hlaw]
    _ = 1 := by simp
