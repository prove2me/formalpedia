-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.brownian_constant_drift_shifted_marginal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:47:09.984231+00:00
-- url     : https://prove2.me/submissions/5858df30-f537-4c71-8723-f80c78c0fb2c

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_tilt_measure
import Theorems.Thm_AppliedSDE_SarkkaSolin_likelihood_tilt_pushforward
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
    (P.withDensity
        (fun ω => ENNReal.ofReal
          (Real.exp (theta * W.W (t : ℝ) ω -
            (t : ℝ) * theta ^ 2 / 2)))).map
        (W.W (t : ℝ)) =
      gaussianReal ((t : ℝ) * theta) t := by
  let f : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal
      (Real.exp (theta * x - (t : ℝ) * theta ^ 2 / 2))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hpush :=
    AppliedSDE.SarkkaSolin.likelihood_tilt_pushforward
      P (W.W (t : ℝ)) (W.measurable_eval _) f hf
  have hlaw := W.hasLaw_eval_readable t
  change (P.withDensity (fun ω => f (W.W (t : ℝ) ω))).map
      (W.W (t : ℝ)) = gaussianReal ((t : ℝ) * theta) t
  calc
    (P.withDensity (fun ω => f (W.W (t : ℝ) ω))).map
        (W.W (t : ℝ)) =
        (P.map (W.W (t : ℝ))).withDensity f := hpush
    _ = (gaussianReal 0 t).withDensity f := by
      rw [hlaw.map_eq]
    _ = gaussianReal ((t : ℝ) * theta) t :=
      AppliedSDE.SarkkaSolin.gaussian_esscher_tilt_measure t ht theta
