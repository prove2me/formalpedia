-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.brownian_constant_drift_centered_marginal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:12:28.422973+00:00
-- url     : https://prove2.me/submissions/fe8837c8-eb93-4a1d-aae4-f963b5ee4dc8

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
    (P.withDensity
        (fun ω => ENNReal.ofReal
          (Real.exp (theta * W.W (t : ℝ) ω -
            (t : ℝ) * theta ^ 2 / 2)))).map
        (fun ω => W.W (t : ℝ) ω - (t : ℝ) * theta) =
      gaussianReal 0 t := by
  let Q : Measure Ω := P.withDensity
    (fun w => ENNReal.ofReal
      (Real.exp (theta * W.W (t : Real) w -
        (t : Real) * theta ^ 2 / 2)))
  have hshift : Q.map (W.W (t : Real)) =
      gaussianReal ((t : Real) * theta) t :=
    AppliedSDE.SarkkaSolin.brownian_constant_drift_shifted_marginal
      W t ht theta
  have hmeas : Measurable (W.W (t : Real)) := W.measurable_eval _
  have hLaw : HasLaw (W.W (t : Real))
      (gaussianReal ((t : Real) * theta) t) Q :=
    ⟨hmeas.aemeasurable, hshift⟩
  have hcenter := gaussianReal_sub_const hLaw ((t : Real) * theta)
  change Q.map (fun w => W.W (t : Real) w - (t : Real) * theta) =
    gaussianReal 0 t
  simpa only [sub_self] using hcenter.map_eq
