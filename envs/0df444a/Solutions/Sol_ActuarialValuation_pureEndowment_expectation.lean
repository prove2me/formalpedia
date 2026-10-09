-- Prove2me | solution 1 for ActuarialValuation.pureEndowment_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:13:48.173167+00:00
-- url     : https://prove2.me/submissions/4058e447-bdc1-4a0f-9f6b-bf8b651e4a8e

import Mathlib
import Definitions.Def_actuarial_strictSurvivalEvent
import Definitions.Def_actuarial_pureEndowmentPV
import Theorems.Thm_ActuarialValuation_singlePayment_expectation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℝ) (hT : Measurable T)
    (hTnonneg : ∀ ω, 0 ≤ T ω) (v : ℝ) (n : ℕ)
    : (∫ ω, pureEndowmentPV T v n ω ∂P) = v ^ n * (P (strictSurvivalEvent T n)).toReal := by
  classical
  have hA : MeasurableSet (strictSurvivalEvent T n) := by
    change MeasurableSet (T ⁻¹' Set.Ioi (n : ℝ))
    exact hT measurableSet_Ioi
  unfold pureEndowmentPV
  simpa only [mul_one] using
    (singlePayment_expectation P (strictSurvivalEvent T n)
      hA (v ^ n) (1 : ℝ))
