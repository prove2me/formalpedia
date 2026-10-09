-- Prove2me | solution 1 for ActuarialValuation.strictSurvivalEvent_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:13:11.301997+00:00
-- url     : https://prove2.me/submissions/0304da14-edcf-4317-8f7f-92887b32342d

import Mathlib
import Definitions.Def_actuarial_strictSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (T : Ω → ℝ) (hT : Measurable T) (n : ℕ)
    : MeasurableSet (strictSurvivalEvent T n) := by
  change MeasurableSet (T ⁻¹' Set.Ioi (n : ℝ))
  exact hT measurableSet_Ioi
