-- Prove2me | solution 1 for ActuarialValuation.annualSurvivalMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:18:11.658762+00:00
-- url     : https://prove2.me/submissions/4e83c0fe-9f64-4196-8041-ca2acf5cba66

import Mathlib
import Definitions.Def_actuarial_annualSurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  : annualSurvivalMass P K 0 = 1 := by
  simp [annualSurvivalMass]
