-- Prove2me | solution 1 for ActuarialValuation.valuationSurvivalEvent_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:52:50.961005+00:00
-- url     : https://prove2.me/submissions/97c923df-9e47-48e4-a9de-ff03a019b9d0

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ)
    :
    valuationSurvivalEvent K 0 = Set.univ := by
  ext ω
  simp [valuationSurvivalEvent]
