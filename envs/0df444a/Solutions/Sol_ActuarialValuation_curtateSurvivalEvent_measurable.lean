-- Prove2me | solution 1 for ActuarialValuation.curtateSurvivalEvent_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:13:21.016062+00:00
-- url     : https://prove2.me/submissions/e1c22f74-ca32-45c6-a2e9-a1659815afb2

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (K : Ω → ℕ) (hK : Measurable K) (n : ℕ)
    : MeasurableSet (curtateSurvivalEvent K n) := by
  change MeasurableSet (K ⁻¹' Set.Ici n)
  exact hK measurableSet_Ici
