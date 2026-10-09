-- Prove2me | solution 1 for ActuarialValuation.valuationSurvivalEvent_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:52:59.289817+00:00
-- url     : https://prove2.me/submissions/6c5b897d-b7dc-4154-88a7-6e7c62a31c27

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (K : Ω → ℕ) (hK : Measurable K) (t : ℕ)
    :
    MeasurableSet (valuationSurvivalEvent K t) := by
  change MeasurableSet (K ⁻¹' Set.Ici t)
  exact hK measurableSet_Ici
