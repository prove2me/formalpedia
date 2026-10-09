-- Prove2me | solution 1 for ActuarialValuation.deathYearEvent_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T19:19:33.811992+00:00
-- url     : https://prove2.me/submissions/baabec3d-d238-41ac-a168-fc617afeb6aa

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (K : Ω → ℕ) (hK : Measurable K)
    (k : ℕ)
    :
    MeasurableSet (deathYearEvent K k) := by
  change MeasurableSet (K ⁻¹' ({k} : Set ℕ))
  exact hK (measurableSet_singleton k)
