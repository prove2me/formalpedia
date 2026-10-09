-- Prove2me | solution 1 for ActuarialValuation.prospectiveTermReserve_at_issue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:54:40.211144+00:00
-- url     : https://prove2.me/submissions/ffd9a848-e691-4de1-af0c-c9c5109b4bbb

import Mathlib
import Definitions.Def_actuarial_futureTermLossPV
import Definitions.Def_actuarial_prospectiveTermReservePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n : ℕ)
    (b π : ℝ)
    :
    prospectiveTermReservePV P K v n 0 b π =
      ∫ ω, futureTermLossPV K v n 0 b π ω ∂P := by
  simp [prospectiveTermReservePV, valuationSurvivalEvent]
