-- Prove2me | solution 1 for ActuarialValuation.prospectiveTermReserve_denominator_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:54:57.271993+00:00
-- url     : https://prove2.me/submissions/e2488644-60d5-4e24-9dc1-43c742acb462

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
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
    (v : ℝ) (n t : ℕ)
    (b π : ℝ)
    (hq : 0 < (P (valuationSurvivalEvent K t)).toReal)
    :
    (P (valuationSurvivalEvent K t)).toReal *
      prospectiveTermReservePV P K v n t b π =
      ∫ ω, futureTermLossPV K v n t b π ω ∂P := by
  have hn : (P (valuationSurvivalEvent K t)).toReal ≠ 0 := ne_of_gt hq
  unfold prospectiveTermReservePV
  field_simp [hn]
