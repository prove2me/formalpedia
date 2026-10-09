-- Prove2me | solution 2 for ActuarialValuation.annualReserve_at_issue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:23:08.358519+00:00
-- url     : https://prove2.me/submissions/c38a14e0-bf03-40fc-8e68-a3dacc620578

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
import Definitions.Def_actuarial_annualProspectiveReserve
import Theorems.Thm_ActuarialValuation_annualSurvivalMass_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ)
  (hK : Measurable K) (v : ℝ) (n : ℕ) (b π : ℝ) :
  annualProspectiveReserve P K v n 0 b π =
    ∫ ω, annualFutureLoss K v n 0 b π ω ∂P := by
  simp [annualProspectiveReserve, annualSurvivalMass_zero P K hK]
