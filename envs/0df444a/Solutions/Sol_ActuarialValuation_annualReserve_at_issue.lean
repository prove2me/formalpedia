-- Prove2me | solution 1 for ActuarialValuation.annualReserve_at_issue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:20:38.679043+00:00
-- url     : https://prove2.me/submissions/41c1785d-b37a-46b4-b9c3-59e5e3dd8fb4

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
import Definitions.Def_actuarial_annualProspectiveReserve
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  (v : ℝ) (n : ℕ) (b π : ℝ)
  : annualProspectiveReserve P K v n 0 b π =
      ∫ ω, annualFutureLoss K v n 0 b π ω ∂P := by
  simp [annualProspectiveReserve, annualSurvivalMass]
