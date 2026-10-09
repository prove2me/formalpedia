-- Prove2me | solution 1 for ActuarialValuation.annualReserve_after_term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:20:49.074749+00:00
-- url     : https://prove2.me/submissions/ed82ba70-db0b-4f77-a5e5-a6ead621aaa6

import Mathlib
import Definitions.Def_actuarial_annualProspectiveReserve
import Theorems.Thm_ActuarialValuation_annualFutureLoss_after_term
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  (v : ℝ) (n t : ℕ) (b π : ℝ) (ht : n ≤ t)
  : annualProspectiveReserve P K v n t b π = 0 := by
  have hz : (fun ω : Ω => annualFutureLoss K v n t b π ω) = 0 := by
    funext ω
    exact annualFutureLoss_after_term K v n t b π ω ht
  simp [annualProspectiveReserve, hz]
