-- Prove2me | solution 1 for ActuarialValuation.prospectiveTermReserve_after_maturity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:54:48.731473+00:00
-- url     : https://prove2.me/submissions/53e25a35-e5a8-4b3b-ab1c-5b2f56ac512d

import Mathlib
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
    (b π : ℝ) (ht : n ≤ t)
    :
    prospectiveTermReservePV P K v n t b π = 0 := by
  have hf : ∀ ω, futureTermLossPV K v n t b π ω = 0 := by
    intro ω
    have hb : futureTermBenefitPV K v n t ω = 0 := by
      unfold futureTermBenefitPV
      split_ifs with h
      · omega
      · rfl
    have hp : futureTermPremiumPV K v n t ω = 0 := by
      unfold futureTermPremiumPV
      apply Finset.sum_eq_zero
      intro j hj
      have hjlt : j < n := Finset.mem_range.mp hj
      have hnot : ¬ (t ≤ j ∧ j ≤ K ω) := by omega
      simp [hnot]
    simp [futureTermLossPV, hb, hp]
  simp [prospectiveTermReservePV, hf]
