-- Prove2me | solution 1 for ActuarialValuation.futureTermLoss_after_maturity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:53:26.905982+00:00
-- url     : https://prove2.me/submissions/8d501bfb-eb34-4b67-82ee-6e4a5e8b681d

import Mathlib
import Definitions.Def_actuarial_futureTermLossPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (b π : ℝ) (ht : n ≤ t)
    :
    futureTermLossPV K v n t b π ω = 0 := by
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
