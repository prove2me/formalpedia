-- Prove2me | solution 1 for ActuarialValuation.futureTermPremium_after_maturity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:53:18.328248+00:00
-- url     : https://prove2.me/submissions/dc5e754b-df46-4244-988e-2bd3c1ecae32

import Mathlib
import Definitions.Def_actuarial_futureTermPremiumPV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (ω : Ω)
    (ht : n ≤ t)
    :
    futureTermPremiumPV K v n t ω = 0 := by
  unfold futureTermPremiumPV
  apply Finset.sum_eq_zero
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hnot : ¬ (t ≤ j ∧ j ≤ K ω) := by omega
  simp [hnot]
