-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossPremium_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:22:47.25331+00:00
-- url     : https://prove2.me/submissions/0023dfbc-effa-4c5c-9af2-b30c1dd21b0e

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium
import Definitions.Def_actuarial_discreteStopLossTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound deductible : ℕ) :
  discreteStopLossPremium w bound deductible =
    discreteStopLossPremium w bound (deductible + 1) +
      discreteStopLossTail w bound deductible := by
  unfold discreteStopLossPremium discreteStopLossTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hd : deductible < s
  · have hp : s - deductible = s - (deductible + 1) + 1 := by omega
    simp only [discreteStopLossPayment, if_pos hd]
    rw [hp]
    push_cast
    ring
  · have hsd : s ≤ deductible := Nat.le_of_not_gt hd
    have hsd1 : s ≤ deductible + 1 := by omega
    simp [discreteStopLossPayment, Nat.sub_eq_zero_of_le hsd,
      Nat.sub_eq_zero_of_le hsd1, hd]
