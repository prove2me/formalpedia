-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossPremium_above_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:21:13.459754+00:00
-- url     : https://prove2.me/submissions/54e7b48d-8c52-4b40-99a4-620eb052bda9

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (h : bound ≤ deductible) :
  discreteStopLossPremium w bound deductible = 0 := by
  unfold discreteStopLossPremium
  apply Finset.sum_eq_zero
  intro s hs
  have hsb : s ≤ bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  simp [discreteStopLossPayment, Nat.sub_eq_zero_of_le (le_trans hsb h)]
