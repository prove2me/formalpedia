-- Prove2me | solution 1 for ActuarialValuation.cm1LoanBalance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:50.401679+00:00
-- url     : https://prove2.me/submissions/c1b32f8a-dcd4-4530-881f-47a9dfb30ba6

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1LoanBalance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n t : ℕ) (i : ℝ) (hi : -1 < i) (hc : ∀ k ∈ Finset.range n, 0 ≤ c k) : 0 ≤ cm1LoanBalance c n t i := by
  unfold cm1LoanBalance
  apply Finset.sum_nonneg
  intro k hk
  split_ifs with h
  · have hp : 0 < 1 + i := by linarith
    have hd : 0 ≤ cm1Discount i (k + 1 - t) := by
      exact le_of_lt (show 0 < cm1Discount i (k + 1 - t) by
        simp only [cm1Discount, cm1Accum]
        exact one_div_pos.mpr (pow_pos hp (k + 1 - t)))
    exact mul_nonneg (hc k hk) hd
  · norm_num
