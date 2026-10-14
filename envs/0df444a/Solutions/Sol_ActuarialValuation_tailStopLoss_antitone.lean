-- Prove2me | solution 1 for ActuarialValuation.tailStopLoss_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:21.377032+00:00
-- url     : https://prove2.me/submissions/5f8b0798-3833-462e-b97f-68b9c6200468

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_tailStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) (t u : ℝ) (ht : t ≤ u)
    (hp : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) :
    tailStopLoss p n u ≤ tailStopLoss p n t := by
  unfold tailStopLoss
  apply Finset.sum_le_sum
  intro k hk
  refine mul_le_mul_of_nonneg_right ?_ (hp k hk)
  unfold tailExcess
  refine max_le_max ?_ le_rfl
  exact sub_le_sub_left ht k
