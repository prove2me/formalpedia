-- Prove2me | solution 1 for ActuarialValuation.commSurvivorSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:10.564994+00:00
-- url     : https://prove2.me/submissions/58f08e22-a018-400f-908f-dfbc3049f67e

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commSurvivorSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (h : ∀ k ∈ Finset.range n, 0 ≤ commDiscountedLives l v (x+k)) : 0 ≤ commSurvivorSum l v x n := by
  unfold commSurvivorSum
  apply Finset.sum_nonneg
  intro k hk
  exact h k hk
