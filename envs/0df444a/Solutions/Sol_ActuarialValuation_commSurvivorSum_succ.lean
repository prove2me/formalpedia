-- Prove2me | solution 1 for ActuarialValuation.commSurvivorSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:58.701986+00:00
-- url     : https://prove2.me/submissions/290d4403-b4f8-442f-9bc3-227cd5abf52f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commSurvivorSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : commSurvivorSum l v x (n+1) = commSurvivorSum l v x n + commDiscountedLives l v (x+n) := by
  simp only [commSurvivorSum, Finset.sum_range_succ]
