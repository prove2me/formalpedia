-- Prove2me | solution 1 for ActuarialValuation.commDiscountedLives_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:35.040714+00:00
-- url     : https://prove2.me/submissions/3916827a-5249-42c8-a55a-e818ea871bd7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) (hl : 0 < l x) (hv : 0 < v) : 0 < commDiscountedLives l v x := by
  unfold commDiscountedLives
  exact mul_pos (pow_pos hv _) hl
