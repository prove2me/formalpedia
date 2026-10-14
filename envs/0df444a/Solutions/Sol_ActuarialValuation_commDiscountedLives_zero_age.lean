-- Prove2me | solution 1 for ActuarialValuation.commDiscountedLives_zero_age
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:10.485493+00:00
-- url     : https://prove2.me/submissions/d7a3ddb0-9227-4f8d-883a-52201f6482c5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) : commDiscountedLives l v 0 = l 0 := by
  simp [commDiscountedLives]
