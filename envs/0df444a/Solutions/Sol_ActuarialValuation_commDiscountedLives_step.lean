-- Prove2me | solution 1 for ActuarialValuation.commDiscountedLives_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:14.34098+00:00
-- url     : https://prove2.me/submissions/6f1d2ff4-381b-4449-908a-f442a634980c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commDiscountedLives l v (x+1) = v^(x+1)*l (x+1) := by
  rfl
