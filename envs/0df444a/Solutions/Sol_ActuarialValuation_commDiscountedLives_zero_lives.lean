-- Prove2me | solution 1 for ActuarialValuation.commDiscountedLives_zero_lives
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:23.33037+00:00
-- url     : https://prove2.me/submissions/06877e98-3fd9-4ed8-b087-10f129bf1853

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v : ℝ) (x : ℕ) : commDiscountedLives (fun _ => 0) v x = 0 := by
  simp [commDiscountedLives]
