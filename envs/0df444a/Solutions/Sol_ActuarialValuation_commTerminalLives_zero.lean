-- Prove2me | solution 1 for ActuarialValuation.commTerminalLives_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:12:51.361656+00:00
-- url     : https://prove2.me/submissions/78c4df38-a103-4d71-8a17-89e020f3ea19

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commTerminalLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commTerminalLives l v x 0 = commDiscountedLives l v x := by
  simp [commTerminalLives]
