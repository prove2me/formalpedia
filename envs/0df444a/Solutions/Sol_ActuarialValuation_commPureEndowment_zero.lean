-- Prove2me | solution 1 for ActuarialValuation.commPureEndowment_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:17.429912+00:00
-- url     : https://prove2.me/submissions/ed891845-5fc0-4568-9f6c-54b043088ee0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commPureEndowment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) (h : commDiscountedLives l v x ≠ 0) : commPureEndowment l v x 0 = 1 := by
  simp [commPureEndowment, commTerminalLives, h]
