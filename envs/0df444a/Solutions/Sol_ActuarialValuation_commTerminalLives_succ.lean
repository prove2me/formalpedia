-- Prove2me | solution 1 for ActuarialValuation.commTerminalLives_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:05.291431+00:00
-- url     : https://prove2.me/submissions/92429a36-9fe7-4b6e-85bf-5753eebb71d2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commTerminalLives

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : commTerminalLives l v x (n+1) = commDiscountedLives l v (x+n+1) := by
  simp only [commTerminalLives, Nat.add_assoc]
