-- Prove2me | solution 1 for ActuarialValuation.commGrossReconciliation_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:21:07.194393+00:00
-- url     : https://prove2.me/submissions/811d0707-defc-4b54-977f-55528dc7f7cb

import Theorems.Thm_ActuarialValuation_commGrossReconciliation_succ
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commGrossReconciliation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) : commGrossReconciliation l v x n = commDiscountedLives l v x := by
  induction n with
  | zero =>
    simp [commGrossReconciliation, commDeathSum, commSurvivorSum, commTerminalLives]
  | succ n ih =>
    rw [ActuarialValuation.commGrossReconciliation_succ]
    exact ih
