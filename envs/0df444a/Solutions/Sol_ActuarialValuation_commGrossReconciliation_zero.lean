-- Prove2me | solution 1 for ActuarialValuation.commGrossReconciliation_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:20.430623+00:00
-- url     : https://prove2.me/submissions/574ad098-f82a-4f00-9e22-8fc31ab220ef

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commGrossReconciliation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commGrossReconciliation l v x 0 = commDiscountedLives l v x := by
  simp [commGrossReconciliation, commDeathSum, commSurvivorSum, commTerminalLives]
