-- Prove2me | solution 1 for ActuarialValuation.commLifeValueBalance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:34.413807+00:00
-- url     : https://prove2.me/submissions/8799f587-df62-4b65-aaed-93ad24311d34

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commLifeValueBalance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) (hD : commDiscountedLives l v x ≠ 0) : commLifeValueBalance l v x 0 = 1 := by
  simp [commLifeValueBalance, commTermAssurance, commTemporaryAnnuity, commPureEndowment, commDeathSum, commSurvivorSum, commTerminalLives, hD]
