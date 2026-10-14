-- Prove2me | solution 1 for ActuarialValuation.commPureEndowment_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:17.326465+00:00
-- url     : https://prove2.me/submissions/2907dab9-2576-4dfc-a0aa-03da2c682240

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commTerminalLives
import Definitions.Def_actuarial_commPureEndowment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : commDiscountedLives l v x ≠ 0) : commPureEndowment l v x n * commDiscountedLives l v x = commTerminalLives l v x n := by
  unfold commPureEndowment
  field_simp [hD]
