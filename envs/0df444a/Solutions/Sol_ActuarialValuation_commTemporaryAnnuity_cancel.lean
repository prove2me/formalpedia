-- Prove2me | solution 1 for ActuarialValuation.commTemporaryAnnuity_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:15:08.849794+00:00
-- url     : https://prove2.me/submissions/42829e69-0f15-4cdd-b266-3da781da5011

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commSurvivorSum
import Definitions.Def_actuarial_commTemporaryAnnuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : commDiscountedLives l v x ≠ 0) : commTemporaryAnnuity l v x n * commDiscountedLives l v x = commSurvivorSum l v x n := by
  unfold commTemporaryAnnuity
  field_simp [hD]
