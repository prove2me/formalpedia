-- Prove2me | solution 1 for ActuarialValuation.commTermAssurance_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:05.615483+00:00
-- url     : https://prove2.me/submissions/1c05ae53-43f0-4fcb-bc34-24d09b924523

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commDeathSum
import Definitions.Def_actuarial_commTermAssurance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : commDiscountedLives l v x ≠ 0) : commTermAssurance l v x n * commDiscountedLives l v x = commDeathSum l v x n := by
  unfold commTermAssurance
  field_simp [hD]
