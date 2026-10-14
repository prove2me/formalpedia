-- Prove2me | solution 1 for ActuarialValuation.commTemporaryAnnuity_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:50.35249+00:00
-- url     : https://prove2.me/submissions/754d9067-8774-4c83-a825-bd6c3b5691a5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commTemporaryAnnuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commTemporaryAnnuity l v x 0 = 0 := by
  simp [commTemporaryAnnuity, commSurvivorSum]
