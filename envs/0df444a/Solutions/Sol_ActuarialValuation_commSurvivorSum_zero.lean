-- Prove2me | solution 1 for ActuarialValuation.commSurvivorSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:23:47.082255+00:00
-- url     : https://prove2.me/submissions/4e9d61e0-6d59-46ab-99a1-3fa3d944e2ef

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commSurvivorSum
open ActuarialValuation

theorem solution(l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commSurvivorSum l v x 0 = 0 := by
  simp [commSurvivorSum]
