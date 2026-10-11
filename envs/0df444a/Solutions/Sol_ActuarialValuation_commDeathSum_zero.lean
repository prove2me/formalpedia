-- Prove2me | solution 1 for ActuarialValuation.commDeathSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:32:04.718578+00:00
-- url     : https://prove2.me/submissions/add31125-2067-45b0-89d4-3068ca610391

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDeathSum
open ActuarialValuation

theorem solution(l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commDeathSum l v x 0 = 0 := by
  simp [commDeathSum]
