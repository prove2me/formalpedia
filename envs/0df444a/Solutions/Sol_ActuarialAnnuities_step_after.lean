-- Prove2me | solution 1 for ActuarialAnnuities.step_after
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:26:05.550387+00:00
-- url     : https://prove2.me/submissions/a1da4b37-a003-46ed-b3ea-0737c062fe84

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bStep
open ActuarialAnnuities

theorem solution(a r j : ℕ) (c d : ℝ) (hj : a+r ≤ j) : bStep a r c d j = d := by
  unfold bStep
  rw [if_neg (by omega)]
