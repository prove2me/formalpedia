-- Prove2me | solution 1 for ActuarialAnnuities.decrease_final
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:25:18.732464+00:00
-- url     : https://prove2.me/submissions/afe7fc6c-042c-4e3d-99f6-dc9e1c130ae6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bDecreasing
open ActuarialAnnuities

theorem solution(a n : ℕ) (hn : 0 < n) : bDecreasing a n (a+n-1) = 1 := by
  unfold bDecreasing
  have : n - (a + n - 1 - a) = 1 := by omega
  rw [this]
  norm_num
