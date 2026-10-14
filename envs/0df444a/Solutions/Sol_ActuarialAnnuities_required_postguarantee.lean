-- Prove2me | solution 1 for ActuarialAnnuities.required_postguarantee
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:12:00.41503+00:00
-- url     : https://prove2.me/submissions/be8de381-0497-430e-835c-fd9651e3098b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bRequiredAge
open ActuarialAnnuities

theorem solution(a g delta j : ℕ) (hj : a+g ≤ j) : bRequiredAge a g delta j = j+delta := by
  unfold bRequiredAge
  rw [if_neg (by omega)]
