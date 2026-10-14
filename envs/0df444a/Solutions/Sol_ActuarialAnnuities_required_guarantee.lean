-- Prove2me | solution 1 for ActuarialAnnuities.required_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T07:28:31.639815+00:00
-- url     : https://prove2.me/submissions/2aff4660-5fdf-4bd6-ac5e-28866fa72b5e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bRequiredAge
open ActuarialAnnuities

theorem solution(a g delta j : ℕ) (hj : j < a+g) : bRequiredAge a g delta j = a := by
  unfold bRequiredAge
  rw [if_pos hj]
