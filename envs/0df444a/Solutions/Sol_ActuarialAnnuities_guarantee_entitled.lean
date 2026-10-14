-- Prove2me | solution 1 for ActuarialAnnuities.guarantee_entitled
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:13:27.939041+00:00
-- url     : https://prove2.me/submissions/38085769-8c53-48f0-9651-2a1ba61967bc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive
import Definitions.Def_actuarial_bEntitlement
open ActuarialAnnuities

theorem solution(a g delta j k : ℕ) (hj : j < a+g) : bEntitlement a g delta j k = bAlive k a := by
  unfold bEntitlement
  rw [if_pos hj]
