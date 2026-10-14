-- Prove2me | solution 1 for ActuarialAnnuities.after_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:17:06.282745+00:00
-- url     : https://prove2.me/submissions/ce308204-994a-4022-bbdc-4a832a6ab48a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive
import Definitions.Def_actuarial_bEntitlement
open ActuarialAnnuities

theorem solution(a g delta j k : ℕ) (hj : a+g ≤ j) : bEntitlement a g delta j k = bAlive k (j+delta) := by
  unfold bEntitlement
  rw [if_neg (by omega)]
