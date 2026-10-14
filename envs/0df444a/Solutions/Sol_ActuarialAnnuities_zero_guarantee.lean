-- Prove2me | solution 1 for ActuarialAnnuities.zero_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:13:26.106968+00:00
-- url     : https://prove2.me/submissions/03c27645-610d-4560-8f52-43ab2b9ab73e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive
import Definitions.Def_actuarial_bEntitlement
open ActuarialAnnuities

theorem solution(a delta j k : ℕ) (hj : a ≤ j) : bEntitlement a 0 delta j k = bAlive k (j+delta) := by
  unfold bEntitlement
  rw [if_neg (by omega)]
