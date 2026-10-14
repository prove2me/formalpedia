-- Prove2me | solution 1 for ActuarialAnnuities.entitlement_required_age
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:33:36.308011+00:00
-- url     : https://prove2.me/submissions/a2a9fc2e-7ac2-4a74-ba3d-980d3112d917

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive
import Definitions.Def_actuarial_bEntitlement
import Definitions.Def_actuarial_bRequiredAge
open ActuarialAnnuities

theorem solution(a g delta j k : ℕ) : bEntitlement a g delta j k = bAlive k (bRequiredAge a g delta j) := by
  unfold bEntitlement bRequiredAge
  split_ifs <;> rfl
