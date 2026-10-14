-- Prove2me | solution 1 for ActuarialValuation.pucProjectedUnit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:17:00.422362+00:00
-- url     : https://prove2.me/submissions/6d03ff76-d3e9-4a87-85f2-3f69407c9509

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucProjectedUnit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a s : ℝ) (ha : 0 ≤ a) (hs : 0 ≤ s) : 0 ≤ pucProjectedUnit a s := by
  unfold pucProjectedUnit
  exact mul_nonneg ha hs
