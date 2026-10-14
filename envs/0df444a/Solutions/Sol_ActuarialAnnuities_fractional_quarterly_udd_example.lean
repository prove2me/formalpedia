-- Prove2me | solution 1 for ActuarialAnnuities.fractional_quarterly_udd_example
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:51:16.497431+00:00
-- url     : https://prove2.me/submissions/83a91111-6cb1-409e-bbe2-5c400f8e9fcd

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bFractionalExpectedPV
open ActuarialAnnuities

theorem solution: bFractionalExpectedPV 3 0 3 0 0 4 1 (fun _ => 1) (fun k => if k ≤ 3 then (1/4 : ℝ) else 0) = 63/32 := by
  unfold bFractionalExpectedPV bExpectedPV bPathPV bUDDMicroMass bEntitlement bAlive
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
