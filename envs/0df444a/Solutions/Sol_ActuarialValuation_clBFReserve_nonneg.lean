-- Prove2me | solution 1 for ActuarialValuation.clBFReserve_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:05:14.427387+00:00
-- url     : https://prove2.me/submissions/ed16b69b-059b-4d01-a6d3-2314a827e642

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clBFReserve
open ActuarialValuation

theorem solution(e f : ℝ) (he : 0 ≤ e) (hf : 1 ≤ f) : 0 ≤ clBFReserve e f := by
  unfold clBFReserve clUnpaidFraction clPaidFraction
  apply mul_nonneg he
  rw [sub_nonneg, div_le_one (by linarith)]
  exact hf
