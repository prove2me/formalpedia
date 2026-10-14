-- Prove2me | solution 1 for ActuarialValuation.irPriceIndex_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:40:54.75797+00:00
-- url     : https://prove2.me/submissions/839bfae4-5c0f-4c10-ba6c-a854587b552e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irPriceIndex
open ActuarialValuation

theorem solution(base growth : ℝ) (hb : 0 < base) (hg : -1 < growth) : 0 < irPriceIndex base growth := by
  unfold irPriceIndex
  apply mul_pos hb
  linarith
