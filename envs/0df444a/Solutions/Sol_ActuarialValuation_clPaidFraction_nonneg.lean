-- Prove2me | solution 1 for ActuarialValuation.clPaidFraction_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:46:17.52478+00:00
-- url     : https://prove2.me/submissions/955585c8-5a96-499e-a7cb-cf0ec9173dd7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidFraction
open ActuarialValuation

theorem solution(f : ℝ) (h : 0 < f) : 0 ≤ clPaidFraction f := by
  unfold clPaidFraction
  positivity
