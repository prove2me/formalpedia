-- Prove2me | solution 1 for ActuarialValuation.scrUncorrelatedSquared_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:26:22.996788+00:00
-- url     : https://prove2.me/submissions/acb72f28-d6c9-4f0b-8555-5e9f338d68c5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrUncorrelatedSquared
open ActuarialValuation

theorem solution(a b : ℝ) : 0 ≤ scrUncorrelatedSquared a b := by
  unfold scrUncorrelatedSquared
  positivity
