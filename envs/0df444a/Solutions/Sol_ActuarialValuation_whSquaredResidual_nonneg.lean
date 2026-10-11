-- Prove2me | solution 1 for ActuarialValuation.whSquaredResidual_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:16:25.189431+00:00
-- url     : https://prove2.me/submissions/0ba508e8-0a27-4a1e-8a01-5f4785a44d58

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSquaredResidual
open ActuarialValuation

theorem solution(g q : ℝ) : 0 ≤ whSquaredResidual g q := by
  unfold whSquaredResidual
  positivity
