-- Prove2me | solution 1 for ActuarialValuation.cxTwoClaimMean_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:03:59.804497+00:00
-- url     : https://prove2.me/submissions/70a5d2f9-aec4-491c-a5bb-42d7ae7dec40

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxTwoClaimMean
open ActuarialValuation

theorem solution(mean p1 : ℝ) : cxTwoClaimMean mean p1 0 = p1*mean := by
  unfold cxTwoClaimMean
  ring
