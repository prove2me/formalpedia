-- Prove2me | solution 1 for ActuarialValuation.irAvgCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:59:27.585748+00:00
-- url     : https://prove2.me/submissions/dec7d37c-bbc8-40aa-b5ac-2695c95a4940

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irAvgCost
open ActuarialValuation

theorem solution(cost count : ℝ) (hc : 0 ≤ cost) (hn : 0 < count) : 0 ≤ irAvgCost cost count := by
  unfold irAvgCost
  positivity
