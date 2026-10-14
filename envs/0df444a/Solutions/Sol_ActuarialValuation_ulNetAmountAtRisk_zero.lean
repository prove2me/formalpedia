-- Prove2me | solution 1 for ActuarialValuation.ulNetAmountAtRisk_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:46:43.390826+00:00
-- url     : https://prove2.me/submissions/fb3803a7-3e83-490c-b96b-303746f69f0a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulNetAmountAtRisk
open ActuarialValuation

theorem solution(fund guarantee : ℝ) (h : guarantee ≤ fund) : ulNetAmountAtRisk fund guarantee=0 := by
  unfold ulNetAmountAtRisk
  exact max_eq_left (by linarith)
