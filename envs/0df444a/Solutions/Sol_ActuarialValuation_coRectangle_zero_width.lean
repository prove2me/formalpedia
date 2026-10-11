-- Prove2me | solution 1 for ActuarialValuation.coRectangle_zero_width
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:35:16.51898+00:00
-- url     : https://prove2.me/submissions/3876092c-4c15-4974-8182-c7539c3c4c3e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coRectangle
open ActuarialValuation

theorem solution(C : ℝ → ℝ → ℝ) (u v1 v2 : ℝ) : coRectangle C u u v1 v2=0 := by
  unfold coRectangle
  ring
