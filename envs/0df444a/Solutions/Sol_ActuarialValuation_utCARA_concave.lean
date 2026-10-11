-- Prove2me | solution 1 for ActuarialValuation.utCARA_concave
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:31:52.389934+00:00
-- url     : https://prove2.me/submissions/b524e6e2-3b59-49a8-bee6-8ed49af74563

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utCARASecond
open ActuarialValuation

theorem solution(a w : ℝ) : utCARASecond a w≤0 := by
  unfold utCARASecond
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg a)) (Real.exp_pos _).le
