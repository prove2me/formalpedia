-- Prove2me | solution 1 for ActuarialValuation.coInd_tail_factor
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:37:31.320077+00:00
-- url     : https://prove2.me/submissions/6d8af4da-dfb9-41ee-8563-07cba8d6be48

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coInd
import Definitions.Def_actuarial_coTailJoint
open ActuarialValuation

theorem solution(u v : ℝ) : coTailJoint coInd u v=(1-u)*(1-v) := by
  first
  | (simp [coInd, coTailJoint]; done)
  | (norm_num [coInd, coTailJoint]; done)
  | (unfold coInd coTailJoint; positivity)
  | (simp only [coInd, coTailJoint]; positivity)
  | (unfold coInd coTailJoint; ring)
  | (unfold coInd coTailJoint; simp; done)
  | (unfold coInd coTailJoint; norm_num; done)
  | (simp [coInd, coTailJoint]; ring)
  | (unfold coInd coTailJoint; split_ifs <;> simp_all <;> linarith)
  | (unfold coInd coTailJoint; nlinarith [sq_nonneg 0])
  | (simp_all [coInd, coTailJoint]; done)
  | (unfold coInd coTailJoint; simp_all; done)
  | rfl
