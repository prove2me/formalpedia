-- Prove2me | solution 1 for ActuarialValuation.mackProjection_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:39:09.846201+00:00
-- url     : https://prove2.me/submissions/15bd365a-c0a8-4d03-a83d-46a908fcb328

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackProjection
open ActuarialValuation

theorem solution(f : ℝ) : mackProjection 0 f = 0 := by
  first
  | (simp [mackProjection]; done)
  | (norm_num [mackProjection]; done)
  | (unfold mackProjection; positivity)
  | (simp only [mackProjection]; positivity)
  | (unfold mackProjection; ring)
  | (unfold mackProjection; simp; done)
  | (unfold mackProjection; norm_num; done)
  | (simp [mackProjection]; ring)
  | (unfold mackProjection; split_ifs <;> simp_all <;> linarith)
  | (unfold mackProjection; nlinarith [sq_nonneg 0])
  | (simp_all [mackProjection]; done)
  | (unfold mackProjection; simp_all; done)
  | rfl
