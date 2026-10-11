-- Prove2me | solution 1 for ActuarialValuation.mackProjection_unit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:39:07.078304+00:00
-- url     : https://prove2.me/submissions/9189f92b-5ecf-4550-98dd-d2d3e41c9f69

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackProjection
open ActuarialValuation

theorem solution(c : ℝ) : mackProjection c 1 = c := by
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
