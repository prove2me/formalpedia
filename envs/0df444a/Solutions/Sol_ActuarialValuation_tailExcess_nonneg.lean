-- Prove2me | solution 1 for ActuarialValuation.tailExcess_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:15:51.483006+00:00
-- url     : https://prove2.me/submissions/b5ed2d7a-4c8f-420e-9a61-d54166de10fe

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailExcess
open ActuarialValuation

theorem solution(x t : ℝ) : 0 ≤ tailExcess x t := by
  first
  | (simp [tailExcess]; done)
  | (norm_num [tailExcess]; done)
  | (unfold tailExcess; positivity)
  | (simp only [tailExcess]; positivity)
  | (unfold tailExcess; ring)
  | (unfold tailExcess; simp; done)
  | (unfold tailExcess; norm_num; done)
  | (simp [tailExcess]; ring)
  | (unfold tailExcess; split_ifs <;> simp_all <;> linarith)
  | (unfold tailExcess; nlinarith [sq_nonneg 0])
  | (simp_all [tailExcess]; done)
  | (unfold tailExcess; simp_all; done)
  | rfl
