-- Prove2me | solution 1 for ActuarialValuation.pgSeverityMean_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:48:58.642416+00:00
-- url     : https://prove2.me/submissions/7c605544-da85-45c4-b1d8-335b421b41c8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgSeverityMean
open ActuarialValuation

theorem solution(f : ℕ → ℝ) : pgSeverityMean f 0=0 := by
  first
  | (simp [pgSeverityMean]; done)
  | (norm_num [pgSeverityMean]; done)
  | (unfold pgSeverityMean; positivity)
  | (simp only [pgSeverityMean]; positivity)
  | (unfold pgSeverityMean; ring)
  | (unfold pgSeverityMean; simp; done)
  | (unfold pgSeverityMean; norm_num; done)
  | (simp [pgSeverityMean]; ring)
  | (unfold pgSeverityMean; split_ifs <;> simp_all <;> linarith)
  | (unfold pgSeverityMean; nlinarith [sq_nonneg 0])
  | (simp_all [pgSeverityMean]; done)
  | (unfold pgSeverityMean; simp_all; done)
  | rfl
