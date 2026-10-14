-- Prove2me | solution 1 for ActuarialValuation.nhCauseBenefit_equal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:34:12.079679+00:00
-- url     : https://prove2.me/submissions/0bb60f29-6c0d-45e2-a7c8-767229120d35

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhCauseBenefit
open ActuarialValuation

theorem solution(p B : ℝ) : nhCauseBenefit p B B=B := by
  first
  | (simp [nhCauseBenefit]; done)
  | (norm_num [nhCauseBenefit]; done)
  | (unfold nhCauseBenefit; positivity)
  | (simp only [nhCauseBenefit]; positivity)
  | (unfold nhCauseBenefit; ring)
  | (unfold nhCauseBenefit; simp; done)
  | (unfold nhCauseBenefit; norm_num; done)
  | (simp [nhCauseBenefit]; ring)
  | (unfold nhCauseBenefit; split_ifs <;> simp_all <;> linarith)
  | (unfold nhCauseBenefit; nlinarith [sq_nonneg 0])
  | (simp_all [nhCauseBenefit]; done)
  | (unfold nhCauseBenefit; simp_all; done)
  | rfl
