-- Prove2me | solution 1 for ActuarialValuation.lcRate_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:05:32.318079+00:00
-- url     : https://prove2.me/submissions/cb255eed-3bb7-41b3-9d61-3d7e3bbd64bf

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcRate
open ActuarialValuation

theorem solution(a b k : ℝ) : 0 < lcRate a b k := by
  first
  | (simp [lcRate, lcLogRate]; done)
  | (norm_num [lcRate, lcLogRate]; done)
  | (unfold lcRate lcLogRate; positivity)
  | (simp only [lcRate, lcLogRate]; positivity)
  | (unfold lcRate lcLogRate; ring)
  | (unfold lcRate lcLogRate; simp; done)
  | (unfold lcRate lcLogRate; norm_num; done)
  | (simp [lcRate, lcLogRate]; ring)
  | (unfold lcRate lcLogRate; split_ifs <;> simp_all <;> linarith)
  | (unfold lcRate lcLogRate; nlinarith [sq_nonneg 0])
  | (simp_all [lcRate, lcLogRate]; done)
  | (unfold lcRate lcLogRate; simp_all; done)
  | rfl
