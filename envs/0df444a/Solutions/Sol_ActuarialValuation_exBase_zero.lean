-- Prove2me | solution 1 for ActuarialValuation.exBase_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:11:32.744982+00:00
-- url     : https://prove2.me/submissions/4793ceee-9d85-4ca2-8b17-9ca0374ef092

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exBase
open ActuarialValuation

theorem solution(xi sigma : ℝ) : exBase xi sigma 0=1 := by
  first
  | (simp [exBase]; done)
  | (norm_num [exBase]; done)
  | (unfold exBase; positivity)
  | (simp only [exBase]; positivity)
  | (unfold exBase; ring)
  | (unfold exBase; simp; done)
  | (unfold exBase; norm_num; done)
  | (simp [exBase]; ring)
  | (unfold exBase; split_ifs <;> simp_all <;> linarith)
  | (unfold exBase; nlinarith [sq_nonneg 0])
  | (simp_all [exBase]; done)
  | (unfold exBase; simp_all; done)
  | rfl
