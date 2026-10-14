-- Prove2me | solution 1 for ActuarialValuation.exHazard_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:32:57.934697+00:00
-- url     : https://prove2.me/submissions/6d28eba3-15e2-498f-8ca9-7e64ac3cd035

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exHazard
open ActuarialValuation

theorem solution(xi sigma x : ℝ) (hxi : 0 ≤ xi) (hs : 0 < sigma) (hx : 0 ≤ x) : 0 < exHazard xi sigma x := by
  first
  | (simp [exHazard]; done)
  | (norm_num [exHazard]; done)
  | (unfold exHazard; positivity)
  | (simp only [exHazard]; positivity)
  | (unfold exHazard; ring)
  | (unfold exHazard; simp; done)
  | (unfold exHazard; norm_num; done)
  | (simp [exHazard]; ring)
  | (unfold exHazard; split_ifs <;> simp_all <;> linarith)
  | (unfold exHazard; nlinarith [sq_nonneg 0])
  | (simp_all [exHazard]; done)
  | (unfold exHazard; simp_all; done)
  | rfl
