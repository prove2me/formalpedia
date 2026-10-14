-- Prove2me | solution 1 for ActuarialValuation.exBase_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:49:56.830907+00:00
-- url     : https://prove2.me/submissions/fa23ecfe-b759-44e1-97c9-7408aa53e85c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exBase
open ActuarialValuation

theorem solution(xi sigma x : ℝ) (hx : 0 ≤ x) (hxi : 0 ≤ xi) (hs : 0 < sigma) : 0 < exBase xi sigma x := by
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
