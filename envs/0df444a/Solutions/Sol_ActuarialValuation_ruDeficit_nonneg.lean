-- Prove2me | solution 1 for ActuarialValuation.ruDeficit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:04:05.838+00:00
-- url     : https://prove2.me/submissions/d439b22d-21ec-4695-8f42-b2ad2cf8862c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinDeficit
open ActuarialValuation

theorem solution(capital : ℝ) : 0≤ruRuinDeficit capital := by
  first
  | (simp [ruRuinDeficit]; done)
  | (norm_num [ruRuinDeficit]; done)
  | (unfold ruRuinDeficit; positivity)
  | (simp only [ruRuinDeficit]; positivity)
  | (unfold ruRuinDeficit; ring)
  | (unfold ruRuinDeficit; simp; done)
  | (unfold ruRuinDeficit; norm_num; done)
  | (simp [ruRuinDeficit]; ring)
  | (unfold ruRuinDeficit; split_ifs <;> simp_all <;> linarith)
  | (unfold ruRuinDeficit; nlinarith [sq_nonneg 0])
  | (simp_all [ruRuinDeficit]; done)
  | (unfold ruRuinDeficit; simp_all; done)
  | rfl
