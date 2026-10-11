-- Prove2me | solution 1 for ActuarialValuation.ctAlive_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:02:04.83422+00:00
-- url     : https://prove2.me/submissions/a1e3ec5b-bdb5-4094-b94e-3c199bf52215

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctAlive
open ActuarialValuation

theorem solution(mu t : ℝ) : 0 < ctAlive mu t := by
  first
  | (simp [ctAlive]; done)
  | (norm_num [ctAlive]; done)
  | (unfold ctAlive; positivity)
  | (simp only [ctAlive]; positivity)
  | (unfold ctAlive; ring)
  | (unfold ctAlive; simp; done)
  | (unfold ctAlive; norm_num; done)
  | (simp [ctAlive]; ring)
  | (unfold ctAlive; split_ifs <;> simp_all <;> linarith)
  | (unfold ctAlive; nlinarith [sq_nonneg 0])
  | rfl
