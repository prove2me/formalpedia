-- Prove2me | solution 1 for ActuarialValuation.gmRate_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:45:53.56369+00:00
-- url     : https://prove2.me/submissions/588ee0b8-7b90-43b9-b694-2c28f66f18d6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmRate
open ActuarialValuation

theorem solution(eta : ℝ) : 0<gmRate eta := by
  first
  | (simp [gmRate]; done)
  | (norm_num [gmRate]; done)
  | (unfold gmRate; positivity)
  | (simp only [gmRate]; positivity)
  | (unfold gmRate; ring)
  | (unfold gmRate; simp; done)
  | (unfold gmRate; norm_num; done)
  | (simp [gmRate]; ring)
  | (unfold gmRate; split_ifs <;> simp_all <;> linarith)
  | (unfold gmRate; nlinarith [sq_nonneg 0])
  | rfl
