-- Prove2me | solution 1 for ActuarialValuation.ctEuler_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:30:02.498261+00:00
-- url     : https://prove2.me/submissions/b5f521e3-290c-4f46-9615-ae26d98642ef

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctEuler
open ActuarialValuation

theorem solution(r : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ctEuler r 0 i j = (if i=j then 1 else 0) := by
  first
  | (simp [ctEuler, ctGenerator, ctRateOut]; done)
  | (norm_num [ctEuler, ctGenerator, ctRateOut]; done)
  | (unfold ctEuler ctGenerator ctRateOut; positivity)
  | (simp only [ctEuler, ctGenerator, ctRateOut]; positivity)
  | (unfold ctEuler ctGenerator ctRateOut; ring)
  | (unfold ctEuler ctGenerator ctRateOut; simp; done)
  | (unfold ctEuler ctGenerator ctRateOut; norm_num; done)
  | (simp [ctEuler, ctGenerator, ctRateOut]; ring)
  | (unfold ctEuler ctGenerator ctRateOut; split_ifs <;> simp_all <;> linarith)
  | (unfold ctEuler ctGenerator ctRateOut; nlinarith [sq_nonneg 0])
  | (simp_all [ctEuler, ctGenerator, ctRateOut]; done)
  | (unfold ctEuler ctGenerator ctRateOut; simp_all; done)
  | rfl
