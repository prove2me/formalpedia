-- Prove2me | solution 1 for ActuarialValuation.panjerPoissonZero_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:23:06.306243+00:00
-- url     : https://prove2.me/submissions/2f1a51a4-432d-4c4a-bcf8-142a5e1769f1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_panjerPoissonZero
open ActuarialValuation

theorem solution: panjerPoissonZero 0 = 1 := by
  first
  | (simp [panjerPoissonZero]; done)
  | (norm_num [panjerPoissonZero]; done)
  | (unfold panjerPoissonZero; positivity)
  | (simp only [panjerPoissonZero]; positivity)
  | (unfold panjerPoissonZero; ring)
  | (unfold panjerPoissonZero; simp; done)
  | (unfold panjerPoissonZero; norm_num; done)
  | (simp [panjerPoissonZero]; ring)
  | (unfold panjerPoissonZero; split_ifs <;> simp_all <;> linarith)
  | (unfold panjerPoissonZero; nlinarith [sq_nonneg 0])
  | (simp_all [panjerPoissonZero]; done)
  | (unfold panjerPoissonZero; simp_all; done)
  | rfl
