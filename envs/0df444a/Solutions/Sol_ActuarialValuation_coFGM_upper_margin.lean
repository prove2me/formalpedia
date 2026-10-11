-- Prove2me | solution 1 for ActuarialValuation.coFGM_upper_margin
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:35:09.473062+00:00
-- url     : https://prove2.me/submissions/1bce4067-df92-451d-9e08-9737507d846f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coFGM
open ActuarialValuation

theorem solution(theta u : ℝ) : coFGM theta u 1=u := by
  first
  | (simp [coFGM]; done)
  | (norm_num [coFGM]; done)
  | (unfold coFGM; positivity)
  | (simp only [coFGM]; positivity)
  | (unfold coFGM; ring)
  | (unfold coFGM; simp; done)
  | (unfold coFGM; norm_num; done)
  | (simp [coFGM]; ring)
  | (unfold coFGM; split_ifs <;> simp_all <;> linarith)
  | (unfold coFGM; nlinarith [sq_nonneg 0])
  | (simp_all [coFGM]; done)
  | (unfold coFGM; simp_all; done)
  | rfl
