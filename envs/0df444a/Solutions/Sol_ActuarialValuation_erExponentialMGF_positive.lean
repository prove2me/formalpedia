-- Prove2me | solution 1 for ActuarialValuation.erExponentialMGF_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:52:25.962038+00:00
-- url     : https://prove2.me/submissions/da7aea67-96ba-47c4-a02b-e19609aa25eb

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_erExponentialMGF
open ActuarialValuation

theorem solution(beta r : ℝ) (hb : 0 < beta) (hr : r < beta) : 0 < erExponentialMGF beta r := by
  first
  | (simp [erExponentialMGF]; done)
  | (norm_num [erExponentialMGF]; done)
  | (unfold erExponentialMGF; positivity)
  | (simp only [erExponentialMGF]; positivity)
  | (unfold erExponentialMGF; ring)
  | (unfold erExponentialMGF; simp; done)
  | (unfold erExponentialMGF; norm_num; done)
  | (simp [erExponentialMGF]; ring)
  | (unfold erExponentialMGF; split_ifs <;> simp_all <;> linarith)
  | (unfold erExponentialMGF; nlinarith [sq_nonneg 0])
  | (simp_all [erExponentialMGF]; done)
  | (unfold erExponentialMGF; simp_all; done)
  | rfl
