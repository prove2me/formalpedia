-- Prove2me | solution 1 for ActuarialValuation.scrCorrelationGap_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:23:03.39767+00:00
-- url     : https://prove2.me/submissions/c306b39d-e3e5-40cc-abf1-74e4d5045522

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrCorrelationGap
open ActuarialValuation

theorem solution: scrCorrelationGap 1 = 0 := by
  first
  | (simp [scrCorrelationGap]; done)
  | (norm_num [scrCorrelationGap]; done)
  | (unfold scrCorrelationGap; positivity)
  | (simp only [scrCorrelationGap]; positivity)
  | (unfold scrCorrelationGap; ring)
  | (unfold scrCorrelationGap; simp; done)
  | (unfold scrCorrelationGap; norm_num; done)
  | (simp [scrCorrelationGap]; ring)
  | (unfold scrCorrelationGap; split_ifs <;> simp_all <;> linarith)
  | (unfold scrCorrelationGap; nlinarith [sq_nonneg 0])
  | (simp_all [scrCorrelationGap]; done)
  | (unfold scrCorrelationGap; simp_all; done)
  | rfl
