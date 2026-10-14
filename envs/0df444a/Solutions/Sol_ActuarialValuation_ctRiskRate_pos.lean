-- Prove2me | solution 1 for ActuarialValuation.ctRiskRate_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:42:38.61964+00:00
-- url     : https://prove2.me/submissions/949dcd4e-1404-4377-8f4d-f844cc20e42f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRiskRate
open ActuarialValuation

theorem solution(delta mu : ℝ) (hd : 0 < delta) (hm : 0 ≤ mu) : 0 < ctRiskRate delta mu := by
  first
  | (simp [ctRiskRate]; done)
  | (norm_num [ctRiskRate]; done)
  | (unfold ctRiskRate; positivity)
  | (simp only [ctRiskRate]; positivity)
  | (unfold ctRiskRate; ring)
  | (unfold ctRiskRate; simp; done)
  | (unfold ctRiskRate; norm_num; done)
  | (simp [ctRiskRate]; ring)
  | (unfold ctRiskRate; split_ifs <;> simp_all <;> linarith)
  | (unfold ctRiskRate; nlinarith [sq_nonneg 0])
  | (simp_all [ctRiskRate]; done)
  | (unfold ctRiskRate; simp_all; done)
  | rfl
