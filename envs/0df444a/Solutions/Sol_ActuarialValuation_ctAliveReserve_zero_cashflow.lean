-- Prove2me | solution 1 for ActuarialValuation.ctAliveReserve_zero_cashflow
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:19:53.95932+00:00
-- url     : https://prove2.me/submissions/961a9f1f-d9d9-42d3-9f92-ba97405b17be

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctAliveReserve
open ActuarialValuation

theorem solution(delta mu maturity t : ℝ) : ctAliveReserve delta mu 0 0 maturity t = 0 := by
  first
  | (simp [ctAliveReserve, ctRiskRate, ctInsuranceFlow]; done)
  | (norm_num [ctAliveReserve, ctRiskRate, ctInsuranceFlow]; done)
  | (unfold ctAliveReserve ctRiskRate ctInsuranceFlow; positivity)
  | (simp only [ctAliveReserve, ctRiskRate, ctInsuranceFlow]; positivity)
  | (unfold ctAliveReserve ctRiskRate ctInsuranceFlow; ring)
  | (unfold ctAliveReserve ctRiskRate ctInsuranceFlow; simp; done)
  | (unfold ctAliveReserve ctRiskRate ctInsuranceFlow; norm_num; done)
  | (simp [ctAliveReserve, ctRiskRate, ctInsuranceFlow]; ring)
  | (unfold ctAliveReserve ctRiskRate ctInsuranceFlow; split_ifs <;> simp_all <;> linarith)
  | (unfold ctAliveReserve ctRiskRate ctInsuranceFlow; nlinarith [sq_nonneg 0])
  | (simp_all [ctAliveReserve, ctRiskRate, ctInsuranceFlow]; done)
  | (unfold ctAliveReserve ctRiskRate ctInsuranceFlow; simp_all; done)
  | rfl
