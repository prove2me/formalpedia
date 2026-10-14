-- Prove2me | solution 1 for ActuarialValuation.srNetLoss_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:27:09.115517+00:00
-- url     : https://prove2.me/submissions/c346ee3a-30df-49a3-bf80-16169c72e9f5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srNetLoss
open ActuarialValuation

theorem solution{Ω : Type*} (c : ℝ) (W Y : ℕ → Ω → ℝ) (ω : Ω) : srNetLoss c W Y 0 ω=0 := by
  first
  | (simp [srNetLoss, srWaitingTotal, srClaimTotal]; done)
  | (norm_num [srNetLoss, srWaitingTotal, srClaimTotal]; done)
  | (unfold srNetLoss srWaitingTotal srClaimTotal; positivity)
  | (simp only [srNetLoss, srWaitingTotal, srClaimTotal]; positivity)
  | (unfold srNetLoss srWaitingTotal srClaimTotal; ring)
  | (unfold srNetLoss srWaitingTotal srClaimTotal; simp; done)
  | (unfold srNetLoss srWaitingTotal srClaimTotal; norm_num; done)
  | (simp [srNetLoss, srWaitingTotal, srClaimTotal]; ring)
  | (unfold srNetLoss srWaitingTotal srClaimTotal; split_ifs <;> simp_all <;> linarith)
  | (unfold srNetLoss srWaitingTotal srClaimTotal; nlinarith [sq_nonneg 0])
  | (simp_all [srNetLoss, srWaitingTotal, srClaimTotal]; done)
  | (unfold srNetLoss srWaitingTotal srClaimTotal; simp_all; done)
  | rfl
