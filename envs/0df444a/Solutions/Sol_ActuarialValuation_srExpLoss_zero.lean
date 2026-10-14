-- Prove2me | solution 1 for ActuarialValuation.srExpLoss_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:17:34.577019+00:00
-- url     : https://prove2.me/submissions/59db16b4-6291-499b-9b36-407fd3dd6a67

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srExpLoss
open ActuarialValuation

theorem solution{Ω : Type*} (R c : ℝ) (W Y : ℕ → Ω → ℝ) (ω : Ω) : srExpLoss R c W Y 0 ω=1 := by
  first
  | (simp [srExpLoss, srNetLoss, srWaitingTotal, srClaimTotal]; done)
  | (norm_num [srExpLoss, srNetLoss, srWaitingTotal, srClaimTotal]; done)
  | (unfold srExpLoss srNetLoss srWaitingTotal srClaimTotal; positivity)
  | (simp only [srExpLoss, srNetLoss, srWaitingTotal, srClaimTotal]; positivity)
  | (unfold srExpLoss srNetLoss srWaitingTotal srClaimTotal; ring)
  | (unfold srExpLoss srNetLoss srWaitingTotal srClaimTotal; simp; done)
  | (unfold srExpLoss srNetLoss srWaitingTotal srClaimTotal; norm_num; done)
  | (simp [srExpLoss, srNetLoss, srWaitingTotal, srClaimTotal]; ring)
  | (unfold srExpLoss srNetLoss srWaitingTotal srClaimTotal; split_ifs <;> simp_all <;> linarith)
  | (unfold srExpLoss srNetLoss srWaitingTotal srClaimTotal; nlinarith [sq_nonneg 0])
  | (simp_all [srExpLoss, srNetLoss, srWaitingTotal, srClaimTotal]; done)
  | (unfold srExpLoss srNetLoss srWaitingTotal srClaimTotal; simp_all; done)
  | rfl
