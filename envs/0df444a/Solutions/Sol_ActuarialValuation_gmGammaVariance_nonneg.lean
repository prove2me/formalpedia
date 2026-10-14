-- Prove2me | solution 1 for ActuarialValuation.gmGammaVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:39:41.524567+00:00
-- url     : https://prove2.me/submissions/1c3a7d78-39e5-4c78-9ecb-100f9a9127f5

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmGammaVariance
open ActuarialValuation

theorem solution(mean shape : ℝ) (hs : 0 < shape) : 0≤gmGammaVariance mean shape := by
  first
  | (simp [gmGammaVariance]; done)
  | (norm_num [gmGammaVariance]; done)
  | (unfold gmGammaVariance; positivity)
  | (simp only [gmGammaVariance]; positivity)
  | (unfold gmGammaVariance; ring)
  | (unfold gmGammaVariance; simp; done)
  | (unfold gmGammaVariance; norm_num; done)
  | (simp [gmGammaVariance]; ring)
  | (unfold gmGammaVariance; split_ifs <;> simp_all <;> linarith)
  | (unfold gmGammaVariance; nlinarith [sq_nonneg 0])
  | (simp_all [gmGammaVariance]; done)
  | (unfold gmGammaVariance; simp_all; done)
  | rfl
