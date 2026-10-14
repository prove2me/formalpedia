-- Prove2me | solution 1 for ActuarialValuation.gmRelativity_reflexive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:40:51.532678+00:00
-- url     : https://prove2.me/submissions/4faef65c-03ee-4b4b-a196-1e1de281e20e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmRelativity
open ActuarialValuation

theorem solution(eta : ℝ) : gmRelativity eta eta=1 := by
  first
  | (simp [gmRelativity]; done)
  | (norm_num [gmRelativity]; done)
  | (unfold gmRelativity; positivity)
  | (simp only [gmRelativity]; positivity)
  | (unfold gmRelativity; ring)
  | (unfold gmRelativity; simp; done)
  | (unfold gmRelativity; norm_num; done)
  | (simp [gmRelativity]; ring)
  | (unfold gmRelativity; split_ifs <;> simp_all <;> linarith)
  | (unfold gmRelativity; nlinarith [sq_nonneg 0])
  | (simp_all [gmRelativity]; done)
  | (unfold gmRelativity; simp_all; done)
  | rfl
