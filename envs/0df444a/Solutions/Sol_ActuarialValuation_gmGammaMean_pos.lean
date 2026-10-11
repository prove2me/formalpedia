-- Prove2me | solution 1 for ActuarialValuation.gmGammaMean_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T19:53:29.055855+00:00
-- url     : https://prove2.me/submissions/163ac2bc-b807-4725-88f1-31b1cc45a9a8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmGammaMean
open ActuarialValuation

theorem solution(eta : ℝ) : 0<gmGammaMean eta := by
  first
  | (simp [gmGammaMean]; done)
  | (norm_num [gmGammaMean]; done)
  | (unfold gmGammaMean; positivity)
  | (simp only [gmGammaMean]; positivity)
  | (unfold gmGammaMean; ring)
  | (unfold gmGammaMean; simp; done)
  | (unfold gmGammaMean; norm_num; done)
  | (simp [gmGammaMean]; ring)
  | (unfold gmGammaMean; split_ifs <;> simp_all <;> linarith)
  | (unfold gmGammaMean; nlinarith [sq_nonneg 0])
  | rfl
