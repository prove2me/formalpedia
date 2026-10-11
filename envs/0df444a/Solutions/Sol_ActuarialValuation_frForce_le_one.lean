-- Prove2me | solution 1 for ActuarialValuation.frForce_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:31:50.496979+00:00
-- url     : https://prove2.me/submissions/eb62ce9d-7866-46d0-b1b1-2c9b4ab5a6d1

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frForceSurvival
open ActuarialValuation

theorem solution(mu t : ℝ) (hm : 0 ≤ mu) (ht : 0 ≤ t) : frForceSurvival mu t ≤ 1 := by
  unfold frForceSurvival
  exact Real.exp_le_one_iff.2 (by nlinarith)
