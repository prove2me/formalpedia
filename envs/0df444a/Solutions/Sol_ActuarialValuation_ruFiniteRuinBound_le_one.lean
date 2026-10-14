-- Prove2me | solution 1 for ActuarialValuation.ruFiniteRuinBound_le_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:31:55.658382+00:00
-- url     : https://prove2.me/submissions/bfe1b126-bb36-4bf9-b9da-7efc10229a71

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruFiniteRuinBound
open ActuarialValuation

theorem solution(R u : ℝ) (hR : 0≤R) (hu : 0≤u) : ruFiniteRuinBound R u ≤ 1 := by
  unfold ruFiniteRuinBound
  apply Real.exp_le_one_iff.mpr
  nlinarith [mul_nonneg hR hu]
