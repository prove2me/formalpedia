-- Prove2me | solution 1 for ActuarialValuation.ruFiniteRuinBound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:51:20.486118+00:00
-- url     : https://prove2.me/submissions/927ee9dd-1ea6-4f75-88dd-8e6756e72512

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruFiniteRuinBound
open ActuarialValuation

theorem solution(R u : ℝ) : 0 < ruFiniteRuinBound R u := by
  unfold ruFiniteRuinBound
  exact Real.exp_pos _
