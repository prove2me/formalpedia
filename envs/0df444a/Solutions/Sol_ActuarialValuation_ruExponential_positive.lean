-- Prove2me | solution 1 for ActuarialValuation.ruExponential_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:47:48.029259+00:00
-- url     : https://prove2.me/submissions/969ba5aa-8a5c-49df-82f2-173a48462f4a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExponential
open ActuarialValuation

theorem solution(R capital : ℝ) : 0 < ruExponential R capital := by
  unfold ruExponential
  exact Real.exp_pos _
