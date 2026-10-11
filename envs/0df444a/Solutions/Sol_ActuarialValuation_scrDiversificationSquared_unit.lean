-- Prove2me | solution 1 for ActuarialValuation.scrDiversificationSquared_unit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:22:48.726473+00:00
-- url     : https://prove2.me/submissions/3f43048a-d672-404d-94f9-fe0297af86af

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrDiversificationSquared
open ActuarialValuation

theorem solution(a b : ℝ) : scrDiversificationSquared 1 a b = 0 := by
  unfold scrDiversificationSquared scrSumSquared scrPairSquared scrCovarianceTerm
  ring
