-- Prove2me | solution 1 for ActuarialValuation.scrPairSquared_unit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:27:12.935768+00:00
-- url     : https://prove2.me/submissions/727cc502-a53f-45da-b684-53351b742f8a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_scrPairSquared
import Definitions.Def_actuarial_scrSumSquared
open ActuarialValuation

theorem solution(a b : ℝ) : scrPairSquared 1 a b = scrSumSquared a b := by
  unfold scrPairSquared scrSumSquared scrCovarianceTerm
  ring
