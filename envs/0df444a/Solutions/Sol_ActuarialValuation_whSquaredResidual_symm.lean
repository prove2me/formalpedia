-- Prove2me | solution 1 for ActuarialValuation.whSquaredResidual_symm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:37:08.688483+00:00
-- url     : https://prove2.me/submissions/00221ae7-bd17-441a-bea4-c207ba4e740a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSquaredResidual
open ActuarialValuation

theorem solution(g q : ℝ) : whSquaredResidual g q = whSquaredResidual q g := by
  unfold whSquaredResidual whRateResidual
  ring
