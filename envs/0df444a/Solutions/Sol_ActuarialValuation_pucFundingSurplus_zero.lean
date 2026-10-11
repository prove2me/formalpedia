-- Prove2me | solution 1 for ActuarialValuation.pucFundingSurplus_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:19:48.533921+00:00
-- url     : https://prove2.me/submissions/05468a2e-c9ab-46c2-aa54-520247e3cef9

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucFundingSurplus
open ActuarialValuation

theorem solution(a al : ℝ) : pucFundingSurplus a 0 1 al = a - al := by
  unfold pucFundingSurplus
  ring
