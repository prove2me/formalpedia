-- Prove2me | solution 1 for ActuarialValuation.bdForwardDiscount_issue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:06.952212+00:00
-- url     : https://prove2.me/submissions/2789055e-1906-43f1-abac-17b849e93d13

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (t : ℕ) (h0 : D 0 = 1) : bdForwardDiscount D 0 t = D t := by
  simp [bdForwardDiscount, h0]
