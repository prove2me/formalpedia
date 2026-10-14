-- Prove2me | solution 1 for ActuarialValuation.bdForwardDiscount_same
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:17.787958+00:00
-- url     : https://prove2.me/submissions/9d7c743d-6ee0-4395-8c53-d7d9e60940da

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (t : ℕ) (h : D t ≠ 0) : bdForwardDiscount D t t = 1 := by
  unfold bdForwardDiscount
  exact div_self h
