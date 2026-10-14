-- Prove2me | solution 1 for ActuarialValuation.cxRiskDenom_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:26:36.639292+00:00
-- url     : https://prove2.me/submissions/a388c1e0-b303-4028-ba4f-e1e48cd48e6c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskDenom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (z : Fin n → ℝ) : cxRiskDenom beta ∅ z=0 := by
  simp [cxRiskDenom]
