-- Prove2me | solution 1 for ActuarialValuation.cxRiskDenom_insert
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:38:03.83598+00:00
-- url     : https://prove2.me/submissions/353f3263-f660-46df-bec2-174357ababea

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRelativeRisk
import Definitions.Def_actuarial_cxRiskDenom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (risk : Finset (Fin n)) (i : Fin n) (z : Fin n → ℝ) (hi : i ∉ risk) : cxRiskDenom beta (insert i risk) z=cxRelativeRisk beta (z i)+cxRiskDenom beta risk z := by
  simp [cxRiskDenom, hi]
