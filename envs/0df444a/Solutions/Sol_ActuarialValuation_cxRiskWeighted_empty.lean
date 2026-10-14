-- Prove2me | solution 1 for ActuarialValuation.cxRiskWeighted_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:29:52.640234+00:00
-- url     : https://prove2.me/submissions/d5dba479-45a3-4740-84f3-8f766790bc40

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskWeighted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (z : Fin n → ℝ) : cxRiskWeighted beta ∅ z=0 := by
  simp [cxRiskWeighted]
