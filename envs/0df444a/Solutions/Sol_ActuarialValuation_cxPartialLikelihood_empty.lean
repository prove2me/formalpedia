-- Prove2me | solution 1 for ActuarialValuation.cxPartialLikelihood_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:31:36.266133+00:00
-- url     : https://prove2.me/submissions/8b9a15b0-91b9-40a7-b4fb-b02e0a9ac614

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxPartialLikelihood

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (risks : Fin n → Finset (Fin n)) (z : Fin n → ℝ) : cxPartialLikelihood beta ∅ risks z=1 := by
  simp [cxPartialLikelihood]
