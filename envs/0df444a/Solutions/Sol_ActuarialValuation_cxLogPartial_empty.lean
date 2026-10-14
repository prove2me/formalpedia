-- Prove2me | solution 1 for ActuarialValuation.cxLogPartial_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:32:21.628829+00:00
-- url     : https://prove2.me/submissions/79ac5741-7269-44b8-93ee-c85c77f76bc0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxLogPartial

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (risks : Fin n → Finset (Fin n)) (z : Fin n → ℝ) : cxLogPartial beta ∅ risks z=0 := by
  simp [cxLogPartial]
