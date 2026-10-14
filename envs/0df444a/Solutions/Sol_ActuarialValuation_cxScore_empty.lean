-- Prove2me | solution 1 for ActuarialValuation.cxScore_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:33:08.411743+00:00
-- url     : https://prove2.me/submissions/2f302488-f41d-4780-8984-21ef3ba5218f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxScore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (beta : ℝ) (risks : Fin n → Finset (Fin n)) (z : Fin n → ℝ) : cxScore beta ∅ risks z=0 := by
  simp [cxScore]
