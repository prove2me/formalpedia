-- Prove2me | solution 1 for ActuarialValuation.cxScore_zero_covariate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:59:16.183274+00:00
-- url     : https://prove2.me/submissions/3a5e9492-b065-4424-8261-d37fa287efc5

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

theorem solution {n : ℕ} (beta : ℝ) (events : Finset (Fin n)) (risks : Fin n → Finset (Fin n)) : cxScore beta events risks (fun _ => 0)=0 := by
  simp [cxScore, cxRiskMean, cxRiskWeighted]
