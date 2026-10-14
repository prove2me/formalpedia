-- Prove2me | solution 1 for ActuarialValuation.cxPartialLikelihood_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:50:30.827278+00:00
-- url     : https://prove2.me/submissions/6b17f1e4-b31d-4dc1-a3f2-273c1b3e05d2

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

theorem solution {n : ℕ} (beta : ℝ) (events : Finset (Fin n)) (risks : Fin n → Finset (Fin n)) (z : Fin n → ℝ) : 0≤cxPartialLikelihood beta events risks z := by
  classical
  unfold cxPartialLikelihood
  induction events using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.prod_insert his]
      apply mul_nonneg
      · unfold cxEventShare
        apply div_nonneg
        · unfold cxRelativeRisk
          exact (Real.exp_pos _).le
        · unfold cxRiskDenom
          apply Finset.sum_nonneg
          intro j hj
          unfold cxRelativeRisk
          exact (Real.exp_pos _).le
      · exact ih
