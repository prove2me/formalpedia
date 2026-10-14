-- Prove2me | solution 1 for ActuarialValuation.msEndStateBenefit_transition_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:19:40.862876+00:00
-- url     : https://prove2.me/submissions/97963097-cdfe-4b7a-8619-31922d7c168e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msTransitionBenefit
import Definitions.Def_actuarial_msEndStateBenefit

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : Fin 3 → ℝ) (T : Fin 3 → Fin 3 → ℝ) (B : Fin 3 → ℝ) (v : ℝ) : msEndStateBenefit p T B v = msTransitionBenefit p T (fun _ j => B j) v := by
  unfold msEndStateBenefit msExpectedBenefit msStep msTransitionBenefit
  congr 1
  calc
    (∑ j : Fin 3, (∑ i : Fin 3, p i * T i j) * B j) =
        (∑ j : Fin 3, ∑ i : Fin 3, (p i * T i j) * B j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, p i * T i j * B j := by
          rw [Finset.sum_comm]
