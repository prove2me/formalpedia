-- Prove2me | solution 1 for ActuarialValuation.crRisk_mixture_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:08:39.356692+00:00
-- url     : https://prove2.me/submissions/c2141862-df4d-4a76-b818-477c6bdbdee8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crMixWeights
import Definitions.Def_actuarial_crScenarioRisk

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) (mix : ℝ) (hl0 : 0≤mix) (hl1 : mix≤1) : crExpected (crMixWeights p q mix) X ≤ crScenarioRisk p q X := by
  have hm :
      crExpected (crMixWeights p q mix) X =
      mix * crExpected p X + (1-mix)*crExpected q X := by
    unfold crExpected crMixWeights
    calc
      (∑ i : Fin n, (mix*p i+(1-mix)*q i)*X i) =
        (∑ i : Fin n, mix*(p i*X i)) +
        (∑ i : Fin n, (1-mix)*(q i*X i)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ = mix*(∑ i : Fin n, p i*X i) +
            (1-mix)*(∑ i : Fin n, q i*X i) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  rw [hm]
  unfold crScenarioRisk
  have h1 := mul_le_mul_of_nonneg_left
    (le_max_left (crExpected p X) (crExpected q X)) hl0
  have h2 := mul_le_mul_of_nonneg_left
    (le_max_right (crExpected p X) (crExpected q X)) (sub_nonneg.mpr hl1)
  linarith
