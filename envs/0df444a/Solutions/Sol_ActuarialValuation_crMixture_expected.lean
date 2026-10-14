-- Prove2me | solution 1 for ActuarialValuation.crMixture_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:07:08.550499+00:00
-- url     : https://prove2.me/submissions/11c58fcc-e016-4044-886a-a230b1c2b526

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crMixWeights

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) (mix : ℝ) : crExpected (crMixWeights p q mix) X = mix*crExpected p X+(1-mix)*crExpected q X := by
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
