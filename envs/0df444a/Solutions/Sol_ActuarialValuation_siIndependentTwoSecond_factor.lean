-- Prove2me | solution 1 for ActuarialValuation.siIndependentTwoSecond_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:13:30.106668+00:00
-- url     : https://prove2.me/submissions/da0b996a-ecdc-45cd-bf42-46bf2aed7dc2

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrossSecond
import Definitions.Def_actuarial_siIndependentTwoSecond

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m n : ℕ} (p : Fin m → ℝ) (q : Fin n → ℝ) (r : Fin m → ℝ) (s : Fin n → ℝ) : siIndependentTwoSecond p q r s=siGrossSecond p r*siGrossSecond q s := by
  unfold siIndependentTwoSecond siGrossSecond siSecond
  calc
    (∑ a : Fin m, ∑ b : Fin n,
      (p a*q b)*(siGrowth (r a)*siGrowth (s b))^2) =
        ∑ a : Fin m, (p a*(siGrowth (r a))^2) *
           (∑ b : Fin n, q b*(siGrowth (s b))^2) := by
             apply Finset.sum_congr rfl
             intro a ha
             rw [Finset.mul_sum]
             apply Finset.sum_congr rfl
             intro b hb
             ring
    _ = (∑ a : Fin m, p a*(siGrowth (r a))^2) *
        (∑ b : Fin n, q b*(siGrowth (s b))^2) := by
           rw [Finset.sum_mul]
