-- Prove2me | solution 1 for ActuarialValuation.crExpected_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:03:38.18998+00:00
-- url     : https://prove2.me/submissions/b896f445-2f89-40f4-bb94-52467e11273c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X : Fin n→ℝ) (hp : ∀ i,0≤p i) (hX : ∀ i,0≤X i) : 0≤crExpected p X := by
  unfold crExpected
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hp i) (hX i)
