-- Prove2me | solution 1 for ActuarialValuation.crExpected_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:03:48.121057+00:00
-- url     : https://prove2.me/submissions/d0b4243b-254d-40c5-9c38-a17a9daf1432

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p X Y : Fin n→ℝ) (hp : ∀ i,0≤p i) (hXY : ∀ i,X i≤Y i) : crExpected p X≤crExpected p Y := by
  unfold crExpected
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hXY i) (hp i)
