-- Prove2me | solution 1 for ActuarialValuation.pvMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:01.508905+00:00
-- url     : https://prove2.me/submissions/3d5653df-6d16-4c73-b86f-b94de59c5247

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ pvMass p loss z := by
  unfold pvMass
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact hp i
  · exact le_refl _
