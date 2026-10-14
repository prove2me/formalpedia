-- Prove2me | solution 1 for ActuarialValuation.siGrossMean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:13:39.911131+00:00
-- url     : https://prove2.me/submissions/d21dbc2c-dad2-4609-936d-df7f38b73f57

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrossMean

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (r : Fin m → ℝ) (hp : ∀ j, 0≤p j) (hr : ∀ j, -1≤r j) : 0≤siGrossMean p r := by
  unfold siGrossMean siMean
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg (hp j)
  unfold siGrowth
  linarith [hr j]
