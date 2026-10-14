-- Prove2me | solution 1 for ActuarialValuation.ruMean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:07:31.684998+00:00
-- url     : https://prove2.me/submissions/cbb07f1f-c0ac-4681-b539-c1d23ad31589

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruMean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (X : Fin m → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hX : ∀ ω, 0 ≤ X ω) :
    0 ≤ ruMean p X := by
  unfold ruMean
  apply Finset.sum_nonneg
  intro ω hω
  exact mul_nonneg (hp ω) (hX ω)
