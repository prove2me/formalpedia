-- Prove2me | solution 1 for ActuarialValuation.bdStatePV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:02:04.939985+00:00
-- url     : https://prove2.me/submissions/a508afb7-f5bd-472d-b523-4ee5ae63caa8

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p discount X : Fin m → ℝ) (hp : ∀ ω,0≤p ω) (hd : ∀ ω,0≤discount ω) (hx : ∀ ω,0≤X ω) : 0≤bdStatePV p discount X := by
  unfold bdStatePV
  apply Finset.sum_nonneg
  intro ω hω
  exact mul_nonneg (mul_nonneg (hp ω) (hd ω)) (hx ω)
