-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityDeathMass_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:51:54.803986+00:00
-- url     : https://prove2.me/submissions/6fb30ff8-a09c-4688-9d03-8f469f30f7fb

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  :
  0 ≤ finiteMortalityDeathMass w K t := by
  unfold finiteMortalityDeathMass
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_refl 0
