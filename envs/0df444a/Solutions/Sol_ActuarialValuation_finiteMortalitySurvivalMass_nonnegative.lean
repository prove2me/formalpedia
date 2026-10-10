-- Prove2me | solution 1 for ActuarialValuation.finiteMortalitySurvivalMass_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:51:49.317411+00:00
-- url     : https://prove2.me/submissions/0a992a96-10fb-4b83-a3be-8ae97cccbf36

import Mathlib
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  :
  0 ≤ finiteMortalitySurvivalMass w K t := by
  unfold finiteMortalitySurvivalMass
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_refl 0
