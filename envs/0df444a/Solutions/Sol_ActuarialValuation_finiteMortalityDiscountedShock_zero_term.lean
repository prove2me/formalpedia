-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityDiscountedShock_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:25.512374+00:00
-- url     : https://prove2.me/submissions/5577a135-8b22-49a7-871d-48f81dbae451

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (ρ : ℕ → ℝ) (ω : Ω)
  :
  finiteMortalityDiscountedShock w K ρ 0 ω = 0 := by
  simp [finiteMortalityDiscountedShock]
