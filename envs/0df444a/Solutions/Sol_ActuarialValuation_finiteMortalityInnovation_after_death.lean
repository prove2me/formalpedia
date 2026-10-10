-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityInnovation_after_death
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:52:13.706018+00:00
-- url     : https://prove2.me/submissions/026915e1-dbf6-4568-8cd0-c6b34fd16183

import Mathlib
import Definitions.Def_actuarial_finiteMortalityInnovation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (ω : Ω) (hK : K ω < t)
  :
  finiteMortalityInnovation w K t ω = 0 := by
  have hn : K ω ≠ t := by omega
  have hs : ¬ t ≤ K ω := by omega
  simp [finiteMortalityInnovation, hn, hs]
