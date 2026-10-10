-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityInnovation_product_later
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:02:40.637738+00:00
-- url     : https://prove2.me/submissions/81a00623-7fb9-4173-87f2-984c2c6d7587

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalityInnovation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (i j : ℕ) (ω : Ω) (hij : i < j)
  :
  finiteMortalityInnovation w K i ω * finiteMortalityInnovation w K j ω =
    -(finiteMortalityDeathRate w K i) * finiteMortalityInnovation w K j ω := by
  by_cases hj : K ω < j
  · have hnj : K ω ≠ j := by omega
    have hnot : ¬ j ≤ K ω := by omega
    simp [finiteMortalityInnovation, hnj, hnot]
  · have hni : K ω ≠ i := by omega
    have hle : i ≤ K ω := by omega
    simp [finiteMortalityInnovation, hni, hle]
