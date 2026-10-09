-- Prove2me | solution 1 for ActuarialValuation.deathYearIndicators_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T19:20:54.247351+00:00
-- url     : https://prove2.me/submissions/947ff492-2678-454d-be3a-78a1c594d493

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} (K : Ω → ℕ)
    (i j : ℕ) (hij : i ≠ j) (ω : Ω)
    :
    (deathYearEvent K i).indicator (fun _ : Ω => (1 : ℝ)) ω *
      (deathYearEvent K j).indicator (fun _ : Ω => (1 : ℝ)) ω = 0 := by
  by_cases hi : ω ∈ deathYearEvent K i
  · have hj : ω ∉ deathYearEvent K j := by
      intro hh
      have heqi : K ω = i := hi
      have heqj : K ω = j := hh
      exact hij (heqi.symm.trans heqj)
    simp [Set.indicator, hi, hj]
  · simp [Set.indicator, hi]
