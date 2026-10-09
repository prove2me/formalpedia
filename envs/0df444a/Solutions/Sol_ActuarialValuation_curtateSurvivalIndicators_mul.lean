-- Prove2me | solution 1 for ActuarialValuation.curtateSurvivalIndicators_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:27:05.239173+00:00
-- url     : https://prove2.me/submissions/81644a4f-5e70-4961-8bb5-2995070eaedd

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} (K : Ω → ℕ) (i j : ℕ) (ω : Ω)
    :
    (curtateSurvivalEvent K i).indicator (fun _ : Ω => (1 : ℝ)) ω *
      (curtateSurvivalEvent K j).indicator (fun _ : Ω => (1 : ℝ)) ω =
      (curtateSurvivalEvent K (max i j)).indicator (fun _ : Ω => (1 : ℝ)) ω := by
  classical
  by_cases hi : i ≤ K ω
  · by_cases hj : j ≤ K ω
    · have hm : max i j ≤ K ω := max_le hi hj
      simp [curtateSurvivalEvent, Set.indicator, hi, hj, hm]
    · have hm : ¬ max i j ≤ K ω := by
        intro h
        exact hj (le_trans (le_max_right i j) h)
      simp [curtateSurvivalEvent, Set.indicator, hi, hj, hm]
  · have hm : ¬ max i j ≤ K ω := by
      intro h
      exact hi (le_trans (le_max_left i j) h)
    simp [curtateSurvivalEvent, Set.indicator, hi, hm]
