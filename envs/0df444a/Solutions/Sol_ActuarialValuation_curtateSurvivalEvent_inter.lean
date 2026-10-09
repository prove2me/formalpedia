-- Prove2me | solution 1 for ActuarialValuation.curtateSurvivalEvent_inter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:25:40.068895+00:00
-- url     : https://prove2.me/submissions/12349539-f284-48dd-a746-55ff4c8f6386

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} (K : Ω → ℕ) (i j : ℕ)
    :
    curtateSurvivalEvent K i ∩ curtateSurvivalEvent K j = curtateSurvivalEvent K (max i j) := by
  ext ω
  change (i ≤ K ω ∧ j ≤ K ω) ↔ max i j ≤ K ω
  exact max_le_iff.symm
