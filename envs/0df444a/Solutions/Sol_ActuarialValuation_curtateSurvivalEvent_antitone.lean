-- Prove2me | solution 1 for ActuarialValuation.curtateSurvivalEvent_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:25:12.839543+00:00
-- url     : https://prove2.me/submissions/74cebc6d-6883-4abb-8942-c2e9ba2ca525

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation
open MeasureTheory

theorem solution {Ω : Type*} (K : Ω → ℕ) (i j : ℕ) (hij : i ≤ j)
    :
    curtateSurvivalEvent K j ⊆ curtateSurvivalEvent K i := by
  intro ω hw
  change j ≤ K ω at hw
  change i ≤ K ω
  exact le_trans hij hw
