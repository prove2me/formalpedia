-- Prove2me | solution 1 for ActuarialValuation.finiteHorizonBellmanValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:17.548287+00:00
-- url     : https://prove2.me/submissions/3e70f0db-fe07-49b8-a78f-0b19d31874f9

import Mathlib
import Definitions.Def_actuarial_finiteHorizonBellmanValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (s : S)
  :
  finiteHorizonBellmanValue P reward v terminal 0 s = terminal s := rfl
