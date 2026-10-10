-- Prove2me | solution 1 for ActuarialValuation.finiteHorizonPolicyValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:17.795157+00:00
-- url     : https://prove2.me/submissions/99285b4e-1583-4f49-adb7-3ec042b53885

import Mathlib
import Definitions.Def_actuarial_finiteHorizonPolicyValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (policy : ℕ → S → A) (s : S)
  :
  finiteHorizonPolicyValue P reward v terminal policy 0 s = terminal s := rfl
