-- Prove2me | solution 1 for ActuarialValuation.transitionRewardValue_zero_cashflows
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:18:01.971663+00:00
-- url     : https://prove2.me/submissions/b41f2017-544c-4ffa-876e-45fad5c04d7d

import Mathlib
import Definitions.Def_actuarial_transitionRewardValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P : S → S → ℝ) (v : ℝ) (a : S)
    :
    transitionRewardValue P v (fun _ => 0) (fun _ => 0) a = 0 := by
  show v * (∑ b : S, P a b * (0 + 0)) = 0
  simp
