-- Prove2me | solution 1 for ActuarialValuation.transitionRewardValue_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:17:57.487266+00:00
-- url     : https://prove2.me/submissions/18ed6d83-057d-48cc-a8e7-e00f70763537

import Mathlib
import Definitions.Def_actuarial_transitionRewardValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P : S → S → ℝ) (r next : S → ℝ) (a : S)
    :
    transitionRewardValue P 0 r next a = 0 := by
  show (0 : ℝ) * (∑ b : S, P a b * (r b + next b)) = 0
  exact zero_mul _
