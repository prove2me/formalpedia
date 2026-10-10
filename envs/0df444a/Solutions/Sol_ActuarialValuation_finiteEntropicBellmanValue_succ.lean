-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicBellmanValue_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:36:14.931098+00:00
-- url     : https://prove2.me/submissions/7111c1a2-20ed-4b7e-b1bb-c0af519ae15d

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanValue
import Definitions.Def_actuarial_finiteEntropicBellmanMinimum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {S A : Type*}
  [Fintype S] [Fintype A] [Nonempty A]
  (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (n : ℕ) (s : S) :
  finiteEntropicBellmanValue P cost beta gamma terminal (n + 1) s =
    finiteEntropicBellmanMinimum P cost beta gamma
      (finiteEntropicBellmanValue P cost beta gamma terminal n) s := by
  rfl
