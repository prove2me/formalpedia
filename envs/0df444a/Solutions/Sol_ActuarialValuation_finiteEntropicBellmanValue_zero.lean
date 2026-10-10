-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicBellmanValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:11:40.71613+00:00
-- url     : https://prove2.me/submissions/351067f2-d5f1-48b3-bdb7-99cbedd37643

import Mathlib
import Definitions.Def_actuarial_finiteEntropicBellmanValue
open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (P : S → A → S → ℝ) (cost : S → A → S → ℝ) (beta gamma : ℝ)
    (terminal : S → ℝ) (s : S) :
    finiteEntropicBellmanValue P cost beta gamma terminal 0 s = terminal s := by
  simp [finiteEntropicBellmanValue]
