-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicPolicyValue_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:37:27.359158+00:00
-- url     : https://prove2.me/submissions/50a7acdb-47d8-4edf-a90d-b76bbf7e9e4f

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPolicyValue
import Definitions.Def_actuarial_finiteEntropicStageCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {S A : Type*}
  [Fintype S] (P : S → A → S → ℝ)
  (cost : S → A → S → ℝ) (beta gamma : ℝ)
  (terminal : S → ℝ) (policy : ℕ → S → A) (n : ℕ) (s : S) :
  finiteEntropicPolicyValue P cost beta gamma terminal policy (n + 1) s =
    finiteEntropicStageCost P cost beta gamma
      (finiteEntropicPolicyValue P cost beta gamma terminal policy n)
      s (policy n s) := by
  rfl
