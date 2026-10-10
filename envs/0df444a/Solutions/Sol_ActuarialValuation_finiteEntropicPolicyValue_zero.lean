-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicPolicyValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:11:39.592053+00:00
-- url     : https://prove2.me/submissions/6c66467d-f606-49fa-8bf6-2ea9601b888b

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPolicyValue
open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] (P : S → A → S → ℝ)
    (cost : S → A → S → ℝ) (beta gamma : ℝ)
    (terminal : S → ℝ) (policy : ℕ → S → A) (s : S) :
    finiteEntropicPolicyValue P cost beta gamma terminal policy 0 s = terminal s := by
  simp [finiteEntropicPolicyValue]
