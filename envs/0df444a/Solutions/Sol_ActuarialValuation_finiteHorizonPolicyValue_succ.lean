-- Prove2me | solution 1 for ActuarialValuation.finiteHorizonPolicyValue_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:51:00.344535+00:00
-- url     : https://prove2.me/submissions/631189dd-aa07-4708-b16d-52a22b66f3ba

import Mathlib
import Definitions.Def_actuarial_finiteHorizonPolicyValue
import Definitions.Def_actuarial_finiteStageActionReturn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (policy : ℕ → S → A) (n : ℕ) (s : S)
  :
  finiteHorizonPolicyValue P reward v terminal policy (n + 1) s =
  finiteStageActionReturn P reward v
    (finiteHorizonPolicyValue P reward v terminal policy n) s (policy n s) := rfl
