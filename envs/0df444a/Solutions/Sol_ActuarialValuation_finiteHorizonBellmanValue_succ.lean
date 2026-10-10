-- Prove2me | solution 1 for ActuarialValuation.finiteHorizonBellmanValue_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:50:58.638005+00:00
-- url     : https://prove2.me/submissions/83070f6c-27e0-49b9-b88b-51209c7d0f67

import Mathlib
import Definitions.Def_actuarial_finiteHorizonBellmanValue
import Definitions.Def_actuarial_finiteStageBellmanMaximum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (n : ℕ) (s : S)
  :
  finiteHorizonBellmanValue P reward v terminal (n + 1) s =
  finiteStageBellmanMaximum P reward v
    (finiteHorizonBellmanValue P reward v terminal n) s := rfl
