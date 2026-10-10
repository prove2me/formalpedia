-- Prove2me | solution 1 for ActuarialValuation.retentionOneStepCost_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:56:17.122986+00:00
-- url     : https://prove2.me/submissions/6a525445-a2da-4801-bee4-32ffe800939b

import Mathlib
import Definitions.Def_actuarial_expectedRetainedLoss
import Definitions.Def_actuarial_retentionOneStepCost
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (q : ℝ → ℝ) (a : ℝ) :
    retentionOneStepCost w z q a = q a + expectedRetainedLoss w z a := by
  change expectedRetainedLoss w z a + q a =
    q a + expectedRetainedLoss w z a
  ring
