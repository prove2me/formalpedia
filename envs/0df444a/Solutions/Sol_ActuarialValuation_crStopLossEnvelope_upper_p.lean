-- Prove2me | solution 1 for ActuarialValuation.crStopLossEnvelope_upper_p
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:58:15.004489+00:00
-- url     : https://prove2.me/submissions/9cd0172a-e60a-4276-b368-e1fe4821c9d8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossEnvelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) (d : ℝ) : crStopLoss p X d≤crStopLossEnvelope p q X d := by
  unfold crStopLossEnvelope
  exact le_max_left _ _
