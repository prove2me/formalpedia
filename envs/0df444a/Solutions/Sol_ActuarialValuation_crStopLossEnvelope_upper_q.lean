-- Prove2me | solution 1 for ActuarialValuation.crStopLossEnvelope_upper_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:58:25.993525+00:00
-- url     : https://prove2.me/submissions/2fe72b6e-fc3f-4fba-95a1-54470dbe54d3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLossEnvelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q X : Fin n→ℝ) (d : ℝ) : crStopLoss q X d≤crStopLossEnvelope p q X d := by
  unfold crStopLossEnvelope
  exact le_max_right _ _
