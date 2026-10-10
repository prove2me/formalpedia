-- Prove2me | solution 1 for ActuarialValuation.layerCededPayment_le_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:45:03.91421+00:00
-- url     : https://prove2.me/submissions/77d7257c-96e9-4f27-9ae9-22e0a8589672

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d L : ℕ) :
  layerCededPayment x d L ≤ layerExcessLoss x d := by
  exact min_le_left _ _
