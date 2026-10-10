-- Prove2me | solution 1 for ActuarialValuation.layerCededPayment_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:48:53.437798+00:00
-- url     : https://prove2.me/submissions/dd3f8c34-d20d-4e9e-9abd-b3ca6cfaf5a0

import Mathlib
import Definitions.Def_actuarial_layerCededPayment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d L : ℕ)
  (h : d + L ≤ x) :
  layerCededPayment x d L = L := by
  dsimp [layerCededPayment, layerExcessLoss]
  have hle : L ≤ x - d := by omega
  exact Nat.min_eq_right hle
