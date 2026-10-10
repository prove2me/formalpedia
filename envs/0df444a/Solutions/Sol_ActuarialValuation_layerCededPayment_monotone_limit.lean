-- Prove2me | solution 1 for ActuarialValuation.layerCededPayment_monotone_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:49:13.78133+00:00
-- url     : https://prove2.me/submissions/293d4833-0c4a-4ad8-a601-8715ab9605e5

import Mathlib
import Definitions.Def_actuarial_layerCededPayment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (x d L1 L2 : ℕ) (h : L1 ≤ L2) :
  layerCededPayment x d L1 ≤ layerCededPayment x d L2 := by
  dsimp [layerCededPayment]
  omega
