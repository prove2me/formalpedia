-- Prove2me | solution 1 for ActuarialValuation.layerCededPayment_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:49:05.825752+00:00
-- url     : https://prove2.me/submissions/41f9b020-2d50-491d-bbca-521106ae6524

import Mathlib
import Definitions.Def_actuarial_layerExcessLoss
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerHigherExcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d L : ℕ) :
  layerExcessLoss x d =
    layerCededPayment x d L + layerHigherExcess x d L := by
  dsimp [layerExcessLoss, layerCededPayment, layerHigherExcess]
  omega
