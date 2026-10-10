-- Prove2me | solution 1 for ActuarialValuation.layerCededPayment_within
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:48:59.334416+00:00
-- url     : https://prove2.me/submissions/31943bef-e5d1-4ba2-b1fd-7250406fb39d

import Mathlib
import Definitions.Def_actuarial_layerCededPayment
import Definitions.Def_actuarial_layerExcessLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d L : ℕ)
  (h : x ≤ d + L) :
  layerCededPayment x d L = layerExcessLoss x d := by
  dsimp [layerCededPayment, layerExcessLoss]
  have hle : x - d ≤ L := by omega
  exact Nat.min_eq_left hle
