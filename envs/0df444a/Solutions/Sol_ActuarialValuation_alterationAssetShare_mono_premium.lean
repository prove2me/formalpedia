-- Prove2me | solution 1 for ActuarialValuation.alterationAssetShare_mono_premium
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:44.10549+00:00
-- url     : https://prove2.me/submissions/856931c1-ebd1-4c5e-9fde-e1498a2a80d0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationAssetShare

import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p1 p2 outgo : ℝ) (h : p1 ≤ p2) : alterationAssetShare p1 outgo ≤ alterationAssetShare p2 outgo := by
  unfold alterationAssetShare
  linarith
