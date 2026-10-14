-- Prove2me | solution 1 for ActuarialValuation.alterationAssetShare_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:32.121018+00:00
-- url     : https://prove2.me/submissions/60532d0c-be00-4d3f-b3f5-ef9152351d70

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationAssetShare

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p outgo : ℝ) : alterationAssetShare p outgo + outgo = p := by
  unfold alterationAssetShare
  ring
