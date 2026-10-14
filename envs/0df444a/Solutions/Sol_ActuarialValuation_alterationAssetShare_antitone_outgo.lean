-- Prove2me | solution 1 for ActuarialValuation.alterationAssetShare_antitone_outgo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:04:49.040978+00:00
-- url     : https://prove2.me/submissions/74dd212f-2e48-47af-a4a4-f469aee46846

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationAssetShare
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p o1 o2 : ℝ) (h : o1 ≤ o2) : alterationAssetShare p o2 ≤ alterationAssetShare p o1 := by
  unfold alterationAssetShare
  linarith
