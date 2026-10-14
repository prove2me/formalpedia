-- Prove2me | solution 1 for ActuarialValuation.pfModifiedRate_above_normal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:33:22.440584+00:00
-- url     : https://prove2.me/submissions/1ee01596-2966-40ec-ae57-bf0cdbc9ab26

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfModifiedRate
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (normal deficit annuity : ℝ) (hd : 0≤deficit) (ha : 0<annuity) : normal≤pfModifiedRate normal deficit annuity := by
  unfold pfModifiedRate pfAmortisation
  have hn : 0 ≤ deficit / annuity := div_nonneg hd ha.le
  linarith
