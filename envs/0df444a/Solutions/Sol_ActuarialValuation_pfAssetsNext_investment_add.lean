-- Prove2me | solution 1 for ActuarialValuation.pfAssetsNext_investment_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:39:08.722+00:00
-- url     : https://prove2.me/submissions/58f8a2ad-4157-48b8-becb-1c6a8dbd94f7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAssetsNext
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a c i b e extra : ℝ) : pfAssetsNext a c (i+extra) b e=pfAssetsNext a c i b e+extra := by
  unfold pfAssetsNext
  ring
