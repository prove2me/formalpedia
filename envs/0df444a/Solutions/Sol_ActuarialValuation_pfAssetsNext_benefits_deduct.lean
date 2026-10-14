-- Prove2me | solution 1 for ActuarialValuation.pfAssetsNext_benefits_deduct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:36:40.464987+00:00
-- url     : https://prove2.me/submissions/f5f37ad9-5de8-46be-9188-da7dd0d41b39

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAssetsNext
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a c i b e extra : ℝ) : pfAssetsNext a c i (b+extra) e=pfAssetsNext a c i b e-extra := by
  unfold pfAssetsNext
  ring
