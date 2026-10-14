-- Prove2me | solution 1 for ActuarialValuation.pfAssetsNext_contribution_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:37:48.470008+00:00
-- url     : https://prove2.me/submissions/e19b23b4-0ef4-4e38-b085-a84ae3659bd4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfAssetsNext
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a c i b e extra : ℝ) : pfAssetsNext a (c+extra) i b e=pfAssetsNext a c i b e+extra := by
  unfold pfAssetsNext
  ring
