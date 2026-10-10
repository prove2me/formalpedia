-- Prove2me | solution 1 for ActuarialValuation.dbCommutationHeadroom_max_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:12.526187+00:00
-- url     : https://prove2.me/submissions/7fc611d1-a9ce-4457-ba9b-1893214a3d28

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash
import Definitions.Def_actuarial_dbCommutationHeadroom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f : ℝ) (hf : 0 < f) :
  dbCommutationHeadroom g (dbHMRCMaximumCash g f) f = 0 := by
  unfold dbCommutationHeadroom dbCommutedPension dbHMRCMaximumCash
  have hfn : f ≠ 0 := ne_of_gt hf
  have hdn : 20 + 3 * f ≠ 0 := ne_of_gt (by linarith : 0 < 20 + 3 * f)
  field_simp [hfn, hdn]
  ring
