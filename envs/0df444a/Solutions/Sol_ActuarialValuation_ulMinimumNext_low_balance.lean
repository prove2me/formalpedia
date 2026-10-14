-- Prove2me | solution 1 for ActuarialValuation.ulMinimumNext_low_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:23:06.120021+00:00
-- url     : https://prove2.me/submissions/eed28e7b-4c8c-4bbc-98c2-bb22a7b207f1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulMinimumNext
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (earned mortality floor : ℝ) (h : earned≤floor) (hm : 1-mortality ≠ 0) : ulMinimumNext earned mortality floor * (1-mortality) + mortality*floor = earned := by
  have hlow : ulMinimumNext earned mortality floor =
      (earned - mortality * floor) / (1 - mortality) := by
    simp [ulMinimumNext, h]
  rw [hlow]
  have hc : ((earned - mortality * floor) / (1 - mortality)) *
      (1 - mortality) = earned - mortality * floor :=
    (eq_div_iff hm).mp rfl
  rw [hc]
  ring
