-- Prove2me | solution 1 for ActuarialValuation.ulTypeA_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:22:52.954399+00:00
-- url     : https://prove2.me/submissions/ef01e786-0804-404f-8832-e3421381b68e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeANext
import Definitions.Def_actuarial_ulEarned
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account prem expense flat interest mortality face : ℝ) (hm : 1-mortality ≠ 0) : ulTypeANext account prem expense flat interest mortality face * (1-mortality) + mortality*face = ulEarned account prem expense flat interest := by
  change ((ulEarned account prem expense flat interest - mortality * face) /
    (1 - mortality)) * (1 - mortality) + mortality * face =
    ulEarned account prem expense flat interest
  have hc : ((ulEarned account prem expense flat interest - mortality * face) /
      (1 - mortality)) * (1 - mortality) =
      ulEarned account prem expense flat interest - mortality * face :=
    (eq_div_iff hm).mp rfl
  rw [hc]
  ring
