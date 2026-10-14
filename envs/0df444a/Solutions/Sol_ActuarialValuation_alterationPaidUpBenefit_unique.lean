-- Prove2me | solution 1 for ActuarialValuation.alterationPaidUpBenefit_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:16:08.829407+00:00
-- url     : https://prove2.me/submissions/51b5a4cf-abc4-4691-9c73-62538ac16d9a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationPaidUpBenefit
import Definitions.Def_actuarial_alterationPaidUpValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (V A b : ℝ) (hA : A ≠ 0) (h : alterationPaidUpValue b A = V) : b = alterationPaidUpBenefit V A := by
  unfold alterationPaidUpValue at h
  unfold alterationPaidUpBenefit
  exact (eq_div_iff hA).2 h
