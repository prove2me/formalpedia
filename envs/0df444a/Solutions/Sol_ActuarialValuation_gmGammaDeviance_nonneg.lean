-- Prove2me | solution 1 for ActuarialValuation.gmGammaDeviance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:45:50.664986+00:00
-- url     : https://prove2.me/submissions/b0f25eff-28bb-4326-9bf6-c23cc9921bea

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_gmGammaDeviance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (observed mean : ℝ) (ho : 0 < observed)
    (hm : 0 < mean) : 0 ≤ gmGammaDeviance observed mean := by
  have hratio : 0 < observed / mean := div_pos ho hm
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hquot : (observed - mean) / mean = observed / mean - 1 := by
    rw [sub_div, div_self (ne_of_gt hm)]
  unfold gmGammaDeviance
  rw [hquot]
  nlinarith [hlog]
