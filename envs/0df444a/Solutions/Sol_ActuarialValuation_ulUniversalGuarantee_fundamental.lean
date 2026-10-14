-- Prove2me | solution 1 for ActuarialValuation.ulUniversalGuarantee_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:24:26.438316+00:00
-- url     : https://prove2.me/submissions/85a3666f-8c50-42bc-a6a3-d697b7802066

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulTypeBNext
import Definitions.Def_actuarial_ulTypeANext
import Definitions.Def_actuarial_ulEarned
import Definitions.Def_actuarial_ulGuaranteedPV
import Definitions.Def_actuarial_ulAccountPV
import Definitions.Def_actuarial_ulShortfallPV
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account prem expense flat interest mortality face : ℝ) (hm : 1-mortality ≠ 0) {m : ℕ} (prob discount balances floors : Fin m → ℝ) : (ulTypeBNext account prem expense flat interest mortality face + mortality*face = ulEarned account prem expense flat interest) ∧ (ulTypeANext account prem expense flat interest mortality face*(1-mortality)+mortality*face = ulEarned account prem expense flat interest) ∧ (ulGuaranteedPV prob discount balances floors = ulAccountPV prob discount balances + ulShortfallPV prob discount balances floors) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ulTypeBNext
    ring
  · change ((ulEarned account prem expense flat interest - mortality * face) /
      (1 - mortality)) * (1 - mortality) + mortality * face =
      ulEarned account prem expense flat interest
    have hc : ((ulEarned account prem expense flat interest - mortality * face) /
        (1 - mortality)) * (1 - mortality) =
        ulEarned account prem expense flat interest - mortality * face :=
      (eq_div_iff hm).mp rfl
    rw [hc]
    ring
  · have hmax (a b : ℝ) : max a b = a + max (b - a) 0 := by
      rcases le_total b a with h | h
      · rw [max_eq_left h, max_eq_right (sub_nonpos.mpr h)]
        ring
      · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
        ring
    unfold ulGuaranteedPV ulAccountPV ulShortfallPV
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    change prob ω * discount ω * max (balances ω) (floors ω) =
      prob ω * discount ω * balances ω +
        prob ω * discount ω * max (floors ω - balances ω) 0
    rw [hmax]
    ring
