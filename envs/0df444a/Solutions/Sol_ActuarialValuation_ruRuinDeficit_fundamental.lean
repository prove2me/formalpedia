-- Prove2me | solution 1 for ActuarialValuation.ruRuinDeficit_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:41:02.036899+00:00
-- url     : https://prove2.me/submissions/2f7f604e-2c48-4930-82ee-345d0c290a51

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruFirstRuin
import Definitions.Def_actuarial_ruRuinAt
import Definitions.Def_actuarial_ruDeficit
import Definitions.Def_actuarial_ruRetainedSurplus
import Definitions.Def_actuarial_ruCededTotal
import Definitions.Def_actuarial_ruClaimTotal
import Definitions.Def_actuarial_ruRetained
import Definitions.Def_actuarial_ruStopLoss
import Theorems.Thm_ActuarialValuation_ruSurplus_succ
import Theorems.Thm_ActuarialValuation_ruFirstRuin_at
import Theorems.Thm_ActuarialValuation_ruDeficit_if_ruin
import Theorems.Thm_ActuarialValuation_ruDeficit_positive_if_ruin
import Theorems.Thm_ActuarialValuation_ruRetainedSurplus_ge_gross
import Theorems.Thm_ActuarialValuation_ruClaimTotal_add
import Theorems.Thm_ActuarialValuation_ruReinsurance_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c d : ℝ) (x : ℕ → ℝ) (n : ℕ)
    (h : ruFirstRuin u c x n) :
    (ruPathSurplus u c x (n+1) =
      ruPathSurplus u c x n + c-x n) ∧
    (ruDeficit u c x n = -ruPathSurplus u c x n) ∧
    (0 < ruDeficit u c x n) ∧
    (ruPathSurplus u c x n ≤ ruRetainedSurplus u c d x n) ∧
    (ruRetainedSurplus u c d x n =
      ruPathSurplus u c x n+ruCededTotal x d n) := by
  have hr : ruRuinAt u c x n := ruFirstRuin_at u c x n h
  have hagg : ruClaimTotal x n =
      ruClaimTotal (fun k => ruRetained (x k) d) n +
        ruCededTotal x d n := by
    calc
      ruClaimTotal x n =
          ruClaimTotal (fun k => ruRetained (x k) d +
            ruStopLoss (x k) d) n := by
            unfold ruClaimTotal
            apply Finset.sum_congr rfl
            intro k hk
            exact (ruReinsurance_split (x k) d).symm
      _ = ruClaimTotal (fun k => ruRetained (x k) d) n +
          ruCededTotal x d n := by
            rw [ruClaimTotal_add]
            rfl
  have hret : ruRetainedSurplus u c d x n =
      ruPathSurplus u c x n + ruCededTotal x d n := by
    unfold ruRetainedSurplus ruPathSurplus
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ruSurplus_succ u c x n
  · exact ruDeficit_if_ruin u c x n hr
  · exact ruDeficit_positive_if_ruin u c x n hr
  · exact ruRetainedSurplus_ge_gross u c d x n
  · exact hret
