-- Prove2me | solution 1 for ActuarialValuation.ruRetainedSurplus_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:36:20.018613+00:00
-- url     : https://prove2.me/submissions/bee9d22a-565d-4377-9c9b-a3b79707e165

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruRetainedSurplus
import Definitions.Def_actuarial_ruClaimTotal
import Definitions.Def_actuarial_ruCededTotal
import Definitions.Def_actuarial_ruRetained
import Definitions.Def_actuarial_ruStopLoss
import Theorems.Thm_ActuarialValuation_ruClaimTotal_add
import Theorems.Thm_ActuarialValuation_ruReinsurance_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c d : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ruRetainedSurplus u c d x n =
      ruPathSurplus u c x n + ruCededTotal x d n := by
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
  unfold ruRetainedSurplus ruPathSurplus
  linarith
