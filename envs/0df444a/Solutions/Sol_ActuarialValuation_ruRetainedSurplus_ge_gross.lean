-- Prove2me | solution 1 for ActuarialValuation.ruRetainedSurplus_ge_gross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:34:15.194457+00:00
-- url     : https://prove2.me/submissions/c2b48a91-c846-4100-80fb-8ab9a36eec91

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruRetainedSurplus
import Definitions.Def_actuarial_ruClaimTotal
import Definitions.Def_actuarial_ruRetained

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c d : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ruPathSurplus u c x n ≤ ruRetainedSurplus u c d x n := by
  have hsum :
      ruClaimTotal (fun k => ruRetained (x k) d) n ≤
        ruClaimTotal x n := by
    unfold ruClaimTotal
    apply Finset.sum_le_sum
    intro k hk
    exact min_le_left (x k) d
  unfold ruRetainedSurplus ruPathSurplus
  linarith
