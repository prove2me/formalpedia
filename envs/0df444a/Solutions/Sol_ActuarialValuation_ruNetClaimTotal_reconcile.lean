-- Prove2me | solution 1 for ActuarialValuation.ruNetClaimTotal_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:31:58.322646+00:00
-- url     : https://prove2.me/submissions/114888ea-cead-41e1-96a6-a6003be8b078

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ruNetClaimTotal
import Definitions.Def_actuarial_ruNetClaim
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruPremiumTotal
import Definitions.Def_actuarial_ruClaimTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ruPathSurplus u c x n = u - ruNetClaimTotal x c n := by
  simp [ruPathSurplus, ruNetClaimTotal, ruNetClaim,
    ruPremiumTotal, ruClaimTotal, Finset.sum_sub_distrib] <;> ring
