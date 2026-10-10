-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffLoss_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:46:33.017678+00:00
-- url     : https://prove2.me/submissions/a7c08033-5ad8-4050-8092-9e5b553ab0ad

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffLoss
import Definitions.Def_actuarial_finiteReserveLossAtIssue
import Definitions.Def_actuarial_finiteLifeInForceIndicator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (K : Ω → ℕ) (v : ℝ)
    (premium benefit reserve : ℕ → ℝ) (ω : Ω) :
    finiteHattendorffLoss K 0 v premium benefit reserve ω =
      reserve 0 := by
  simp [finiteHattendorffLoss, finiteReserveLossAtIssue,
    finiteLifeInForceIndicator]
