-- Prove2me | solution 1 for ActuarialValuation.bnAmerican_two_step_dominate_european
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:06:25.562293+00:00
-- url     : https://prove2.me/submissions/7e4828b1-6009-4669-a7de-2df307e472a0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnTwoStepPrice
import Definitions.Def_actuarial_bnAmericanTwoPeriod

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R q immediate up down uu ud du dd : ℝ) (hR : 0 < R) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : bnTwoStepPrice R q uu ud du dd ≤ bnAmericanTwoPeriod R q immediate up down uu ud du dd := by
  let eu := bnOnePeriodPrice R q uu ud
  let ed := bnOnePeriodPrice R q du dd
  let au := bnAmericanNode up eu
  let ad := bnAmericanNode down ed
  have hup : eu ≤ au := by
    dsimp [au, bnAmericanNode]
    exact le_max_right _ _
  have hdown : ed ≤ ad := by
    dsimp [ad, bnAmericanNode]
    exact le_max_right _ _
  have hweighted : q*eu + (1-q)*ed ≤ q*au + (1-q)*ad :=
    add_le_add (mul_le_mul_of_nonneg_left hup hq0)
      (mul_le_mul_of_nonneg_left hdown (sub_nonneg.mpr hq1))
  have hprice : bnOnePeriodPrice R q eu ed ≤ bnOnePeriodPrice R q au ad := by
    change (q*eu + (1-q)*ed)/R ≤ (q*au+(1-q)*ad)/R
    have hdiff : 0 ≤ ((q*au + (1-q)*ad) - (q*eu+(1-q)*ed))/R :=
      div_nonneg (sub_nonneg.mpr hweighted) (le_of_lt hR)
    rw [sub_div] at hdiff
    linarith
  have htwo : bnTwoStepPrice R q uu ud du dd = bnOnePeriodPrice R q eu ed := by
    dsimp [eu, ed, bnTwoStepPrice, bnOnePeriodPrice, bnExpectedPayoff]
    field_simp [ne_of_gt hR] <;> ring
  have houter : bnOnePeriodPrice R q au ad ≤
      bnAmericanNode immediate (bnOnePeriodPrice R q au ad) := by
    unfold bnAmericanNode
    exact le_max_right _ _
  calc
    bnTwoStepPrice R q uu ud du dd = bnOnePeriodPrice R q eu ed := htwo
    _ ≤ bnOnePeriodPrice R q au ad := hprice
    _ ≤ bnAmericanTwoPeriod R q immediate up down uu ud du dd := by
      change bnOnePeriodPrice R q au ad ≤
        bnAmericanNode immediate (bnOnePeriodPrice R q au ad)
      exact houter
