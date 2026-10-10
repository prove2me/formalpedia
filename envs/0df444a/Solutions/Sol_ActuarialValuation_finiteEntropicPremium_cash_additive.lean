-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicPremium_cash_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:30:58.714799+00:00
-- url     : https://prove2.me/submissions/7f5504ab-98cd-45ef-98ce-bd4e2c7486f0

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_finiteEntropicPremium
import Definitions.Def_actuarial_finiteExponentialMoment
import Theorems.Thm_ActuarialValuation_finiteExponentialMoment_shift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ)
    (gamma c : ℝ) (hgamma : gamma ≠ 0)
    (hM : 0 < finiteExponentialMoment w X gamma) :
    finiteEntropicPremium w (fun ω => X ω + c) gamma =
      finiteEntropicPremium w X gamma + c := by
  unfold finiteEntropicPremium
  rw [finiteExponentialMoment_shift w X gamma c]
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hM), Real.log_exp]
  field_simp
  ring
