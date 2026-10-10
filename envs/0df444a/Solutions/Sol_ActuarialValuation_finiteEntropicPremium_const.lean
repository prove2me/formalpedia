-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicPremium_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:34:16.806699+00:00
-- url     : https://prove2.me/submissions/7e0cd6ab-5654-40d4-a1e2-58e358719612

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_finiteEntropicPremium
import Theorems.Thm_ActuarialValuation_finiteExponentialMoment_const
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (gamma c : ℝ) (hsum : (∑ ω : Ω, w ω) = 1)
    (hgamma : gamma ≠ 0) :
    finiteEntropicPremium w (fun _ => c) gamma = c := by
  unfold finiteEntropicPremium
  rw [finiteExponentialMoment_const w gamma c hsum, Real.log_exp]
  field_simp
