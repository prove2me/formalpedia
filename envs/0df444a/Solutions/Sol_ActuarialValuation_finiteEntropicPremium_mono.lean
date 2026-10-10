-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicPremium_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:31:34.404899+00:00
-- url     : https://prove2.me/submissions/7edbb5aa-397f-4400-a5f2-2266464dcd5d

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_actuarial_finiteEntropicPremium
import Theorems.Thm_ActuarialValuation_finiteExponentialMoment_positive
import Theorems.Thm_ActuarialValuation_finiteExponentialMoment_mono
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ)
    (gamma : ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hsum : (∑ ω : Ω, w ω) = 1)
    (hgamma : 0 < gamma) (hXY : ∀ ω, X ω ≤ Y ω) :
    finiteEntropicPremium w X gamma ≤ finiteEntropicPremium w Y gamma := by
  have hpos := finiteExponentialMoment_positive w X gamma hw hsum
  have hle := finiteExponentialMoment_mono w X Y gamma hw (le_of_lt hgamma) hXY
  unfold finiteEntropicPremium
  exact div_le_div_of_nonneg_right (Real.log_le_log hpos hle) (le_of_lt hgamma)
