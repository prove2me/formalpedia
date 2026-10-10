-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityGain_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:07:19.04756+00:00
-- url     : https://prove2.me/submissions/23b80c7e-8295-4519-8427-250f019dc287

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityGain

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM P₁ P₂ : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM)
  (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂) :
  0 ≤ exposureCredibilityGain EPV VHM P₁ P₂ := by
  unfold exposureCredibilityGain
  apply sub_nonneg.mpr
  change P₁ * VHM / (P₁ * VHM + EPV) ≤
    P₂ * VHM / (P₂ * VHM + EPV)
  have hA : P₁ * VHM ≤ P₂ * VHM :=
    mul_le_mul_of_nonneg_right hP hV
  have hn₁ : 0 ≤ P₁ * VHM := mul_nonneg hP₁ hV
  have hn₂ : 0 ≤ P₂ * VHM := le_trans hn₁ hA
  have hd₁ : 0 < P₁ * VHM + EPV := add_pos_of_nonneg_of_pos hn₁ hE
  have hd₂ : 0 < P₂ * VHM + EPV := add_pos_of_nonneg_of_pos hn₂ hE
  apply (div_le_div_iff₀ hd₁ hd₂).2
  nlinarith [mul_nonneg (le_of_lt hE) (sub_nonneg.mpr hA)]
