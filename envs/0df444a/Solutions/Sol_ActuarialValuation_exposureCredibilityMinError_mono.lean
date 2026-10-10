-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityMinError_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:07:28.638696+00:00
-- url     : https://prove2.me/submissions/f62757a7-a327-4baf-97b3-376f41f59884

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityMinError

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM P₁ P₂ : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM)
  (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂) :
  exposureCredibilityMinError EPV VHM P₂ ≤
    exposureCredibilityMinError EPV VHM P₁ := by
  change EPV * VHM / (P₂ * VHM + EPV) ≤
    EPV * VHM / (P₁ * VHM + EPV)
  have ha : P₁ * VHM ≤ P₂ * VHM :=
    mul_le_mul_of_nonneg_right hP hV
  have hn₁ : 0 ≤ P₁ * VHM := mul_nonneg hP₁ hV
  have hn₂ : 0 ≤ P₂ * VHM := le_trans hn₁ ha
  have hd₁ : 0 < P₁ * VHM + EPV := add_pos_of_nonneg_of_pos hn₁ hE
  have hd₂ : 0 < P₂ * VHM + EPV := add_pos_of_nonneg_of_pos hn₂ hE
  apply (div_le_div_iff₀ hd₂ hd₁).2
  exact mul_le_mul_of_nonneg_left (add_le_add_left ha EPV)
    (mul_nonneg (le_of_lt hE) hV)
