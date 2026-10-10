-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityAccuracy_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:08:09.745655+00:00
-- url     : https://prove2.me/submissions/b89adb08-1e52-46b0-b96a-f50fa5505280

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight
import Definitions.Def_actuarial_exposureCredibilityMinError
import Definitions.Def_actuarial_exposureCredibilityGain

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM P₁ P₂ : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM)
  (hP₁ : 0 ≤ P₁) (hP : P₁ ≤ P₂) :
  (exposureCredibilityWeight EPV VHM P₁ ≤
    exposureCredibilityWeight EPV VHM P₂) ∧
  (0 ≤ exposureCredibilityGain EPV VHM P₁ P₂) ∧
  (exposureCredibilityMinError EPV VHM P₂ ≤
    exposureCredibilityMinError EPV VHM P₁) := by
  have hmono : exposureCredibilityWeight EPV VHM P₁ ≤
      exposureCredibilityWeight EPV VHM P₂ := by
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
  have hrisk : exposureCredibilityMinError EPV VHM P₂ ≤
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
  constructor
  · exact hmono
  constructor
  · unfold exposureCredibilityGain
    exact sub_nonneg.mpr hmono
  · exact hrisk
