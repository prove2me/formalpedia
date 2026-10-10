-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityPremium_between
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:02:52.52498+00:00
-- url     : https://prove2.me/submissions/58087c7b-e921-447e-8de5-c8843b73c721

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM P experience collective : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P)
  (hx : experience ≤ collective) :
  experience ≤ exposureCredibilityPremium EPV VHM P experience collective ∧
    exposureCredibilityPremium EPV VHM P experience collective ≤ collective := by
  have hn : 0 ≤ P * VHM := mul_nonneg hP hV
  have hd : 0 < P * VHM + EPV := add_pos_of_nonneg_of_pos hn hE
  have hw : 0 ≤ exposureCredibilityWeight EPV VHM P := by
    change 0 ≤ P * VHM / (P * VHM + EPV)
    exact div_nonneg hn (le_of_lt hd)
  have hw1 : exposureCredibilityWeight EPV VHM P ≤ 1 := by
    change P * VHM / (P * VHM + EPV) ≤ 1
    apply (div_le_iff₀ hd).2
    simpa only [one_mul] using
      (show P * VHM ≤ P * VHM + EPV by linarith)
  unfold exposureCredibilityPremium
  constructor
  · have hh := mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hx)
    nlinarith
  · have hh := mul_nonneg hw (sub_nonneg.mpr hx)
    nlinarith
