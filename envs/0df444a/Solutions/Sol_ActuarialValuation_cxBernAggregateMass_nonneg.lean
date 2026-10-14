-- Prove2me | solution 1 for ActuarialValuation.cxBernAggregateMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:37:35.971236+00:00
-- url     : https://prove2.me/submissions/5f0b95fd-afb1-4f2f-bdb0-ec13ea4d7fff

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernAggregateMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p0 p1 : ℝ) (f : ℕ → ℝ) (k : ℕ) (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (hf : 0 ≤ f k) (hf0 : 0 ≤ f 0) : 0 ≤ cxBernAggregateMass p0 p1 f k := by
  unfold cxBernAggregateMass
  split_ifs with hk
  · exact add_nonneg h0 (mul_nonneg h1 hf0)
  · exact mul_nonneg h1 hf
