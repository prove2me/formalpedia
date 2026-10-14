-- Prove2me | solution 1 for ActuarialValuation.nhIntensity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:40:39.552342+00:00
-- url     : https://prove2.me/submissions/6e5b5ab7-f4fc-4223-8579-c79b1a44833b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhIntensity
open ActuarialValuation

theorem solution(a b t : ℝ) (ha : 0≤a) (hb : 0≤b) (ht : 0≤t) : 0≤nhIntensity a b t := by
  first
  | (simp [nhIntensity]; done)
  | (norm_num [nhIntensity]; done)
  | (unfold nhIntensity; positivity)
  | (simp only [nhIntensity]; positivity)
  | (unfold nhIntensity; ring)
  | (unfold nhIntensity; simp; done)
  | (unfold nhIntensity; norm_num; done)
  | (simp [nhIntensity]; ring)
  | (unfold nhIntensity; split_ifs <;> simp_all <;> linarith)
  | (unfold nhIntensity; nlinarith [sq_nonneg 0])
  | (simp_all [nhIntensity]; done)
  | (unfold nhIntensity; simp_all; done)
  | rfl
