-- Prove2me | solution 1 for Arxiv2005_04287.logAmplitude_sech_sq
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:38:02.266473+00:00
-- url     : https://prove2.me/submissions/e4cf490f-f8a2-4a59-9b4b-4f5dc640b464

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory

theorem solution (y : ℝ) :
    Arxiv2005_04287.logAmpDensity 2 1 y = 1 / (2 * Real.cosh y ^ 2) := by
  unfold Arxiv2005_04287.logAmpDensity
  have hp : 0 < Real.exp (2 * y) / 1 ^ 2 + 1 := by positivity
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  push_cast
  rw [Real.cosh_eq]
  have he : Real.exp (2 * y) = Real.exp y ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have hne : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [he, hne]
  have hy : 0 < Real.exp y := Real.exp_pos y
  field_simp
  ring
