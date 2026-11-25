-- Prove2me | solution 1 for Arxiv2005_04287.burr_mode
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:39:28.853084+00:00
-- url     : https://prove2.me/submissions/145bf22f-15db-4c4e-b4c0-7378cab049e8

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

open MeasureTheory

namespace S69B

lemma key (b t : ℝ) (hb : 1 < b) (ht : 0 < t) (ht1 : t ≠ 1) :
    Real.sqrt t < (1 + (t - 1) / (2 * b)) ^ b := by
  have hb0 : 0 < b := by linarith
  have h := rpow_one_add_lt_one_add_mul_self (s := t - 1) (by linarith) (sub_ne_zero.mpr ht1)
    (p := 1 / (2 * b)) (by positivity) (by rw [div_lt_one (by positivity)]; linarith)
  rw [add_sub_cancel] at h
  have h2 := Real.rpow_lt_rpow (by positivity) h hb0
  rw [← Real.rpow_mul ht.le, show 1 / (2 * b) * b = 1 / 2 by field_simp, ← Real.sqrt_eq_rpow] at h2
  convert h2 using 2; ring

lemma mode (b lam : ℝ) (hb : 1 < b) (hlam : 0 < lam) (A : ℝ)
    (hA : A ≠ lam / Real.sqrt (2 * b - 1)) :
    Arxiv2005_04287.burrDensity b lam A <
      Arxiv2005_04287.burrDensity b lam (lam / Real.sqrt (2 * b - 1)) := by
  set c := 2 * b - 1 with hc
  have hc1 : 1 < c := by linarith
  have hc0 : 0 < c := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
  set M := lam / Real.sqrt c with hMdef
  have hM : 0 < M := by positivity
  have hfM : 0 < Arxiv2005_04287.burrDensity b lam M := by
    unfold Arxiv2005_04287.burrDensity; rw [if_pos hM]
    have : 0 < b - 1 := by linarith
    positivity
  rcases le_or_gt A 0 with hA0 | hA0
  · unfold Arxiv2005_04287.burrDensity at hfM ⊢
    rw [if_neg (not_lt.mpr hA0)]; exact hfM
  unfold Arxiv2005_04287.burrDensity
  rw [if_pos hA0, if_pos hM]
  set t := c * (A / lam) ^ 2 with htdef
  have ht : 0 < t := by positivity
  have hsqc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0.le
  have hsqt : Real.sqrt t = Real.sqrt c * (A / lam) := by
    rw [htdef, Real.sqrt_mul hc0.le, Real.sqrt_sq (by positivity)]
  have hAM : A = M * Real.sqrt t := by
    rw [hsqt, hMdef]; field_simp
  have ht1 : t ≠ 1 := by
    intro h; apply hA; rw [hAM, h, Real.sqrt_one, mul_one]
  have e1 : (M / lam) ^ 2 + 1 = (2 * b) / c := by
    rw [hMdef, div_div, div_pow, mul_pow, hsqc]; field_simp; ring
  have e2 : (A / lam) ^ 2 + 1 = (2 * b) / c * (1 + (t - 1) / (2 * b)) := by
    rw [htdef]; field_simp; ring
  have hpos : 0 ≤ 1 + (t - 1) / (2 * b) := by
    rw [show 1 + (t - 1) / (2 * b) = (t + (2 * b - 1)) / (2 * b) by field_simp; ring]
    exact div_nonneg (by linarith) (by linarith)
  rw [e1, e2, Real.mul_rpow (by positivity) hpos]
  have hk := key b t hb ht ht1
  have hb1 : 0 < b - 1 := by linarith
  have hP : 0 < (2 * b / c) ^ b := by positivity
  have hQ : 0 < (1 + (t - 1) / (2 * b)) ^ b := by linarith [Real.sqrt_nonneg t]
  rw [div_lt_div_iff₀ (by positivity) (by positivity), hAM]
  have : M * Real.sqrt t * (2 * (b - 1)) * (lam ^ 2 * (2 * b / c) ^ b)
      < M * ((1 + (t - 1) / (2 * b)) ^ b) * (2 * (b - 1)) * (lam ^ 2 * (2 * b / c) ^ b) := by
    have h0 : 0 < (2 * (b - 1)) * (lam ^ 2 * (2 * b / c) ^ b) := by positivity
    have := mul_lt_mul_of_pos_left hk hM
    nlinarith
  calc 2 * (M * Real.sqrt t) * (b - 1) * (lam ^ 2 * (2 * b / c) ^ b)
      = M * Real.sqrt t * (2 * (b - 1)) * (lam ^ 2 * (2 * b / c) ^ b) := by ring
    _ < M * ((1 + (t - 1) / (2 * b)) ^ b) * (2 * (b - 1)) * (lam ^ 2 * (2 * b / c) ^ b) := this
    _ = 2 * M * (b - 1) * (lam ^ 2 * ((2 * b / c) ^ b * (1 + (t - 1) / (2 * b)) ^ b)) := by ring

end S69B

theorem solution (b lam : ℝ) (hb : 1 < b) (hlam : 0 < lam) :
    ∀ A : ℝ, A ≠ lam / Real.sqrt (2 * b - 1) →
      Arxiv2005_04287.burrDensity b lam A <
        Arxiv2005_04287.burrDensity b lam (lam / Real.sqrt (2 * b - 1)) :=
  fun A hA => S69B.mode b lam hb hlam A hA
