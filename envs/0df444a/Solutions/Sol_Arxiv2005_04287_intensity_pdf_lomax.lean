-- Prove2me | solution 1 for Arxiv2005_04287.intensity_pdf_lomax
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:29:34.790854+00:00
-- url     : https://prove2.me/submissions/22bf5f4c-813c-4b06-b930-50ba1bd527d3

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

set_option autoImplicit false

open MeasureTheory Set

namespace S78IL
open Arxiv2005_04287

lemma restr_ioi (g : ℝ → ENNReal) (c : ℝ) (hg : ∀ x, x ≤ c → g x = 0) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫⁻ x in s, g x = ∫⁻ x in s ∩ Ioi c, g x := by
  have : g = (Ioi c).indicator g := by
    funext x; by_cases hx : c < x
    · simp [indicator_of_mem (show x ∈ Ioi c from hx)]
    · rw [indicator_of_notMem (show x ∉ Ioi c from hx), hg x (not_lt.1 hx)]
  conv_lhs => rw [this]
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_comm]

lemma part1 (b amin I0 : ℝ) (hb : 1 < b) (hamin : 0 < amin) (hI0 : 0 < I0) :
    (powerLawMeasure b amin).map (intensityMap I0 amin) =
      volume.withDensity (fun I => ENNReal.ofReal (intensityDensity13 b amin I0 I)) := by
  have hfm : Measurable (intensityMap I0 amin) := by
    unfold intensityMap
    exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  set φ : ℝ → ℝ := fun a => I0 * (a - amin) with hφ
  ext t ht
  rw [Measure.map_apply hfm ht, powerLawMeasure, withDensity_apply _ (hfm ht), withDensity_apply _ ht]
  rw [restr_ioi _ amin (fun x hx => by simp [powerLawDensity, not_lt.2 hx]) _ (hfm ht)]
  rw [restr_ioi _ 0 (fun x hx => by simp [intensityDensity13, not_lt.2 hx]) _ ht]
  have hset : intensityMap I0 amin ⁻¹' t ∩ Ioi amin = φ ⁻¹' t ∩ Ioi amin := by
    ext a; simp only [mem_inter_iff, mem_preimage, mem_Ioi, intensityMap]
    constructor
    · rintro ⟨h1, h2⟩; rw [if_pos h2] at h1; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; rw [if_pos h2]; exact ⟨h1, h2⟩
  have himg : t ∩ Ioi 0 = φ '' (φ ⁻¹' t ∩ Ioi amin) := by
    ext x; simp only [mem_inter_iff, mem_Ioi, mem_image, mem_preimage, hφ]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨x / I0 + amin, ⟨?_, ?_⟩, ?_⟩
      · convert h1 using 1; field_simp; ring
      · have := div_pos h2 hI0; linarith
      · field_simp; ring
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1, mul_pos hI0 (by linarith)⟩
  have hmeas : MeasurableSet (φ ⁻¹' t ∩ Ioi amin) :=
    ((show Measurable φ by fun_prop) ht).inter measurableSet_Ioi
  rw [hset, himg, lintegral_image_eq_lintegral_abs_deriv_mul hmeas (f' := fun _ => I0)]
  · refine setLIntegral_congr_fun hmeas ?_
    intro a ha
    have ha' : amin < a := ha.2
    have hpos : 0 < φ a := mul_pos hI0 (by linarith)
    simp only [powerLawDensity, intensityDensity13, if_pos ha', if_pos hpos, abs_of_pos hI0]
    rw [← ENNReal.ofReal_mul hI0.le]
    congr 1
    have ha0 : 0 < a := by linarith
    have hq : φ a / I0 + amin = a := by simp only [hφ]; field_simp; ring
    rw [hq, Real.div_rpow ha0.le hamin.le, Real.rpow_neg ha0.le, Real.rpow_neg hamin.le,
      Real.rpow_sub hamin, Real.rpow_one]
    have h1 : 0 < amin ^ b := Real.rpow_pos_of_pos hamin b
    have h2 : 0 < a ^ b := Real.rpow_pos_of_pos ha0 b
    field_simp
  · intro x _
    exact ((hasDerivAt_id x).sub_const amin |>.const_mul I0 |>.hasDerivWithinAt).congr_deriv (by simp)
  · intro x _ y _ hxy
    have := mul_left_cancel₀ hI0.ne' hxy
    linarith

end S78IL

open Arxiv2005_04287 in
theorem solution (b amin I0 : ℝ) (hb : 1 < b) (hamin : 0 < amin) (hI0 : 0 < I0) :
    (powerLawMeasure b amin).map (intensityMap I0 amin) =
      volume.withDensity (fun I => ENNReal.ofReal (intensityDensity13 b amin I0 I)) ∧
    (∀ I : ℝ, intensityDensity13 b amin I0 I = intensityDensity14 b (I0 * amin) I) ∧
    (∀ I : ℝ, intensityDensity14 b (I0 * amin) I = lomaxDensity (b - 1) (I0 * amin) I) := by
  refine ⟨S78IL.part1 b amin I0 hb hamin hI0, ?_, ?_⟩
  · intro I
    unfold intensityDensity13 intensityDensity14
    split_ifs with hI
    · have hs : 0 < I / I0 + amin := by have := div_pos hI hI0; linarith
      have he : I + I0 * amin = I0 * (I / I0 + amin) := by field_simp
      rw [he, Real.mul_rpow hI0.le hs.le, Real.mul_rpow hI0.le hamin.le]
      simp only [Real.rpow_sub hamin, Real.rpow_sub hI0, Real.rpow_one]
      have h1 : 0 < amin ^ b := Real.rpow_pos_of_pos hamin b
      have h2 : 0 < I0 ^ b := Real.rpow_pos_of_pos hI0 b
      have h3 : 0 < (I / I0 + amin) ^ b := Real.rpow_pos_of_pos hs b
      field_simp
    · rfl
  · intro I
    unfold intensityDensity14 lomaxDensity
    split_ifs with hI
    · have hl : 0 < I0 * amin := mul_pos hI0 hamin
      have he : 1 + I / (I0 * amin) = (I + I0 * amin) / (I0 * amin) := by field_simp; ring
      rw [he, show -(b - 1 + 1) = -b by ring, Real.rpow_neg (by positivity),
        Real.div_rpow (by positivity) hl.le, Real.rpow_sub hl, Real.rpow_one]
      have h1 : 0 < (I0 * amin) ^ b := Real.rpow_pos_of_pos hl b
      have h3 : 0 < (I + I0 * amin) ^ b := Real.rpow_pos_of_pos (by positivity) b
      field_simp
    · rfl
