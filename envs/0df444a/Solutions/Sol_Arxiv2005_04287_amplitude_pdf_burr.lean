-- Prove2me | solution 1 for Arxiv2005_04287.amplitude_pdf_burr
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:33:25.791249+00:00
-- url     : https://prove2.me/submissions/e22dc037-22ee-40bd-9da5-4beaf5cbda8f

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

set_option autoImplicit false

open MeasureTheory Set

namespace S78AP
open Arxiv2005_04287

lemma restr_ioi (g : ℝ → ENNReal) (c : ℝ) (hg : ∀ x, x ≤ c → g x = 0) (s : Set ℝ) :
    ∫⁻ x in s, g x = ∫⁻ x in s ∩ Ioi c, g x := by
  have : g = (Ioi c).indicator g := by
    funext x; by_cases hx : c < x
    · simp [indicator_of_mem (show x ∈ Ioi c from hx)]
    · rw [indicator_of_notMem (show x ∉ Ioi c from hx), hg x (not_lt.1 hx)]
  conv_lhs => rw [this]
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_comm]

lemma part1 (b amin A0 : ℝ) (hamin : 0 < amin) (hA0 : 0 < A0) :
    (powerLawMeasure b amin).map (ampMap A0 amin) =
      volume.withDensity (fun A => ENNReal.ofReal (ampDensity9 b amin A0 A)) := by
  have hfm : Measurable (ampMap A0 amin) := by
    unfold ampMap
    exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ψ = fun A => (A / A0) ^ 2 + amin := ⟨_, rfl⟩
  ext t ht
  rw [Measure.map_apply hfm ht, powerLawMeasure, withDensity_apply _ (hfm ht), withDensity_apply _ ht]
  rw [restr_ioi _ amin (fun x hx => by simp [powerLawDensity, not_lt.2 hx]) _]
  rw [restr_ioi (fun A => ENNReal.ofReal (ampDensity9 b amin A0 A)) 0 (fun x hx => by simp [ampDensity9, not_lt.2 hx]) t]
  have hmeas : MeasurableSet (t ∩ Ioi 0) := ht.inter measurableSet_Ioi
  have himg : ampMap A0 amin ⁻¹' t ∩ Ioi amin = ψ '' (t ∩ Ioi 0) := by
    ext a; simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_image, ampMap, hψ]
    constructor
    · rintro ⟨h1, h2⟩
      rw [if_pos h2] at h1
      have hs : 0 < Real.sqrt (a - amin) := Real.sqrt_pos.2 (by linarith)
      refine ⟨A0 * Real.sqrt (a - amin), ⟨h1, mul_pos hA0 hs⟩, ?_⟩
      rw [mul_div_cancel_left₀ _ hA0.ne', Real.sq_sqrt (by linarith)]; ring
    · rintro ⟨A, ⟨h1, h2⟩, rfl⟩
      have hp : 0 < (A / A0) ^ 2 := by positivity
      refine ⟨?_, by linarith⟩
      rw [if_pos (by linarith), add_sub_cancel_right, Real.sqrt_sq (div_pos h2 hA0).le,
        mul_div_cancel₀ _ hA0.ne']
      exact h1
  rw [himg, lintegral_image_eq_lintegral_abs_deriv_mul hmeas (f' := fun A => 2 * A / A0 ^ 2)]
  · refine setLIntegral_congr_fun hmeas ?_
    intro A hA
    have hA' : 0 < A := hA.2
    have hp : 0 < (A / A0) ^ 2 := by positivity
    have hψp : amin < ψ A := by rw [hψ]; linarith
    have hψ0 : 0 < ψ A := by linarith
    simp only [powerLawDensity, ampDensity9, if_pos hA', if_pos hψp,
      abs_of_pos (show 0 < 2 * A / A0 ^ 2 by positivity)]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hq : (A / A0) ^ 2 + amin = ψ A := by rw [hψ]
    rw [hq, Real.div_rpow hψ0.le hamin.le, Real.rpow_neg hψ0.le, Real.rpow_neg hamin.le,
      Real.rpow_sub hamin, Real.rpow_one]
    have h1 : 0 < amin ^ b := Real.rpow_pos_of_pos hamin b
    have h2 : 0 < ψ A ^ b := Real.rpow_pos_of_pos hψ0 b
    field_simp
  · intro x _
    rw [hψ]
    refine (((hasDerivAt_id x).div_const A0 |>.pow 2 |>.add_const amin).hasDerivWithinAt).congr_deriv ?_
    simp; field_simp
  · intro x hx y hy hxy
    simp only [hψ, add_left_inj] at hxy
    have := (pow_left_inj₀ (div_pos hx.2 hA0).le (div_pos hy.2 hA0).le two_ne_zero).1 hxy
    field_simp at this; linarith

end S78AP

open Arxiv2005_04287 in
theorem solution (b amin A0 : ℝ) (hb : 1 < b) (hamin : 0 < amin) (hA0 : 0 < A0) :
    (powerLawMeasure b amin).map (ampMap A0 amin) =
      volume.withDensity (fun A => ENNReal.ofReal (ampDensity9 b amin A0 A)) ∧
    (∀ A : ℝ, ampDensity9 b amin A0 A = burrDensity b (A0 * Real.sqrt amin) A) ∧
    (∀ A : ℝ, burrDensity b (A0 * Real.sqrt amin) A =
      burrXIIDensity 2 (b - 1) (A0 * Real.sqrt amin) A) := by
  have hsq : 0 < Real.sqrt amin := Real.sqrt_pos.2 hamin
  have hl2 : (A0 * Real.sqrt amin) ^ 2 = A0 ^ 2 * amin := by
    rw [mul_pow, Real.sq_sqrt hamin.le]
  refine ⟨S78AP.part1 b amin A0 hamin hA0, ?_, ?_⟩
  · intro A
    unfold ampDensity9 burrDensity
    split_ifs with hA
    · have he : (A / (A0 * Real.sqrt amin)) ^ 2 + 1 = ((A / A0) ^ 2 + amin) / amin := by
        rw [div_pow, hl2]; field_simp
      have hs : 0 < (A / A0) ^ 2 + amin := by positivity
      rw [he, Real.div_rpow hs.le hamin.le, hl2]
      simp only [Real.rpow_sub hamin, Real.rpow_one]
      have h1 : 0 < amin ^ b := Real.rpow_pos_of_pos hamin b
      have h3 : 0 < ((A / A0) ^ 2 + amin) ^ b := Real.rpow_pos_of_pos hs b
      field_simp
    · rfl
  · intro A
    unfold burrDensity burrXIIDensity
    split_ifs with hA
    · have hl : 0 < A0 * Real.sqrt amin := mul_pos hA0 hsq
      have h21 : ((2 : ℝ) - 1) = 1 := by norm_num
      rw [h21, Real.rpow_one, Real.rpow_two, show -(b - 1 + 1) = -b by ring,
        Real.rpow_neg (by positivity)]
      have h3 : 0 < (1 + (A / (A0 * Real.sqrt amin)) ^ 2) ^ b := Real.rpow_pos_of_pos (by positivity) b
      rw [add_comm (1 : ℝ)]
      field_simp
    · rfl
