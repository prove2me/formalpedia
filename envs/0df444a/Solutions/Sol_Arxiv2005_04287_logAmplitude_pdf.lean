-- Prove2me | solution 1 for Arxiv2005_04287.logAmplitude_pdf
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:30:59.224981+00:00
-- url     : https://prove2.me/submissions/cfc75cf9-5eb3-47f1-9a42-06072c8434f6

import Mathlib
import Definitions.Def_Arxiv2005_04287_Basic

set_option autoImplicit false

open MeasureTheory Set

namespace S78LA
open Arxiv2005_04287

lemma restr_ioi (g : ℝ → ENNReal) (c : ℝ) (hg : ∀ x, x ≤ c → g x = 0) (s : Set ℝ) :
    ∫⁻ x in s, g x = ∫⁻ x in s ∩ Ioi c, g x := by
  have : g = (Ioi c).indicator g := by
    funext x; by_cases hx : c < x
    · simp [indicator_of_mem (show x ∈ Ioi c from hx)]
    · rw [indicator_of_notMem (show x ∉ Ioi c from hx), hg x (not_lt.1 hx)]
  conv_lhs => rw [this]
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, inter_comm]

end S78LA

open Arxiv2005_04287 in
theorem solution (b lam : ℝ) (hb : 1 < b) (hlam : 0 < lam) :
    (burrMeasure b lam).map Real.log = logAmpMeasure b lam := by
  ext t ht
  rw [Measure.map_apply Real.measurable_log ht, burrMeasure, logAmpMeasure,
    withDensity_apply _ (Real.measurable_log ht), withDensity_apply _ ht,
    S78LA.restr_ioi _ 0 (fun x hx => by simp [burrDensity, not_lt.2 hx])]
  have himg : Real.log ⁻¹' t ∩ Ioi 0 = Real.exp '' t := by
    ext x; simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_image]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Real.log x, h1, Real.exp_log h2⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨by rwa [Real.log_exp], Real.exp_pos y⟩
  rw [himg, lintegral_image_eq_lintegral_abs_deriv_mul ht (f' := Real.exp)]
  · refine setLIntegral_congr_fun ht ?_
    intro y _
    have he := Real.exp_pos y
    simp only [burrDensity, logAmpDensity, if_pos he, abs_of_pos he]
    rw [← ENNReal.ofReal_mul he.le]
    congr 1
    have h2 : Real.exp (2 * y) = Real.exp y ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h2]; field_simp
  · intro x _; exact (Real.hasDerivAt_exp x).hasDerivWithinAt
  · exact Real.exp_injective.injOn
