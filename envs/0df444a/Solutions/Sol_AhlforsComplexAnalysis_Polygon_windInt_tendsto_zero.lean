-- Prove2me | solution 1 for AhlforsComplexAnalysis.Polygon.windInt_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T12:37:16.2421+00:00
-- url     : https://prove2.me/submissions/66e4cd75-93a9-4da8-a0dd-006744865d10

import Mathlib
import Definitions.Def_AhlforsComplexAnalysis_Polygon

set_option autoImplicit false

open Set Complex Topology Filter

namespace AhlforsComplexAnalysis.Polygon

open scoped Interval

/-- Points of the form `p + t (q - p)` with `t ∈ [0, 1]` lie on the segment. -/
lemma w3_mem_segment {p q : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p + (t : ℂ) * (q - p) ∈ segment ℝ p q := by
  rw [segment_eq_image']
  exact ⟨t, ht, by simp [Complex.real_smul]⟩

/-- Crude bound for a segment integral. -/
lemma w3_segInt_norm_le {g : ℂ → ℂ} {p q : ℂ} {C : ℝ}
    (hg : ∀ w ∈ segment ℝ p q, ‖g w‖ ≤ C) : ‖segInt g p q‖ ≤ ‖q - p‖ * C := by
  have hIoc : Ι (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [Set.uIoc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  have h : ∀ t ∈ Ι (0 : ℝ) 1, ‖g (p + (t : ℂ) * (q - p)) * (q - p)‖ ≤ C * ‖q - p‖ := by
    intro t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hg _ (w3_mem_segment (hIoc ht))) (norm_nonneg _)
  have h' := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) h
  rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at h'
  unfold segInt
  linarith [mul_comm C ‖q - p‖]

/-- Decay of `windInt l` away from a ball containing the trace. -/
lemma w3_norm_le : ∀ (l : List ℂ), ∃ L : ℝ, 0 ≤ L ∧ ∀ (R : ℝ) (b : ℂ),
    (∀ z ∈ polyTrace l, ‖z‖ ≤ R) → R < ‖b‖ → ‖windInt l b‖ ≤ L / (‖b‖ - R)
  | [] => ⟨0, le_rfl, fun R b _ _ => by simp [windInt, polyInt]⟩
  | [x] => ⟨0, le_rfl, fun R b _ _ => by simp [windInt, polyInt]⟩
  | p :: q :: rest => by
      obtain ⟨L, hL, hbound⟩ := w3_norm_le (q :: rest)
      refine ⟨‖q - p‖ + L, add_nonneg (norm_nonneg _) hL, fun R b hR hb => ?_⟩
      have hpos : 0 < ‖b‖ - R := sub_pos.mpr hb
      have h1 : ∀ w ∈ segment ℝ p q, ‖(w - b)⁻¹‖ ≤ 1 / (‖b‖ - R) := by
        intro w hw
        have hwR : ‖w‖ ≤ R := hR w (Or.inl hw)
        have hle : ‖b‖ - R ≤ ‖w - b‖ := by
          have := norm_sub_norm_le b w
          rw [norm_sub_rev] at this
          linarith
        rw [norm_inv, one_div]
        exact inv_anti₀ hpos hle
      have h2 := w3_segInt_norm_le h1
      have h3 := hbound R b (fun z hz => hR z (Or.inr hz)) hb
      have hsplit : windInt (p :: q :: rest) b =
          segInt (fun z => (z - b)⁻¹) p q + windInt (q :: rest) b := rfl
      rw [hsplit]
      calc ‖segInt (fun z => (z - b)⁻¹) p q + windInt (q :: rest) b‖
          ≤ ‖segInt (fun z => (z - b)⁻¹) p q‖ + ‖windInt (q :: rest) b‖ := norm_add_le _ _
        _ ≤ ‖q - p‖ * (1 / (‖b‖ - R)) + L / (‖b‖ - R) := add_le_add h2 h3
        _ = (‖q - p‖ + L) / (‖b‖ - R) := by ring

end AhlforsComplexAnalysis.Polygon

open AhlforsComplexAnalysis.Polygon

theorem solution (l : List ℂ) : Tendsto (windInt l) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨L, hL, hbound⟩ := w3_norm_le l
  obtain ⟨R, hR⟩ := (polyTrace_isCompact l).isBounded.exists_norm_le
  have hev : ∀ᶠ b in cocompact ℂ, R < ‖b‖ :=
    tendsto_norm_cocompact_atTop.eventually_gt_atTop R
  have hlim : Tendsto (fun b : ℂ => L / (‖b‖ - R)) (cocompact ℂ) (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right (cocompact ℂ) (-R) tendsto_norm_cocompact_atTop
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hev] with b hb using hbound R b hR hb

#print axioms solution
