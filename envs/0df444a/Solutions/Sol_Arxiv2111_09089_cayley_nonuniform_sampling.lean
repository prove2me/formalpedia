-- Prove2me | solution 1 for Arxiv2111_09089.cayley_nonuniform_sampling
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:10:58.020234+00:00
-- url     : https://prove2.me/submissions/3deeacb5-4ddc-480e-a32f-cab31040b743

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Filter Topology Complex
open Arxiv2111_09089

lemma sin_half_pos {φ : ℝ} (h : φ ∈ Set.Ioo 0 (2 * Real.pi)) : 0 < Real.sin (φ / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2])

lemma cayley_circle {φ : ℝ} (h : φ ∈ Set.Ioo 0 (2 * Real.pi)) :
    cayley (exp ((φ : ℂ) * I)) = (Real.cot (φ / 2) : ℂ) := by
  have hs := sin_half_pos h
  set u := exp (((φ / 2 : ℝ) : ℂ) * I) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have he : exp ((φ : ℂ) * I) = u * u := by
    rw [hu, ← Complex.exp_add]; congr 1; push_cast; ring
  have hinv : exp (-(((φ / 2 : ℝ) : ℂ) * I)) = u⁻¹ := by rw [Complex.exp_neg]
  have hcos : Complex.cos ((φ / 2 : ℝ) : ℂ) = (u + u⁻¹) / 2 := by
    rw [Complex.cos, ← hu, ← hinv]; ring_nf
  have hsin : Complex.sin ((φ / 2 : ℝ) : ℂ) = (u⁻¹ - u) * I / 2 := by
    rw [Complex.sin, ← hu, ← hinv]; ring_nf
  have hsC : Complex.sin ((φ / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sin]; exact_mod_cast hs.ne'
  have hd : u⁻¹ - u ≠ 0 := by
    intro h0; apply hsC; rw [hsin, h0]; ring
  have h1 : 1 - u * u ≠ 0 := by
    intro h0; apply hd
    have : u⁻¹ = u := by
      field_simp; linear_combination h0
    rw [this, sub_self]
  rw [Complex.ofReal_cot, Complex.cot_eq_cos_div_sin, hcos, hsin, he]
  unfold cayley
  rw [div_eq_div_iff h1 (by
    intro h0; apply hsC; rw [hsin]; linear_combination h0)]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma hasDeriv_cot_half {φ : ℝ} (h : φ ∈ Set.Ioo 0 (2 * Real.pi)) :
    HasDerivAt (fun ψ : ℝ => Real.cot (ψ / 2)) (-(1 + Real.cot (φ / 2) ^ 2) / 2) φ := by
  have hs := (sin_half_pos h).ne'
  have hc : HasDerivAt (fun ψ : ℝ => Real.cos (ψ / 2)) (-Real.sin (φ / 2) * (1 / 2)) φ := by
    have := ((hasDerivAt_id φ).div_const 2).cos
    simpa using this
  have hsn : HasDerivAt (fun ψ : ℝ => Real.sin (ψ / 2)) (Real.cos (φ / 2) * (1 / 2)) φ := by
    have := ((hasDerivAt_id φ).div_const 2).sin
    simpa using this
  have hq := hc.div hsn hs
  have hfun : (fun ψ : ℝ => Real.cot (ψ / 2)) = fun ψ => Real.cos (ψ / 2) / Real.sin (ψ / 2) := by
    funext ψ; rw [Real.cot_eq_cos_div_sin]
  rw [hfun]
  refine hq.congr_deriv ?_
  rw [Real.cot_eq_cos_div_sin]
  field_simp
  ring

theorem solution :
    (∀ φ ∈ Set.Ioo 0 (2 * Real.pi), cayley (exp ((φ : ℂ) * I)) = (Real.cot (φ / 2) : ℂ)) ∧
    StrictAntiOn (fun φ : ℝ => Real.cot (φ / 2)) (Set.Ioo 0 (2 * Real.pi)) ∧
    Tendsto (fun φ : ℝ => Real.cot (φ / 2)) (𝓝[>] 0) atTop ∧
    Tendsto (fun φ : ℝ => Real.cot (φ / 2)) (𝓝[<] (2 * Real.pi)) atBot ∧
    ∀ φ ∈ Set.Ioo 0 (2 * Real.pi),
      HasDerivAt (fun ψ : ℝ => Real.cot (ψ / 2)) (-(1 + Real.cot (φ / 2) ^ 2) / 2) φ := by
  have hpi := Real.pi_pos
  have hfun : (fun ψ : ℝ => Real.cot (ψ / 2)) = fun ψ => Real.cos (ψ / 2) * (Real.sin (ψ / 2))⁻¹ := by
    funext ψ; rw [Real.cot_eq_cos_div_sin, div_eq_mul_inv]
  refine ⟨fun φ h => cayley_circle h, ?_, ?_, ?_, fun φ h => hasDeriv_cot_half h⟩
  · apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (2 * Real.pi))
    · exact fun φ h => (hasDeriv_cot_half h).continuousAt.continuousWithinAt
    · intro φ h
      rw [interior_Ioo] at h
      rw [(hasDeriv_cot_half h).deriv]
      have := sq_nonneg (Real.cot (φ / 2))
      linarith
  · rw [hfun]
    have hsin : Tendsto (fun ψ : ℝ => Real.sin (ψ / 2)) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · apply tendsto_nhdsWithin_of_tendsto_nhds
        have : Continuous (fun ψ : ℝ => Real.sin (ψ / 2)) := by fun_prop
        simpa using this.tendsto 0
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * Real.pi by positivity)] with ψ hψ
        exact sin_half_pos hψ
    have hcos : Tendsto (fun ψ : ℝ => Real.cos (ψ / 2)) (𝓝[>] 0) (𝓝 1) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun ψ : ℝ => Real.cos (ψ / 2)) := by fun_prop
      simpa using this.tendsto 0
    exact hcos.pos_mul_atTop one_pos (tendsto_inv_nhdsGT_zero.comp hsin)
  · rw [hfun]
    have hsin : Tendsto (fun ψ : ℝ => Real.sin (ψ / 2)) (𝓝[<] (2 * Real.pi)) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · apply tendsto_nhdsWithin_of_tendsto_nhds
        have : Continuous (fun ψ : ℝ => Real.sin (ψ / 2)) := by fun_prop
        have h2 := this.tendsto (2 * Real.pi)
        simpa [mul_div_cancel_left₀] using h2
      · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 2 * Real.pi by positivity)] with ψ hψ
        exact sin_half_pos hψ
    have hcos : Tendsto (fun ψ : ℝ => Real.cos (ψ / 2)) (𝓝[<] (2 * Real.pi)) (𝓝 (-1)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun ψ : ℝ => Real.cos (ψ / 2)) := by fun_prop
      have h2 := this.tendsto (2 * Real.pi)
      simpa [mul_div_cancel_left₀] using h2
    exact hcos.neg_mul_atTop (by norm_num) (tendsto_inv_nhdsGT_zero.comp hsin)

