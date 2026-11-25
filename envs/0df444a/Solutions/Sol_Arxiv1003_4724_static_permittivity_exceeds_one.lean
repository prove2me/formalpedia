-- Prove2me | solution 1 for Arxiv1003_4724.static_permittivity_exceeds_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T15:57:38.0148+00:00
-- url     : https://prove2.me/submissions/e1e1a1f5-4c6f-415f-b6d1-0cd1e2906799

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology
namespace Arxiv1003_4724

lemma tc_herm {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (ω : A →ₗ[ℂ] ℂ) (hω : IsState ω) (Y : A) : ω (star Y) = star (ω Y) := by
  obtain ⟨-, hpos⟩ := hω
  have h1 := (hpos (1 + Y)).1
  have h2 := (hpos (1 + Complex.I • Y)).1
  have e1 : star (1 + Y) * (1 + Y) = 1 + Y + star Y + star Y * Y := by
    simp [star_add, star_one, add_mul, mul_add]; abel
  have e2 : star (1 + Complex.I • Y) * (1 + Complex.I • Y) =
      1 + Complex.I • Y - Complex.I • star Y + star Y * Y := by
    simp [star_add, star_one, add_mul, mul_add, star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    abel
  rw [e1, map_add, map_add, map_add] at h1
  rw [e2, map_add, map_sub, map_add, map_smul, map_smul] at h2
  have h0 := (hpos 1).1
  have h3 := (hpos Y).1
  simp only [star_one, one_mul] at h0
  simp only [Complex.add_im, Complex.sub_im, smul_eq_mul, Complex.mul_im, Complex.I_re,
    Complex.I_im] at h1 h2
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]; linarith
  · simp only [Complex.star_def, Complex.conj_im]; linarith


theorem static_permittivity_exceeds_one {A ι : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι]
    (ω : A →ₗ[ℂ] ℂ) (hω : IsState ω) (N : ι → A) (hN : ∀ a, IsSelfAdjoint (N a))
    (hNc : ∀ a b, Commute (N a) (N b)) (z : ι → ℝ) (e T V : ℝ) (he : 0 < e) (hT : 0 < T)
    (hV : 0 < V) (h3 : IsQuasiNeutral ω N z e V) (epsStatic : ℝ → ℝ) (D : ι → ι → ℝ)
    (h18 : Tendsto (fun q => q ^ 2 * epsStatic q) (𝓝[>] (0 : ℝ))
      (𝓝 (4 * Real.pi * ∑ a, ∑ b, z a * z b * e ^ 2 * D a b)))
    (h22 : ∀ a b, ((T * D a b : ℝ) : ℂ) = numberCov ω N a b / V)
    (hZ : 0 < (ω (totalCharge N z e * totalCharge N z e)).re) :
    ∃ δ > 0, ∀ q : ℝ, 0 < q → q < δ → 1 < epsStatic q  := by
  have hreal : ∀ a, ω (N a) = (((ω (N a)).re : ℝ) : ℂ) := by
    intro a
    have h := tc_herm ω hω (N a)
    rw [(hN a).star_eq] at h
    apply Complex.ext
    · simp
    · have := congrArg Complex.im h
      simp only [Complex.star_def, Complex.conj_im] at this
      simp; linarith
  have hcov : ∀ a b, numberCov ω N a b = ω (N a * N b) - ω (N a) * ω (N b) := by
    intro a b
    unfold numberCov
    simp only [sub_mul, mul_sub, map_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      map_smul, smul_eq_mul, smul_one_smul, hω.1]
    ring
  have hcovre : ∀ a b, (numberCov ω N a b).re =
      (ω (N a * N b)).re - (ω (N a)).re * (ω (N b)).re := by
    intro a b
    rw [hcov, Complex.sub_re, Complex.mul_re, hreal a, hreal b]
    simp
  have hQQre : (ω (totalCharge N z e * totalCharge N z e)).re =
      ∑ a, ∑ b, (z a * e) * (z b * e) * (ω (N a * N b)).re := by
    unfold totalCharge
    rw [Finset.sum_mul, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_smul_comm, map_smul, smul_eq_mul]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    push_cast
    simp [Complex.mul_re]
  have hsum0 : ∑ a, z a * e * (ω (N a)).re = 0 := by
    have := h3
    unfold IsQuasiNeutral meanDensity at this
    have e2 : ∑ a, z a * e * (ω (N a)).re = V * ∑ a, e * z a * ((ω (N a)).re / V) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      field_simp
    rw [e2, this, mul_zero]
  have hD : ∀ a b, D a b = (numberCov ω N a b).re / (T * V) := by
    intro a b
    have := congrArg Complex.re (h22 a b)
    rw [Complex.div_ofReal_re, Complex.ofReal_re] at this
    rw [eq_div_iff (by positivity)]
    rw [eq_div_iff hV.ne'] at this
    linear_combination this
  have hS : ∑ a, ∑ b, z a * z b * e ^ 2 * D a b =
      (ω (totalCharge N z e * totalCharge N z e)).re / (T * V) := by
    have : (ω (totalCharge N z e * totalCharge N z e)).re =
        (ω (totalCharge N z e * totalCharge N z e)).re -
          (∑ a, z a * e * (ω (N a)).re) * (∑ b, z b * e * (ω (N b)).re) := by
      rw [hsum0]; ring
    rw [this, hQQre, Finset.sum_mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hD, hcovre]
    ring
  set L := 4 * Real.pi * ∑ a, ∑ b, z a * z b * e ^ 2 * D a b with hL
  have hLpos : 0 < L := by
    rw [hL, hS]
    have := Real.pi_pos
    positivity
  have hq2 : Tendsto (fun q : ℝ => q ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun q : ℝ => q ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ q in 𝓝[>] (0 : ℝ), L / 2 < q ^ 2 * epsStatic q ∧ q ^ 2 < L / 2 := by
    have h1 := h18.eventually (lt_mem_nhds (show L / 2 < L by linarith))
    have h2 := hq2.eventually (gt_mem_nhds (show (0 : ℝ) < L / 2 by linarith))
    exact h1.and h2
  obtain ⟨δ, hδ, hsub⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
  refine ⟨δ, hδ, fun q hq hqδ => ?_⟩
  obtain ⟨h1, h2⟩ := hsub ⟨hq, hqδ⟩
  by_contra hcon
  push Not at hcon
  have : q ^ 2 * epsStatic q ≤ q ^ 2 * 1 := mul_le_mul_of_nonneg_left hcon (by positivity)
  linarith

end Arxiv1003_4724
open Arxiv1003_4724 in
theorem solution {A ι : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι]
    (ω : A →ₗ[ℂ] ℂ) (hω : IsState ω) (N : ι → A) (hN : ∀ a, IsSelfAdjoint (N a))
    (hNc : ∀ a b, Commute (N a) (N b)) (z : ι → ℝ) (e T V : ℝ) (he : 0 < e) (hT : 0 < T)
    (hV : 0 < V) (h3 : IsQuasiNeutral ω N z e V) (epsStatic : ℝ → ℝ) (D : ι → ι → ℝ)
    (h18 : Tendsto (fun q => q ^ 2 * epsStatic q) (𝓝[>] (0 : ℝ))
      (𝓝 (4 * Real.pi * ∑ a, ∑ b, z a * z b * e ^ 2 * D a b)))
    (h22 : ∀ a b, ((T * D a b : ℝ) : ℂ) = numberCov ω N a b / V)
    (hZ : 0 < (ω (totalCharge N z e * totalCharge N z e)).re) :
    ∃ δ > 0, ∀ q : ℝ, 0 < q → q < δ → 1 < epsStatic q :=
  static_permittivity_exceeds_one ω hω N hN hNc z e T V he hT hV h3 epsStatic D h18 h22 hZ
