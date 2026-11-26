-- Prove2me | solution 1 for Arxiv1811_00800.eq4_vortex_phase_topological
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T08:35:18.575907+00:00
-- url     : https://prove2.me/submissions/6bccc9cd-48a3-4912-88c5-5fb6dffd480b

import Mathlib
import Definitions.Def_Arxiv1811_00800_Basic

open MeasureTheory Complex Set Filter Topology intervalIntegral
open scoped Interval

noncomputable section
namespace VX
open Arxiv1811_00800

lemma ae_ne1 (c : ℝ) : ∀ᵐ x : ℝ, x ≠ c := by
  have : ({c}ᶜ : Set ℝ) ∈ ae volume := compl_mem_ae_iff.2 (measure_singleton c)
  filter_upwards [this] with x hx
  simpa using hx

lemma wind (γ : ℝ → ℂ) (K : NNReal) (hK : LipschitzOnWith K γ (Icc 0 1)) (h01 : γ 0 = γ 1)
    (h0 : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) :
    IntervalIntegrable (fun t => deriv γ t / γ t) volume 0 1 ∧
    ∃ n : ℤ, ∫ t in (0 : ℝ)..1, deriv γ t / γ t = n * (2 * Real.pi * I) := by
  have hcont : ContinuousOn γ (Icc 0 1) := hK.continuousOn
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
    (continuous_norm.comp_continuousOn hcont)
  set m := ‖γ t0‖ with hm
  have mpos : 0 < m := norm_pos_iff.2 (h0 t0 ht0)
  have hmle : ∀ t ∈ Icc (0:ℝ) 1, m ≤ ‖γ t‖ := fun t ht => hmin ht
  set g : ℝ → ℂ := fun t => deriv γ t / γ t with hg
  set C : ℝ := K / m
  have hbd0 : ∀ t ∈ Ioo (0:ℝ) 1, ‖g t‖ ≤ C := by
    intro t ht
    have h1 : ‖deriv γ t‖ ≤ K := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hK
    have h2 := hmle t (Ioo_subset_Icc_self ht)
    simp only [g, norm_div]
    exact div_le_div₀ (NNReal.coe_nonneg K) h1 mpos h2
  have hbd : ∀ᵐ x : ℝ, x ∈ Ioc (0:ℝ) 1 → ‖g x‖ ≤ C := by
    filter_upwards [ae_ne1 1] with x hx hmem
    exact hbd0 x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
  have hmeas : AEStronglyMeasurable g (volume.restrict (Ioc (0:ℝ) 1)) := by
    have a1 : AEStronglyMeasurable (deriv γ) (volume.restrict (Ioc (0:ℝ) 1)) :=
      (measurable_deriv γ).aestronglyMeasurable
    have a2 : AEStronglyMeasurable γ (volume.restrict (Ioc (0:ℝ) 1)) :=
      (hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    exact (a1.aemeasurable.div a2.aemeasurable).aestronglyMeasurable
  have hint : IntervalIntegrable g volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have : IsFiniteMeasure (volume.restrict (Ioc (0:ℝ) 1)) := isFiniteMeasure_restrict.2 (by simp)
    exact Integrable.of_bound hmeas C (by rw [ae_restrict_iff' measurableSet_Ioc]; exact hbd)
  refine ⟨hint, ?_⟩
  set L : ℝ → ℂ := fun t => ∫ s in (0:ℝ)..t, g s with hL
  have hsub : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, Ι s t ⊆ Ioc 0 1 := by
    intro s hs t ht x hx
    rcases hx with ⟨h1, h2⟩
    exact ⟨lt_of_le_of_lt (le_min hs.1 ht.1) h1, h2.trans (max_le hs.2 ht.2)⟩
  have hii : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, IntervalIntegrable g volume s t := by
    intro s hs t ht
    exact hint.mono_set (by rw [uIcc_of_le zero_le_one]; exact uIcc_subset_Icc hs ht)
  have hLlip : LipschitzOnWith (Real.toNNReal C) L (Icc 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs
    rw [dist_eq_norm, hL]
    simp only
    rw [integral_interval_sub_left (hii 0 ⟨le_rfl, zero_le_one⟩ t ht) (hii 0 ⟨le_rfl, zero_le_one⟩ s hs)]
    have := norm_integral_le_of_norm_le_const_ae (a := s) (b := t) (C := C) (f := g) (by
      filter_upwards [hbd] with x hx hmem
      exact hx (hsub s hs t ht hmem))
    rw [Real.coe_toNNReal _ (div_nonneg (NNReal.coe_nonneg K) mpos.le), Real.dist_eq]
    exact this
  have hLb : ∀ t ∈ Icc (0:ℝ) 1, ‖-L t‖ ≤ C := by
    intro t ht
    rw [norm_neg]
    have := norm_integral_le_of_norm_le_const_ae (a := 0) (b := t) (C := C) (f := g) (by
      filter_upwards [hbd] with x hx hmem
      exact hx (hsub 0 ⟨le_rfl, zero_le_one⟩ t ht hmem))
    calc ‖L t‖ ≤ C * |t - 0| := this
      _ ≤ C * 1 := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (NNReal.coe_nonneg K) mpos.le)
        rw [sub_zero, abs_of_nonneg ht.1]; exact ht.2
      _ = C := mul_one C
  have hexpl : LipschitzOnWith (Real.toNNReal (Real.exp C)) Complex.exp (Metric.closedBall 0 C) := by
    apply (convex_closedBall (0:ℂ) C).lipschitzOnWith_of_nnnorm_deriv_le
    · intro x _; exact differentiableAt_exp
    · intro x hx
      rw [Complex.deriv_exp]
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (Real.exp_pos _).le, norm_exp]
      apply Real.exp_le_exp.2
      have := (mem_closedBall_zero_iff.1 hx)
      exact (re_le_norm x).trans this
  have hEl : LipschitzOnWith (Real.toNNReal (Real.exp C) * Real.toNNReal C) (fun t => exp (-L t)) (Icc 0 1) := by
    have := hexpl.comp hLlip.neg (fun t ht => mem_closedBall_zero_iff.2 (hLb t ht))
    exact this
  have hFac : AbsolutelyContinuousOnInterval (γ • fun t => exp (-L t)) 0 1 := by
    have a := (hK.mono (by rw [uIcc_of_le zero_le_one])).absolutelyContinuousOnInterval (a := 0) (b := 1)
    have b := (hEl.mono (by rw [uIcc_of_le zero_le_one])).absolutelyContinuousOnInterval (a := 0) (b := 1)
    exact a.smul b
  have hder : ∀ᵐ x, x ∈ uIcc (0:ℝ) 1 → HasDerivAt (γ • fun t => exp (-L t)) 0 x := by
    filter_upwards [hint.ae_hasDerivAt_integral, hK.ae_differentiableWithinAt_of_mem (μ := volume),
      ae_ne1 0, ae_ne1 1] with x hx1 hx2 hx3 hx4 hmem
    rw [uIcc_of_le zero_le_one] at hmem
    have hio : x ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hx3), lt_of_le_of_ne hmem.2 hx4⟩
    have hdγ : HasDerivAt γ (deriv γ x) x :=
      ((hx2 hmem).differentiableAt (Icc_mem_nhds hio.1 hio.2)).hasDerivAt
    have hdL : HasDerivAt L (g x) x := by
      have := hx1 (by rw [uIcc_of_le zero_le_one]; exact hmem) 0 (by simp)
      exact this
    have hdE := hdL.neg.cexp
    have := hdγ.mul hdE
    have heq : (γ • fun t => exp (-L t)) = fun t => γ t * exp (-L t) := by
      funext t; simp [Pi.smul_apply]
    rw [heq]
    refine this.congr_deriv ?_
    simp only [g]; field_simp [h0 x hmem]; ring
  obtain ⟨Cc, hCc⟩ := hFac.const_of_ae_hasDerivAt_zero hder
  have e0 := hCc 0 (by simp)
  have e1 := hCc 1 (by simp)
  simp only [Pi.smul_apply', smul_eq_mul, hL, integral_same, neg_zero, exp_zero, mul_one] at e0 e1
  have hE1 : exp (-L 1) = 1 := by
    have : γ 1 * exp (-L 1) = γ 1 * 1 := by rw [mul_one]; simp only [hL]; rw [e1, ← e0, h01]
    exact mul_left_cancel₀ (h0 1 ⟨zero_le_one, le_rfl⟩) this
  obtain ⟨n, hn⟩ := exp_eq_one_iff.1 hE1
  refine ⟨-n, ?_⟩
  have : L 1 = ∫ t in (0:ℝ)..1, deriv γ t / γ t := rfl
  rw [← this]; push_cast; linear_combination -hn

end VX

open Arxiv1811_00800 VX in
theorem solution (Gam lam c : ℝ) (hlam : 0 < lam) (hc : 0 < c)
    (γ : ℝ → ℂ) (hγ : IsClosedPath γ) (h0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ 0) :
    ∃ n : ℤ, windingNumber γ 0 = n ∧
      phaseDiff lam c (vortexField Gam) γ = 4 * Real.pi / (lam * c) * n * Gam ∧
      phaseDiff lam c (vortexField Gam) γ = 4 * Real.pi * abParam Gam lam c * n := by
  obtain ⟨⟨K, hK⟩, h01⟩ := hγ
  obtain ⟨hint, n, hn⟩ := wind γ K hK h01 h0
  have hw : windingNumber γ 0 = n := by
    unfold windingNumber
    simp only [sub_zero]
    rw [hn]; push_cast
    field_simp
  have hcirc : circulation (vortexField Gam) γ = Gam * n := by
    unfold circulation
    have hpt : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        ((vortexField Gam (γ t)).re * (deriv γ t).re + (vortexField Gam (γ t)).im * (deriv γ t).im)
          = Gam / (2 * Real.pi) * (deriv γ t / γ t).im := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have hz := h0 t ht
      have hn2 : normSq (γ t) ≠ 0 := by simpa using hz
      simp only [vortexField, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, div_im]
      rw [← normSq_eq_norm_sq]
      field_simp
      ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
    have him : ∫ t in (0:ℝ)..1, (deriv γ t / γ t).im = (∫ t in (0:ℝ)..1, deriv γ t / γ t).im :=
      (Complex.imCLM).intervalIntegral_comp_comm hint
    rw [him, hn]
    simp
    field_simp
  refine ⟨n, hw, ?_, ?_⟩
  · unfold phaseDiff; rw [hcirc]; ring
  · unfold phaseDiff abParam; rw [hcirc]; field_simp
