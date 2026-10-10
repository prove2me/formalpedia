-- Prove2me | solution 1 for ArtinPrimitiveRoots.ne_zero_of_norm_principalMellinOf_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T11:06:23.407717+00:00
-- url     : https://prove2.me/submissions/6be5605d-93e6-4dba-94b4-170808de2fff

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe

section
namespace ArtinPrimitiveRoots

open Complex MeasureTheory Filter Topology Set

/-- Shifting a vertical line integral across a strip on which `F` is holomorphic and has
Gaussian decay `‖F s‖ ≤ K exp(-(Im s)^2)`. -/
theorem T12D_shift (F : ℂ → ℂ) {a b K : ℝ} (hab : a ≤ b)
    (hF : DifferentiableOn ℂ F {s | a ≤ s.re ∧ s.re ≤ b})
    (hK : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ K * Real.exp (-s.im ^ 2))
    (hia : Integrable fun τ : ℝ => F (a + τ * I)) (hib : Integrable fun τ : ℝ => F (b + τ * I)) :
    ∫ τ : ℝ, F (a + τ * I) = ∫ τ : ℝ, F (b + τ * I) := by
  have hrect : ∀ T : ℝ, (∫ x : ℝ in a..b, F (x + (-T) * I)) - (∫ x : ℝ in a..b, F (x + T * I)) +
      I • (∫ y : ℝ in -T..T, F (b + y * I)) - I • (∫ y : ℝ in -T..T, F (a + y * I)) = 0 := by
    intro T
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F ⟨a, -T⟩ ⟨b, T⟩
      (hF.mono fun z hz => by
        rw [mem_reProdIm, Set.uIcc_of_le hab] at hz
        exact ⟨hz.1.1, hz.1.2⟩)
    simpa using this
  have hhor : ∀ T : ℝ, ‖∫ x : ℝ in a..b, F (x + T * I)‖ ≤ K * Real.exp (-T ^ 2) * |b - a| := by
    intro T
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Set.uIoc_of_le hab] at hx
    have := hK (x + T * I) (by simpa using hx.1.le) (by simpa using hx.2)
    simpa using this
  have hexp : Tendsto (fun T : ℝ => K * Real.exp (-T ^ 2) * |b - a|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => Real.exp (-T ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
    simpa using (h1.const_mul K).mul_const |b - a|
  have hup : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F (x + T * I)) atTop (𝓝 0) :=
    squeeze_zero_norm hhor hexp
  have hlow : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F (x + (-T) * I)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => by simpa using hhor (-T)) hexp
  have hva : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, F (a + y * I)) atTop
      (𝓝 (∫ τ : ℝ, F (a + τ * I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hvb : Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, F (b + y * I)) atTop
      (𝓝 (∫ τ : ℝ, F (b + τ * I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have h1 := ((hlow.sub hup).add ((hvb.const_smul I).sub (hva.const_smul I)))
  have h2 : Tendsto (fun T : ℝ => (0 : ℂ)) atTop
      (𝓝 ((0 - 0) + ((I • ∫ τ : ℝ, F (b + τ * I)) - I • ∫ τ : ℝ, F (a + τ * I)))) := by
    refine h1.congr fun T => ?_
    rw [← hrect T]
    ring
  have h3 := tendsto_nhds_unique tendsto_const_nhds h2
  simp only [sub_self, zero_add, smul_eq_mul] at h3
  rw [← mul_sub, eq_comm, mul_eq_zero, sub_eq_zero] at h3
  exact (h3.resolve_left I_ne_zero).symm

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open Complex MeasureTheory Filter Topology Set

/-- The line integral `g(t) = ∫ t^{2+iτ} G(2+iτ) dτ` (the inverse Mellin integral without `1/2π`). -/
noncomputable def T12D_g (G : ℂ → ℂ) (t : ℝ) : ℂ :=
  ∫ τ : ℝ, (t : ℂ) ^ ((2 : ℂ) + τ * I) * G (2 + τ * I)

theorem T12D_cont_line {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s | 1 < s.re}) {c : ℝ}
    (hc : 1 < c) : Continuous fun τ : ℝ => G (c + τ * I) :=
  hGd.continuousOn.comp_continuous (by fun_prop) fun τ => by simpa using hc

theorem T12D_norm_cpow {t : ℝ} (ht : 0 < t) (s : ℂ) : ‖(t : ℂ) ^ s‖ = t ^ s.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos ht s

theorem T12D_integrable_line {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s | 1 < s.re})
    {c K : ℝ} (hc : 1 < c) (hK : ∀ τ : ℝ, ‖G (c + τ * I)‖ ≤ K * Real.exp (-τ ^ 2))
    {t : ℝ} (ht : 0 < t) :
    Integrable fun τ : ℝ => (t : ℂ) ^ ((c : ℂ) + τ * I) * G (c + τ * I) := by
  have hint : Integrable fun τ : ℝ => t ^ c * K * Real.exp (-1 * τ ^ 2) :=
    (integrable_exp_neg_mul_sq one_pos).const_mul _
  refine hint.mono' ?_ (Eventually.of_forall fun τ => ?_)
  · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ (T12D_cont_line hGd hc))
    exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast ht.ne'))
  · rw [norm_mul, T12D_norm_cpow ht]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, neg_mul, one_mul]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK τ) (by positivity)

theorem T12D_integrable_line' {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s | 1 < s.re})
    {c K : ℝ} (hc : 1 < c) (hK : ∀ τ : ℝ, ‖G (c + τ * I)‖ ≤ K * Real.exp (-τ ^ 2)) :
    Integrable fun τ : ℝ => G (c + τ * I) := by
  have := T12D_integrable_line hGd hc hK one_pos
  simpa using this

/-- The line integral is independent of the abscissa `c ≥ 2`. -/
theorem T12D_g_eq_shift {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s | 1 < s.re})
    (hGb : ∀ c : ℝ, ∃ K : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ c → ‖G s‖ ≤ K * Real.exp (-s.im ^ 2))
    {t : ℝ} (ht : 0 < t) {c : ℝ} (hc : 2 ≤ c) :
    T12D_g G t = ∫ τ : ℝ, (t : ℂ) ^ ((c : ℂ) + τ * I) * G (c + τ * I) := by
  obtain ⟨K, hK⟩ := hGb c
  have hK0 : 0 ≤ K := by
    have h := hK 2 (by simp) (by simpa using hc)
    by_contra hneg
    have : K * Real.exp (-(2 : ℂ).im ^ 2) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hneg) (Real.exp_pos _)
    linarith [norm_nonneg (G 2)]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hb : ∀ σ : ℝ, 2 ≤ σ → σ ≤ c → ∀ τ : ℝ, ‖G (σ + τ * I)‖ ≤ K * Real.exp (-τ ^ 2) :=
    fun σ h1 h2 τ => by simpa using hK (σ + τ * I) (by simpa using h1) (by simpa using h2)
  have h2 := T12D_integrable_line hGd one_lt_two (hb 2 le_rfl hc) ht
  have hcc := T12D_integrable_line hGd (by linarith) (hb c hc le_rfl) ht
  unfold T12D_g
  have := T12D_shift (fun s => (t : ℂ) ^ s * G s) (a := 2) (b := c) (K := (t ^ (2:ℝ) + t ^ c) * K) hc
    ?_ ?_ (by simpa using h2) hcc
  · simpa using this
  · refine DifferentiableOn.mul (fun s _ => (differentiableAt_id.const_cpow
      (Or.inl ht0)).differentiableWithinAt) (hGd.mono fun s hs => ?_)
    simp only [mem_ofPred_eq] at hs ⊢
    linarith [hs.1]
  · intro s h1 h2'
    rw [norm_mul, T12D_norm_cpow ht]
    have hpow : t ^ s.re ≤ t ^ (2:ℝ) + t ^ c := by
      rcases le_or_gt 1 t with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h h2'
        linarith [Real.rpow_nonneg ht.le 2]
      · have := Real.rpow_le_rpow_of_exponent_ge ht h.le h1
        linarith [Real.rpow_nonneg ht.le c]
    calc t ^ s.re * ‖G s‖ ≤ (t ^ (2:ℝ) + t ^ c) * (K * Real.exp (-s.im ^ 2)) :=
          mul_le_mul hpow (hK s h1 h2') (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- `g(t) = O(t^3)` on `t > 0`. -/
theorem T12D_g_bound_zero {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s | 1 < s.re})
    (hGb : ∀ c : ℝ, ∃ K : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ c → ‖G s‖ ≤ K * Real.exp (-s.im ^ 2)) :
    ∃ A : ℝ, ∀ t : ℝ, 0 < t → ‖T12D_g G t‖ ≤ A * t ^ (3 : ℝ) := by
  obtain ⟨K, hK⟩ := hGb 3
  have hb : ∀ τ : ℝ, ‖G ((3 : ℝ) + τ * I)‖ ≤ K * Real.exp (-τ ^ 2) :=
    fun τ => by simpa using hK ((3 : ℝ) + τ * I) (by norm_num) (by norm_num)
  refine ⟨∫ τ : ℝ, ‖G ((3 : ℝ) + τ * I)‖, fun t ht => ?_⟩
  rw [T12D_g_eq_shift hGd hGb ht (c := 3) (by norm_num)]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [mul_comm, ← integral_const_mul]
  congr 1
  funext τ
  rw [norm_mul, T12D_norm_cpow ht]
  simp

/-- `g` is continuous on `t > 0`. -/
theorem T12D_g_continuousOn {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s | 1 < s.re})
    (hGb : ∀ c : ℝ, ∃ K : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ c → ‖G s‖ ≤ K * Real.exp (-s.im ^ 2)) :
    ContinuousOn (T12D_g G) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  obtain ⟨K, hK⟩ := hGb 2
  have hb : ∀ τ : ℝ, ‖G ((2 : ℝ) + τ * I)‖ ≤ K * Real.exp (-τ ^ 2) :=
    fun τ => by simpa using hK ((2 : ℝ) + τ * I) (by norm_num) (by norm_num)
  have hGi := T12D_integrable_line' hGd one_lt_two hb
  refine ContinuousAt.continuousWithinAt ?_
  have hnhds : ∀ᶠ t in 𝓝 t₀, t ∈ Ioo (t₀ / 2) (2 * t₀) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  refine continuousAt_of_dominated (bound := fun τ => (2 * t₀) ^ 2 * ‖G ((2 : ℝ) + τ * I)‖)
    ?_ ?_ (hGi.norm.const_mul _) ?_
  · filter_upwards [hnhds] with t ht
    have htp : 0 < t := by linarith [ht.1]
    have := T12D_integrable_line hGd one_lt_two hb htp
    simpa using this.aestronglyMeasurable
  · filter_upwards [hnhds] with t ht
    have htp : 0 < t := by linarith [ht.1]
    refine Eventually.of_forall fun τ => ?_
    rw [norm_mul, T12D_norm_cpow htp]
    have h1 : t ^ ((2 : ℂ) + τ * I).re = t ^ 2 := by simp
    rw [h1]
    have : t ^ 2 ≤ (2 * t₀) ^ 2 := pow_le_pow_left₀ htp.le ht.2.le 2
    simpa using mul_le_mul_of_nonneg_right this (norm_nonneg _)
  · refine Eventually.of_forall fun τ => ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
    simp [ht₀']

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open Complex MeasureTheory Filter Topology Set Real

open scoped FourierTransform

private theorem T12D_rexp_neg_deriv_aux :
    ∀ x ∈ univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem T12D_rexp_neg_image_aux : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem T12D_rexp_neg_injOn_aux : univ.InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

private theorem T12D_rexp_cexp_aux (x : ℝ) (s : ℂ) (f : ℂ) :
    cexp (-↑x) * (cexp (-↑x) ^ (s - 1) * f) = cexp (-(s * ↑x)) * f := by
  have h : cexp (-↑x) ^ (s - 1) = cexp ((-↑x) * (s - 1)) := by
    rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [pi_pos]) (by simpa using pi_nonneg)]
  rw [h, ← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- Mellin convergence at `σ` gives integrability of `u ↦ e^{-σu} f(e^{-u})`. -/
theorem T12D_integrable_of_mellinConvergent {f : ℝ → ℂ} {σ : ℝ}
    (hf : MellinConvergent f σ) :
    Integrable fun u : ℝ => (rexp (-σ * u) : ℂ) * f (rexp (-u)) := by
  rw [MellinConvergent, ← T12D_rexp_neg_image_aux,
    integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ T12D_rexp_neg_deriv_aux T12D_rexp_neg_injOn_aux] at hf
  replace hf : Integrable fun (x : ℝ) ↦ cexp (-↑σ * ↑x) • f (rexp (-x)) := by
    simpa [T12D_rexp_cexp_aux] using hf
  refine hf.congr (Eventually.of_forall fun u => ?_)
  simp [smul_eq_mul]

/-- `e^{σu} g(e^{-u})` is the Fourier transform of `ξ ↦ 2π G(σ + 2πξ i)`. -/
theorem T12D_fourier_eq {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s | 1 < s.re})
    (hGb : ∀ c : ℝ, ∃ K : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ c → ‖G s‖ ≤ K * Real.exp (-s.im ^ 2))
    {σ : ℝ} (hσ : 2 ≤ σ) (u : ℝ) :
    (rexp (σ * u) : ℂ) * T12D_g G (rexp (-u)) =
      𝓕 (fun ξ : ℝ => (2 * π : ℂ) * G (σ + (2 * π * ξ : ℝ) * I)) u := by
  rw [T12D_g_eq_shift hGd hGb (Real.exp_pos _) hσ, fourier_real_eq_integral_exp_smul]
  have hsub := Measure.integral_comp_mul_left
    (fun τ : ℝ => cexp (↑(-τ * u) * I) * G (σ + τ * I)) (2 * π)
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have e1 : (∫ ξ : ℝ, cexp (↑(-2 * π * ξ * u) * I) • ((2 * π : ℂ) * G (σ + (2 * π * ξ : ℝ) * I)))
      = (2 * π : ℂ) * ∫ ξ : ℝ, cexp (↑(-(2 * π * ξ) * u) * I) * G (σ + (2 * π * ξ : ℝ) * I) := by
    rw [← integral_const_mul]
    congr 1
    funext ξ
    simp only [smul_eq_mul]
    ring_nf
  rw [e1, hsub, ← integral_const_mul, abs_inv, abs_of_pos hpi, real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hpi.ne'), one_mul]
  congr 1
  funext τ
  have hx : cexp (-(u : ℂ)) ^ ((σ : ℂ) + τ * I) = cexp (-(u : ℂ) * (σ + τ * I)) := by
    rw [cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [pi_pos]) (by simpa using pi_nonneg)]
  rw [hx, ← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- Mellin–Fourier inversion: the Mellin transform of `g` at `-(σ + iη)` is `2π G(σ + iη)`. -/
theorem T12D_mellin_eq {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s | 1 < s.re})
    (hGb : ∀ c : ℝ, ∃ K : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ c → ‖G s‖ ≤ K * Real.exp (-s.im ^ 2))
    {σ : ℝ} (hσ : 2 ≤ σ) (hconv : MellinConvergent (T12D_g G) ((-σ : ℝ) : ℂ)) (η : ℝ) :
    mellin (T12D_g G) (-((σ : ℂ) + η * I)) = 2 * π * G (σ + η * I) := by
  set ψ := fun ξ : ℝ => (2 * π : ℂ) * G (σ + (2 * π * ξ : ℝ) * I) with hψ
  have hF : (fun u : ℝ => rexp (-(-((σ : ℂ) + η * I)).re * u) • T12D_g G (rexp (-u))) = 𝓕 ψ := by
    funext u
    rw [← T12D_fourier_eq hGd hGb hσ u]
    simp [Complex.real_smul]
  rw [mellin_eq_fourier, hF]
  have him : (-((σ : ℂ) + η * I)).im / (2 * π) = -(η / (2 * π)) := by simp; ring
  rw [him, ← fourierInv_eq_fourier_neg]
  obtain ⟨K, hK⟩ := hGb σ
  have hline := T12D_integrable_line' hGd (c := σ) (K := K) (by linarith)
    (fun τ => by simpa using hK (σ + τ * I) (by simpa using hσ) (by simp))
  have hψi : Integrable ψ :=
    (hline.comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)).const_mul _
  have h𝓕i : Integrable (𝓕 ψ) := by
    have := T12D_integrable_of_mellinConvergent hconv
    refine this.congr (Eventually.of_forall fun u => ?_)
    rw [← T12D_fourier_eq hGd hGb hσ u]
    simp
  have hψc : Continuous ψ :=
    continuous_const.mul ((T12D_cont_line hGd (c := σ) (by linarith)).comp
      (by fun_prop : Continuous fun ξ : ℝ => 2 * π * ξ))
  rw [hψi.fourierInv_fourier_eq h𝓕i hψc.continuousAt, hψ]
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  simp only
  congr 3
  field_simp

end ArtinPrimitiveRoots
end

section
namespace ArtinPrimitiveRoots

open Complex MeasureTheory Filter Topology Set

/-- The analytic continuation: if `g = O(t^{1-δ})` at `∞`, the Mellin transform `s ↦ mellin g (-s)`
is holomorphic on `1 - δ < Re s < 3` and equals `2π G` on `2 < Re s < 3`. -/
theorem T12D_core {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s | 1 < s.re})
    (hGb : ∀ c : ℝ, ∃ K : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ c → ‖G s‖ ≤ K * Real.exp (-s.im ^ 2))
    {δ A Z₁ : ℝ} (hδ : 0 < δ) (hZ₁ : 0 < Z₁) (htop : ∀ t : ℝ, Z₁ ≤ t → ‖T12D_g G t‖ ≤ A * t ^ (1 - δ)) :
    DifferentiableOn ℂ (fun s => mellin (T12D_g G) (-s)) {s | 1 - δ < s.re ∧ s.re < 3} ∧
    ∀ s : ℂ, 2 < s.re → s.re < 3 → mellin (T12D_g G) (-s) = 2 * Real.pi * G s := by
  have hloc : LocallyIntegrableOn (T12D_g G) (Ioi 0) :=
    (T12D_g_continuousOn hGd hGb).locallyIntegrableOn measurableSet_Ioi
  have hf_top : T12D_g G =O[atTop] fun t : ℝ => t ^ (-(δ - 1)) := by
    refine Asymptotics.IsBigO.of_bound A ?_
    filter_upwards [eventually_ge_atTop Z₁] with t ht
    have htp : 0 < t := hZ₁.trans_le ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg htp.le _), neg_sub]
    exact htop t ht
  obtain ⟨B, hB⟩ := T12D_g_bound_zero hGd hGb
  have hf_bot : T12D_g G =O[𝓝[>] 0] fun t : ℝ => t ^ (-(-3 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound B ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _), neg_neg]
    exact hB t ht
  refine ⟨fun s hs => ?_, fun s h2 h3 => ?_⟩
  · have := mellin_differentiableAt_of_isBigO_rpow hloc hf_top (s := -s) (by simp; linarith [hs.1])
      hf_bot (by simp; linarith [hs.2])
    exact (this.comp s differentiableAt_id.neg).differentiableWithinAt
  · have hconv : MellinConvergent (T12D_g G) ((-s.re : ℝ) : ℂ) :=
      mellinConvergent_of_isBigO_rpow hloc hf_top (by simp; linarith) hf_bot (by simp; linarith)
    have := T12D_mellin_eq hGd hGb (σ := s.re) (by linarith) hconv s.im
    rwa [re_add_im] at this

theorem T12D_norm_gauss_le {s : ℂ} {c : ℝ} (h2 : 2 ≤ s.re) (hc : s.re ≤ c) :
    ‖cexp ((s - 5 / 6) ^ 2)‖ ≤ Real.exp ((c - 5 / 6) ^ 2) * Real.exp (-s.im ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have : ((s - 5 / 6) ^ 2).re = (s.re - 5 / 6) ^ 2 - s.im ^ 2 := by
    simp [sq]
  rw [this]
  nlinarith

/-- `g(Z) = 2π Z^{8/15} f(Z)` for `Z > 0`. -/
theorem T12D_g_eq (H L : ℂ → ℂ) {Z : ℝ} (hZ : 0 < Z) :
    T12D_g (fun s => cexp ((s - 5 / 6) ^ 2) * H s / L s) Z =
      2 * Real.pi * (Z : ℂ) ^ ((8 / 15 : ℂ)) * principalMellinOf H L Z := by
  unfold T12D_g principalMellinOf
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hZ0 : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  rw [← mul_assoc, mul_assoc (2 * (Real.pi : ℂ)), mul_comm ((Z : ℂ) ^ _), ← mul_assoc,
    show 2 * (Real.pi : ℂ) * (1 / (2 * Real.pi)) = 1 by field_simp, one_mul,
    ← integral_const_mul]
  congr 1
  funext τ
  have : (Z : ℂ) ^ ((2 : ℂ) + τ * I) =
      (Z : ℂ) ^ ((8 / 15 : ℂ)) * (Z : ℂ) ^ ((2 : ℂ) + τ * I - 8 / 15) := by
    rw [← cpow_add _ _ hZ0]
    ring_nf
  rw [this]
  ring

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Complex MeasureTheory Filter Topology Set
theorem solution (L H : ℂ → ℂ) (δ : ℝ)
    (hL : DifferentiableOn ℂ L {s | 1 - δ < s.re ∧ s ≠ 1})
    (hL1 : ∀ s : ℂ, 1 < s.re → L s ≠ 0)
    (hLb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖(L s)⁻¹‖ ≤ B)
    (hH : DifferentiableOn ℂ H {s | 1 - δ < s.re})
    (hH0 : ∀ s : ℂ, 1 - δ < s.re → H s ≠ 0)
    (hHb : ∃ B : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖H s‖ ≤ B)
    (hf : ∃ C Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z →
      ‖principalMellinOf H L Z‖ ≤ C * Z ^ ((7 : ℝ) / 15 - δ)) :
    ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 → L s ≠ 0 := by
  intro s₀ hs₀ hs₁
  rcases lt_or_ge 1 s₀.re with h1 | h1
  · exact hL1 s₀ h1
  have hδ : 0 < δ := by linarith
  obtain ⟨BL, hBL⟩ := hLb
  obtain ⟨BH, hBH⟩ := hHb
  obtain ⟨C, Z₀, hf⟩ := hf
  have hBL0 : 0 ≤ BL := (norm_nonneg _).trans (hBL 2 (by simp))
  have hBH0 : 0 ≤ BH := (norm_nonneg _).trans (hBH 2 (by simp))
  set G : ℂ → ℂ := fun s => cexp ((s - 5 / 6) ^ 2) * H s / L s with hG
  have hsub1 : {s : ℂ | 1 < s.re} ⊆ {s | 1 - δ < s.re ∧ s ≠ 1} := fun s (hs : 1 < s.re) =>
    ⟨by linarith, fun h => by rw [h] at hs; simp at hs⟩
  have hGd : DifferentiableOn ℂ G {s | 1 < s.re} := by
    refine DifferentiableOn.div (DifferentiableOn.mul ?_ (hH.mono fun s hs => (hsub1 hs).1))
      (hL.mono hsub1) fun s hs => hL1 s hs
    exact (Differentiable.cexp (by fun_prop)).differentiableOn
  have hGb : ∀ c : ℝ, ∃ K : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ c →
      ‖G s‖ ≤ K * Real.exp (-s.im ^ 2) := by
    intro c
    refine ⟨Real.exp ((c - 5 / 6) ^ 2) * BH * BL, fun s h2 hc => ?_⟩
    simp only [hG, div_eq_mul_inv, norm_mul]
    have e1 := T12D_norm_gauss_le h2 hc
    calc ‖cexp ((s - 5 / 6) ^ 2)‖ * ‖H s‖ * ‖(L s)⁻¹‖
        ≤ (Real.exp ((c - 5 / 6) ^ 2) * Real.exp (-s.im ^ 2)) * BH * BL := by
          gcongr
          · exact hBH s h2
          · exact hBL s h2
      _ = _ := by ring_nf
  -- the bound at infinity
  set Z₁ := max Z₀ 1 with hZ₁
  have hZ₁0 : 0 < Z₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have htop : ∀ t : ℝ, Z₁ ≤ t → ‖T12D_g G t‖ ≤ (2 * Real.pi * C) * t ^ (1 - δ) := by
    intro t ht
    have htp : 0 < t := hZ₁0.trans_le ht
    rw [T12D_g_eq H L htp, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htp]
    have hft := hf t ((le_max_left _ _).trans ht)
    have hpi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; norm_num
    rw [hpi]
    have e : t ^ (1 - δ) = t ^ ((8 / 15 : ℂ)).re * t ^ ((7 : ℝ) / 15 - δ) := by
      rw [← Real.rpow_add htp]; congr 1; norm_num; ring
    rw [e]
    calc 2 * Real.pi * t ^ ((8 / 15 : ℂ)).re * ‖principalMellinOf H L t‖
        ≤ 2 * Real.pi * t ^ ((8 / 15 : ℂ)).re * (C * t ^ ((7 : ℝ) / 15 - δ)) := by
          gcongr
      _ = _ := by ring
  obtain ⟨hMd, hMeq⟩ := T12D_core hGd hGb hδ hZ₁0 htop
  -- the identity theorem
  set M : ℂ → ℂ := fun s => mellin (T12D_g G) (-s) with hM
  set F1 : ℂ → ℂ := fun s => M s * L s with hF1
  set F2 : ℂ → ℂ := fun s => 2 * Real.pi * (cexp ((s - 5 / 6) ^ 2) * H s) with hF2
  set A : Set ℂ := {s | 1 - δ < s.re} ∩ {s | s.re < 3} ∩ {s | 0 < s.im} with hA
  set B : Set ℂ := {s | 1 - δ < s.re} ∩ {s | s.re < 3} ∩ {s | s.im < 0} with hB
  set Cc : Set ℂ := {s | 1 < s.re} ∩ {s | s.re < 3} with hCc
  set D : Set ℂ := {s | 1 - δ < s.re} ∩ {s | s.re < 1} with hD
  set W : Set ℂ := ((A ∪ Cc) ∪ B) ∪ D with hW
  have hreo : ∀ r : ℝ, IsOpen {s : ℂ | r < s.re} := fun r => isOpen_lt continuous_const
    Complex.continuous_re
  have hreo' : ∀ r : ℝ, IsOpen {s : ℂ | s.re < r} := fun r => isOpen_lt Complex.continuous_re
    continuous_const
  have hWo : IsOpen W := by
    refine (((((hreo _).inter (hreo' _)).inter (isOpen_lt continuous_const
      Complex.continuous_im)).union ((hreo _).inter (hreo' _))).union
      (((hreo _).inter (hreo' _)).inter (isOpen_lt Complex.continuous_im
      continuous_const))).union ((hreo _).inter (hreo' _))
  have hWsub : ∀ s ∈ W, (1 - δ < s.re ∧ s.re < 3) ∧ s ≠ 1 := by
    intro s hs
    have hne : ∀ s : ℂ, s.im ≠ 0 → s ≠ 1 := fun s h e => by rw [e] at h; simp at h
    have hne' : ∀ s : ℂ, s.re ≠ 1 → s ≠ 1 := fun s h e => by rw [e] at h; simp at h
    rcases hs with ((⟨⟨ha, hb⟩, hc⟩ | ⟨ha, hb⟩) | ⟨⟨ha, hb⟩, hc⟩) | ⟨ha, hb⟩
    · exact ⟨⟨ha, hb⟩, hne s (ne_of_gt hc)⟩
    · exact ⟨⟨by simp only [mem_ofPred_eq] at ha; linarith, hb⟩, hne' s (ne_of_gt ha)⟩
    · exact ⟨⟨ha, hb⟩, hne s (ne_of_lt hc)⟩
    · exact ⟨⟨ha, by simp only [mem_ofPred_eq] at hb; linarith⟩, hne' s (ne_of_lt hb)⟩
  have hF1d : DifferentiableOn ℂ F1 W :=
    (hMd.mono fun s hs => (hWsub s hs).1).mul
      (hL.mono fun s hs => ⟨(hWsub s hs).1.1, (hWsub s hs).2⟩)
  have hF2d : DifferentiableOn ℂ F2 W := by
    refine DifferentiableOn.const_mul (DifferentiableOn.mul ?_
      (hH.mono fun s hs => (hWsub s hs).1.1)) _
    exact (Differentiable.cexp (by fun_prop)).differentiableOn
  have hWc : IsPreconnected W := by
    have cA : Convex ℝ A := ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
      (convex_halfSpace_im_gt _)
    have cB : Convex ℝ B := ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
      (convex_halfSpace_im_lt _)
    have cC : Convex ℝ Cc := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
    have cD : Convex ℝ D := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
    refine IsPreconnected.union ((1 - δ / 2 : ℝ) + I) ?_ ?_
      (IsPreconnected.union (2 - I) ?_ ?_ (IsPreconnected.union (2 + I) ?_ ?_
        cA.isPreconnected cC.isPreconnected) cB.isPreconnected) cD.isPreconnected
    · refine Or.inl (Or.inl ⟨⟨?_, ?_⟩, ?_⟩) <;> simp <;> linarith
    · refine ⟨?_, ?_⟩ <;> simp <;> linarith
    · refine Or.inr ⟨?_, ?_⟩ <;> simp <;> norm_num
    · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp <;> norm_num <;> linarith
    · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp <;> norm_num <;> linarith
    · refine ⟨?_, ?_⟩ <;> simp <;> norm_num
  have hz₀ : (5 / 2 : ℂ) ∈ W := Or.inl (Or.inl (Or.inr ⟨by simp; norm_num, by simp; norm_num⟩))
  have hev : F1 =ᶠ[𝓝 (5 / 2 : ℂ)] F2 := by
    have hU : {s : ℂ | 2 < s.re} ∩ {s | s.re < 3} ∈ 𝓝 (5 / 2 : ℂ) :=
      ((hreo _).inter (hreo' _)).mem_nhds ⟨by simp; norm_num, by simp; norm_num⟩
    filter_upwards [hU] with s hs
    have hLs : L s ≠ 0 := hL1 s (by have := hs.1; simp only [mem_ofPred_eq] at this; linarith)
    simp only [hF1, hF2, hM]
    rw [hMeq s hs.1 hs.2, hG]
    field_simp
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hF1d.analyticOnNhd hWo)
    (hF2d.analyticOnNhd hWo) hWc hz₀ hev
  have hs₀W : s₀ ∈ W := by
    rcases lt_trichotomy s₀.im 0 with h | h | h
    · exact Or.inl (Or.inr ⟨⟨hs₀, show s₀.re < 3 by linarith⟩, h⟩)
    · have hre : s₀.re ≠ 1 := fun e => hs₁ (Complex.ext (by simpa using e) (by simpa using h))
      exact Or.inr ⟨hs₀, lt_of_le_of_ne h1 hre⟩
    · exact Or.inl (Or.inl (Or.inl ⟨⟨hs₀, show s₀.re < 3 by linarith⟩, h⟩))
  intro hL0
  have := heq hs₀W
  simp only [hF1, hF2, hL0, mul_zero] at this
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  exact (mul_ne_zero hpi (mul_ne_zero (Complex.exp_ne_zero _) (hH0 s₀ hs₀))) this.symm
end
