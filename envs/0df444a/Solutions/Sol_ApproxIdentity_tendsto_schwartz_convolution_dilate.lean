-- Prove2me | solution 1 for ApproxIdentity.tendsto_schwartz_convolution_dilate
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:36:22.927531+00:00
-- url     : https://prove2.me/submissions/79c09fb5-4eee-4ffc-a83c-8c8314ebb180

import Mathlib

open MeasureTheory Filter Topology
open scoped SchwartzMap

set_option autoImplicit false

namespace Sol_ApproxIdentity_tendsto_schwartz_convolution_dilate

open SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma comp_smul_eq (χ : 𝓢(E, ℂ)) (ε : ℝ) :
    (fun x : E => χ (ε • x)) = (χ : E → ℂ) ∘ (ε • ContinuousLinearMap.id ℝ E) := by
  ext x; simp

lemma norm_iteratedFDeriv_comp_smul_le (χ : 𝓢(E, ℂ)) (ε : ℝ) (i : ℕ) (ξ : E) :
    ‖iteratedFDeriv ℝ i (fun x => χ (ε • x)) ξ‖ ≤ |ε| ^ i * SchwartzMap.seminorm ℝ 0 i χ := by
  rw [comp_smul_eq, (ε • ContinuousLinearMap.id ℝ E).iteratedFDeriv_comp_right (χ.smooth ⊤) ξ
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  have h1 : ‖ε • ContinuousLinearMap.id ℝ E‖ ≤ |ε| := by
    refine (norm_smul_le ε (ContinuousLinearMap.id ℝ E)).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (ContinuousLinearMap.norm_id_le)
  gcongr
  exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ i _

lemma norm_sub_zero_le (χ : 𝓢(E, ℂ)) (x : E) :
    ‖χ x - χ 0‖ ≤ SchwartzMap.seminorm ℝ 0 1 χ * ‖x‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := (χ : E → ℂ)) (s := Set.univ)
    (C := SchwartzMap.seminorm ℝ 0 1 χ) (x := 0) (y := x) (hs := convex_univ)
    (fun z _ => (χ.differentiableAt)) (fun z _ => ?_) (Set.mem_univ _)
    (Set.mem_univ _)
  · simpa using this
  · rw [← norm_iteratedFDeriv_one]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ 1 z

lemma contDiff_comp_smul (χ : 𝓢(E, ℂ)) (ε : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => χ (ε • x)) :=
  (χ.smooth ⊤).comp (contDiff_const_smul ε)

lemma iteratedFDeriv_comp_smul_sub_one (χ : 𝓢(E, ℂ)) (ε : ℝ) {i : ℕ} (hi : i ≠ 0) (ξ : E) :
    iteratedFDeriv ℝ i (fun x => χ (ε • x) - 1) ξ =
      iteratedFDeriv ℝ i (fun x => χ (ε • x)) ξ := by
  rw [fun_iteratedFDeriv_sub_apply ((contDiff_comp_smul χ ε).contDiffAt.of_le
    (by exact_mod_cast le_top)) contDiffAt_const, iteratedFDeriv_const_of_ne hi]
  simp

/-- The pointwise estimate behind the Schwartz-seminorm bound. -/
lemma term_le (χ g : 𝓢(E, ℂ)) (hχ : χ 0 = 1) (k n : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (i : ℕ) (hi : i ≤ n) (ξ : E) :
    ‖ξ‖ ^ k * (‖iteratedFDeriv ℝ i (fun x => χ (ε • x) - 1) ξ‖ *
      ‖iteratedFDeriv ℝ (n - i) g ξ‖) ≤
      ε * ((SchwartzMap.seminorm ℝ 0 1 χ + SchwartzMap.seminorm ℝ 0 i χ) *
        (SchwartzMap.seminorm ℝ k (n - i) g + SchwartzMap.seminorm ℝ (k + 1) (n - i) g)) := by
  have s01 := apply_nonneg (SchwartzMap.seminorm ℝ 0 1) χ
  have s0i := apply_nonneg (SchwartzMap.seminorm ℝ 0 i) χ
  have g1 := apply_nonneg (SchwartzMap.seminorm ℝ k (n - i)) g
  have g2 := apply_nonneg (SchwartzMap.seminorm ℝ (k + 1) (n - i)) g
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [norm_iteratedFDeriv_zero]
    have h1 : ‖χ (ε • ξ) - 1‖ ≤ SchwartzMap.seminorm ℝ 0 1 χ * (ε * ‖ξ‖) := by
      have := norm_sub_zero_le χ (ε • ξ)
      rwa [hχ, norm_smul, Real.norm_of_nonneg hε0] at this
    have h2 : ‖ξ‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - 0) g ξ‖ ≤
        SchwartzMap.seminorm ℝ (k + 1) (n - 0) g := SchwartzMap.le_seminorm ℝ _ _ g ξ
    calc ‖ξ‖ ^ k * (‖χ (ε • ξ) - 1‖ * ‖iteratedFDeriv ℝ (n - 0) g ξ‖)
        ≤ ‖ξ‖ ^ k * ((SchwartzMap.seminorm ℝ 0 1 χ * (ε * ‖ξ‖)) *
            ‖iteratedFDeriv ℝ (n - 0) g ξ‖) := by gcongr
      _ = ε * SchwartzMap.seminorm ℝ 0 1 χ *
            (‖ξ‖ ^ (k + 1) * ‖iteratedFDeriv ℝ (n - 0) g ξ‖) := by ring
      _ ≤ ε * SchwartzMap.seminorm ℝ 0 1 χ * SchwartzMap.seminorm ℝ (k + 1) (n - 0) g := by
          gcongr
      _ ≤ _ := by
          have : SchwartzMap.seminorm ℝ 0 1 χ * SchwartzMap.seminorm ℝ (k + 1) (n - 0) g ≤
              (SchwartzMap.seminorm ℝ 0 1 χ + SchwartzMap.seminorm ℝ 0 0 χ) *
              (SchwartzMap.seminorm ℝ k (n - 0) g + SchwartzMap.seminorm ℝ (k + 1) (n - 0) g) := by
            gcongr <;> linarith
          calc _ = ε * (SchwartzMap.seminorm ℝ 0 1 χ * SchwartzMap.seminorm ℝ (k + 1) (n - 0) g) := by
                ring
            _ ≤ _ := by gcongr
  · rw [iteratedFDeriv_comp_smul_sub_one χ ε hipos.ne']
    have h1 := norm_iteratedFDeriv_comp_smul_le χ ε i ξ
    rw [abs_of_nonneg hε0] at h1
    have h3 : ε ^ i ≤ ε := by
      calc ε ^ i ≤ ε ^ 1 := pow_le_pow_of_le_one hε0 hε1 hipos
        _ = ε := pow_one ε
    have h2 : ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g ξ‖ ≤ SchwartzMap.seminorm ℝ k (n - i) g :=
      SchwartzMap.le_seminorm ℝ _ _ g ξ
    calc ‖ξ‖ ^ k * (‖iteratedFDeriv ℝ i (fun x => χ (ε • x)) ξ‖ * ‖iteratedFDeriv ℝ (n - i) g ξ‖)
        = ‖iteratedFDeriv ℝ i (fun x => χ (ε • x)) ξ‖ *
            (‖ξ‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g ξ‖) := by ring
      _ ≤ (ε * SchwartzMap.seminorm ℝ 0 i χ) * SchwartzMap.seminorm ℝ k (n - i) g := by
          gcongr
          exact h1.trans (by gcongr)
      _ ≤ _ := by
          rw [mul_assoc]
          gcongr <;> linarith

/-- The constant in the seminorm estimate. -/
noncomputable def bound (χ g : 𝓢(E, ℂ)) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ((SchwartzMap.seminorm ℝ 0 1 χ + SchwartzMap.seminorm ℝ 0 i χ) *
        (SchwartzMap.seminorm ℝ k (n - i) g + SchwartzMap.seminorm ℝ (k + 1) (n - i) g))

lemma bound_nonneg (χ g : 𝓢(E, ℂ)) (k n : ℕ) : 0 ≤ bound χ g k n := by
  unfold bound
  refine Finset.sum_nonneg fun i _ => ?_
  have s01 := apply_nonneg (SchwartzMap.seminorm ℝ 0 1) χ
  have s0i := apply_nonneg (SchwartzMap.seminorm ℝ 0 i) χ
  have g1 := apply_nonneg (SchwartzMap.seminorm ℝ k (n - i)) g
  have g2 := apply_nonneg (SchwartzMap.seminorm ℝ (k + 1) (n - i)) g
  positivity

lemma seminorm_le (χ g : 𝓢(E, ℂ)) (hχ : χ 0 = 1) (k n : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h : 𝓢(E, ℂ)) (hh : ∀ ξ, h ξ = (χ (ε • ξ) - 1) * g ξ) :
    SchwartzMap.seminorm ℝ k n h ≤ ε * bound χ g k n := by
  refine SchwartzMap.seminorm_le_bound ℝ k n h (mul_nonneg hε0 (bound_nonneg χ g k n))
    fun ξ => ?_
  have hfun : (h : E → ℂ) = fun x => (χ (ε • x) - 1) * g x := funext hh
  rw [hfun]
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => χ (ε • x) - 1) :=
    (contDiff_comp_smul χ ε).sub contDiff_const
  have hL := norm_iteratedFDeriv_mul_le hf (g.smooth ⊤) ξ (n := n) (by exact_mod_cast le_top)
  calc ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => (χ (ε • x) - 1) * g x) ξ‖
      ≤ ‖ξ‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x => χ (ε • x) - 1) ξ‖ * ‖iteratedFDeriv ℝ (n - i) g ξ‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (‖ξ‖ ^ k * (‖iteratedFDeriv ℝ i (fun x => χ (ε • x) - 1) ξ‖ *
            ‖iteratedFDeriv ℝ (n - i) g ξ‖)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (ε * ((SchwartzMap.seminorm ℝ 0 1 χ + SchwartzMap.seminorm ℝ 0 i χ) *
            (SchwartzMap.seminorm ℝ k (n - i) g + SchwartzMap.seminorm ℝ (k + 1) (n - i) g))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact term_le χ g hχ k n hε0 hε1 i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) ξ
    _ = ε * bound χ g k n := by
        unfold bound
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

/-- If `χ` is a Schwartz function with `χ 0 = 1`, then `χ (ε • ·) * g → g` in `𝓢` as `ε → 0⁺`. -/
lemma tendsto_dilate_mul (χ g : 𝓢(E, ℂ)) (hχ : χ 0 = 1) (P : ℝ → 𝓢(E, ℂ))
    (hP : ∀ ε : ℝ, 0 < ε → ∀ ξ, P ε ξ = χ (ε • ξ) * g ξ) :
    Tendsto P (𝓝[>] 0) (𝓝 g) := by
  rw [(schwartz_withSeminorms ℝ E ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ δ hδ
  have hC0 := bound_nonneg χ g k n
  have hpos : (0 : ℝ) < min 1 (δ / (bound χ g k n + 1)) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
  have hε1 : ε ≤ 1 := hε.2.le.trans (min_le_left _ _)
  have hb := seminorm_le χ g hχ k n hε.1.le hε1 (P ε - g)
    (fun ξ => by rw [sub_apply, hP ε hε.1 ξ]; ring)
  show SchwartzMap.seminorm ℝ k n (P ε - g) < δ
  have hεδ : ε * (bound χ g k n + 1) < δ := by
    have h2 : ε < δ / (bound χ g k n + 1) := hε.2.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by linarith)] at h2
  calc SchwartzMap.seminorm ℝ k n (P ε - g) ≤ ε * bound χ g k n := hb
    _ ≤ ε * (bound χ g k n + 1) := by nlinarith [hε.1]
    _ < δ := hεδ

section Fourier

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform Real in
lemma fourier_dilate (ψ ψ' : 𝓢(E, ℂ)) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x : E, ψ' x = ((ε ^ Module.finrank ℝ E)⁻¹ : ℂ) * ψ (ε⁻¹ • x)) (ξ : E) :
    𝓕 ψ' ξ = 𝓕 ψ (ε • ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq']
  simp_rw [h]
  have key := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := volume)
    (fun y : E => Complex.exp ((↑(-2 * π * inner ℝ (ε • y) ξ) * Complex.I)) •
      (((ε ^ Module.finrank ℝ E)⁻¹ : ℂ) * ψ y)) hε.le
  simp only [smul_inv_smul₀ hε.ne'] at key
  rw [key, ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
  have hε' : ((ε : ℂ) ^ Module.finrank ℝ E) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hε.ne')
  rw [Complex.real_smul]
  push_cast
  field_simp

open FourierTransform Real in
lemma fourier_apply_zero_eq_integral (ψ : 𝓢(E, ℂ)) : 𝓕 ψ 0 = ∫ x : E, ψ x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp

end Fourier

end Sol_ApproxIdentity_tendsto_schwartz_convolution_dilate

open Sol_ApproxIdentity_tendsto_schwartz_convolution_dilate FourierTransform in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ψ φ : 𝓢(E, ℂ)) (hψ : ∫ x : E, ψ x = 1) (ψε : ℝ → 𝓢(E, ℂ))
    (hψε : ∀ ε : ℝ, 0 < ε → ∀ x : E, ψε ε x = ((ε ^ Module.finrank ℝ E)⁻¹ : ℂ) * ψ (ε⁻¹ • x)) :
    Tendsto (fun ε : ℝ => SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (ψε ε) φ)
      (𝓝[>] 0) (𝓝 φ) := by
  have hconv : ∀ ε, SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (ψε ε) φ =
      fourierInvCLM ℂ 𝓢(E, ℂ)
        (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 (ψε ε)) (𝓕 φ)) := fun ε => rfl
  simp_rw [hconv]
  have hlim := tendsto_dilate_mul (𝓕 ψ) (𝓕 φ) (by rw [Sol_ApproxIdentity_tendsto_schwartz_convolution_dilate.fourier_apply_zero_eq_integral, hψ])
    (fun ε => SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 (ψε ε)) (𝓕 φ))
    (fun ε hε ξ => by
      rw [SchwartzMap.pairing_apply_apply, ContinuousLinearMap.mul_apply',
        fourier_dilate ψ (ψε ε) hε (hψε ε hε) ξ])
  have hc := (fourierInvCLM ℂ 𝓢(E, ℂ)).continuous.tendsto (𝓕 φ)
  rw [fourierInvCLM_apply, fourierInv_fourier_eq] at hc
  exact hc.comp hlim
