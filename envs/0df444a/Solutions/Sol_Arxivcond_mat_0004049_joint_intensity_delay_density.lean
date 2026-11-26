-- Prove2me | solution 1 for Arxivcond_mat_0004049.joint_intensity_delay_density
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T16:11:02.015141+00:00
-- url     : https://prove2.me/submissions/3f3be1fa-8d76-4359-bf3d-3f2498b80a9c

import Definitions.Def_Arxivcond_mat_0004049_Basic
import Theorems.Thm_MathlibGap_gaussianReal_prod_map_sq_add_sq
import Theorems.Thm_Arxivcond_mat_0004049_gaussVec_isProbabilityMeasure
import Theorems.Thm_Arxivcond_mat_0004049_laguerreEnsemble_isProbabilityMeasure
import Theorems.Thm_Arxivcond_mat_0004049_localizedModel_isProbabilityMeasure

open MeasureTheory ProbabilityTheory Set

namespace Arxivcond_mat_0004049

section PairLaw
open MeasureTheory ProbabilityTheory Complex

/-- A real-linear functional on `ℂ` is determined by its values at `1` and `I`. -/
private lemma dual_apply_eq (ℓ : StrongDual ℝ ℂ) (z : ℂ) : ℓ z = z.re * ℓ 1 + z.im * ℓ I := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Dual characteristic function of the circular complex Gaussian with re/im variance `s`. -/
private lemma charFunDual_cG (s : NNReal) (ℓ : StrongDual ℝ ℂ) :
    charFunDual (((gaussianReal 0 s).prod (gaussianReal 0 s)).map
      Complex.measurableEquivRealProd.symm) ℓ =
      cexp (-((s : ℝ) * (ℓ 1 ^ 2 + ℓ I ^ 2) / 2 : ℝ)) := by
  rw [charFunDual_apply, integral_map_equiv]
  have hin : ∀ p : ℝ × ℝ, cexp (((ℓ (Complex.measurableEquivRealProd.symm p) : ℝ) : ℂ) * I)
      = cexp ((ℓ 1 : ℂ) * p.1 * I) * cexp ((ℓ I : ℂ) * p.2 * I) := by
    intro p
    rw [← Complex.exp_add, dual_apply_eq]
    congr 1
    simp [Complex.measurableEquivRealProd]
    ring
  simp_rw [hin]
  rw [integral_prod_mul (fun x : ℝ => cexp ((ℓ 1 : ℂ) * x * I))
    (fun y : ℝ => cexp ((ℓ I : ℂ) * y * I))]
  rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem gaussVec_map_pair (N : ℕ) (a b : Fin N → ℂ)
    (hab : ∑ i, a i * (starRingEnd ℂ) (b i) = 0) :
    (Arxivcond_mat_0004049.gaussVec N).map (fun v => (∑ i, a i * v i, ∑ i, b i * v i)) =
      (((gaussianReal 0 ((∑ i, Complex.normSq (a i)).toNNReal / (2 * N))).prod
          (gaussianReal 0 ((∑ i, Complex.normSq (a i)).toNNReal / (2 * N)))).map
            Complex.measurableEquivRealProd.symm).prod
        (((gaussianReal 0 ((∑ i, Complex.normSq (b i)).toNNReal / (2 * N))).prod
          (gaussianReal 0 ((∑ i, Complex.normSq (b i)).toNNReal / (2 * N)))).map
            Complex.measurableEquivRealProd.symm) := by
  set s : NNReal := (N : NNReal)⁻¹ / 2 with hs
  set ν : Measure ℂ := ((gaussianReal 0 s).prod (gaussianReal 0 s)).map
    Complex.measurableEquivRealProd.symm with hν
  have hνP : IsProbabilityMeasure ν := by
    rw [hν]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hpi : Arxivcond_mat_0004049.gaussVec N = Measure.pi (fun _ : Fin N => ν) := by
    rw [Arxivcond_mat_0004049.gaussVec, Measure.pi_map_pi (fun _ => by fun_prop)]
  -- the pair of projections as a real-linear map
  let F : (Fin N → ℂ) →L[ℝ] ℂ × ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun v => (∑ i, a i * v i, ∑ i, b i * v i)
      map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by simp [Finset.mul_sum, mul_left_comm] }
  have hF : (fun v : Fin N → ℂ => (∑ i, a i * v i, ∑ i, b i * v i)) = ⇑F := rfl
  rw [hF, hpi]
  have : IsProbabilityMeasure ((Measure.pi (fun _ : Fin N => ν)).map ⇑F) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  refine (charFunDual_eq_prod_iff).mp fun L => ?_
  rw [charFunDual_map, charFunDual_pi]
  simp_rw [hν, charFunDual_cG]
  rw [← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  have hFi : ∀ i z, F (Pi.single i z) = (a i * z, b i * z) := by
    intro i z
    simp [F, Pi.single_apply]
  have hL : ∀ z w : ℂ, L (z, w) = z.re * L (1, 0) + z.im * L (I, 0) + w.re * L (0, 1)
      + w.im * L (0, I) := by
    intro z w
    rw [← L.comp_inl_add_comp_inr, dual_apply_eq (L.comp _) z, dual_apply_eq (L.comp _) w]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    ring
  have h1 : ∑ i, ((a i).re * (b i).re + (a i).im * (b i).im) = 0 := by
    have := congrArg Complex.re hab
    simpa [Complex.re_sum] using this
  have h2 : ∑ i, ((a i).im * (b i).re - (a i).re * (b i).im) = 0 := by
    have := congrArg Complex.im hab
    simp only [Complex.im_sum, mul_im, conj_re, conj_im, Complex.zero_im] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hna : (0 : ℝ) ≤ ∑ i, normSq (a i) := Finset.sum_nonneg fun i _ => normSq_nonneg _
  have hnb : (0 : ℝ) ≤ ∑ i, normSq (b i) := Finset.sum_nonneg fun i _ => normSq_nonneg _
  have hpt : ∀ i, ((L.comp F).comp (ContinuousLinearMap.single ℝ (fun _ => ℂ) i)) 1 ^ 2
      + ((L.comp F).comp (ContinuousLinearMap.single ℝ (fun _ => ℂ) i)) I ^ 2
      = (L (1, 0) ^ 2 + L (I, 0) ^ 2) * normSq (a i) + (L (0, 1) ^ 2 + L (0, I) ^ 2) * normSq (b i)
        + 2 * (L (1, 0) * L (0, 1) + L (I, 0) * L (0, I))
          * ((a i).re * (b i).re + (a i).im * (b i).im)
        + 2 * (L (I, 0) * L (0, 1) - L (1, 0) * L (0, I))
          * ((a i).im * (b i).re - (a i).re * (b i).im) := by
    intro i
    change L (F (Pi.single i 1)) ^ 2 + L (F (Pi.single i I)) ^ 2 = _
    rw [hFi, hFi, mul_one, mul_one]
    rw [hL (a i) (b i), hL (a i * I) (b i * I)]
    simp [normSq_apply]
    ring
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_sum, ← Complex.ofReal_add]
  congr 1
  rw [Finset.sum_congr rfl fun i _ => by rw [hpt i]]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, NNReal.coe_div, Real.coe_toNNReal _ hna,
    Real.coe_toNNReal _ hnb, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, hs,
    NNReal.coe_inv]
  simp only [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib,
    h1, h2]
  ring

end PairLaw

section CondGauss
open MeasureTheory ProbabilityTheory Set

/-- `m + a X + b Y` for i.i.d. `X, Y ~ N(0, s)` is `N(m, (a² + b²) s)`. -/
private lemma gauss_lin (s : NNReal) (m a b : ℝ) :
    ((gaussianReal 0 s).prod (gaussianReal 0 s)).map (fun p : ℝ × ℝ => m + (a * p.1 + b * p.2)) =
      gaussianReal m ((a ^ 2 + b ^ 2).toNNReal * s) := by
  have h1 : ((gaussianReal 0 s).prod (gaussianReal 0 s)).map (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      ((gaussianReal 0 s).map (a * ·)) ∗ ((gaussianReal 0 s).map (b * ·)) := by
    rw [Measure.conv, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h2 : ((gaussianReal 0 s).prod (gaussianReal 0 s)).map
        (fun p : ℝ × ℝ => m + (a * p.1 + b * p.2)) =
      (((gaussianReal 0 s).prod (gaussianReal 0 s)).map
        (fun p : ℝ × ℝ => a * p.1 + b * p.2)).map (m + ·) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
  rw [h2, h1, gaussianReal_map_const_mul, gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal,
    gaussianReal_map_const_add]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ (by positivity : 0 ≤ a ^ 2 + b ^ 2)]
    ring

private theorem condGauss_eq13_aux (N : ℕ) (hN : 1 ≤ N) (B1 B2 : ℝ) (hB : B1 ^ 2 < B2) :
    ((((gaussianReal 0 ((1 : ℝ).toNNReal / (2 * N))).prod
          (gaussianReal 0 ((1 : ℝ).toNNReal / (2 * N)))).map
            Complex.measurableEquivRealProd.symm).prod
        (((gaussianReal 0 ((B2 - B1 ^ 2).toNNReal / (2 * N))).prod
          (gaussianReal 0 ((B2 - B1 ^ 2).toNNReal / (2 * N)))).map
            Complex.measurableEquivRealProd.symm)).map
      (fun p : ℂ × ℂ => (Complex.normSq p.1, B1 + (p.2 / p.1).re)) =
    (volume : Measure (ℝ × ℝ)).withDensity
      (fun q => ENNReal.ofReal (eq13Kernel N B1 B2 q.1 q.2)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : 0 < B2 - B1 ^ 2 := by linarith
  set s0 : NNReal := (1 : ℝ).toNNReal / (2 * N) with hs0
  set s1 : NNReal := (B2 - B1 ^ 2).toNNReal / (2 * N) with hs1
  have hs0r : (s0 : ℝ) = 1 / (2 * N) := by
    rw [hs0, NNReal.coe_div, Real.coe_toNNReal _ zero_le_one]; push_cast; ring
  have hs1r : (s1 : ℝ) = (B2 - B1 ^ 2) / (2 * N) := by
    rw [hs1, NNReal.coe_div, Real.coe_toNNReal _ hc.le]; push_cast; ring
  have hs0ne : s0 ≠ 0 := by rw [← NNReal.coe_ne_zero, hs0r]; positivity
  set μZ := ((gaussianReal 0 s0).prod (gaussianReal 0 s0)).map
    Complex.measurableEquivRealProd.symm with hμZ
  set μR := ((gaussianReal 0 s1).prod (gaussianReal 0 s1)).map
    Complex.measurableEquivRealProd.symm with hμR
  -- the conditional density of `φ` given `I`; it vanishes for `I ≤ 0`, so needs no `if`
  set K : ℝ → ℝ → ℝ := fun I φ =>
    √(N * I / (Real.pi * (B2 - B1 ^ 2))) * Real.exp (-(N * I * (φ - B1) ^ 2 / (B2 - B1 ^ 2)))
    with hK_def
  have hK : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal (K q.1 q.2)) := by
    simp only [hK_def]; fun_prop
  -- law of `I = |Z|²`
  have hrad : μZ.map Complex.normSq = volume.withDensity (fun x => ENNReal.ofReal
      (if 0 < x then (2 * (s0 : ℝ))⁻¹ * Real.exp (-(2 * (s0 : ℝ))⁻¹ * x) else 0)) := by
    rw [hμZ, Measure.map_map Complex.continuous_normSq.measurable
      Complex.measurableEquivRealProd.symm.measurable,
      ← MathlibGap.gaussianReal_prod_map_sq_add_sq _ hs0ne]
    congr 1; funext p
    simp [Complex.normSq_apply, Complex.measurableEquivRealProd_symm_apply, sq]
  have hrate : (2 * (s0 : ℝ))⁻¹ = N := by rw [hs0r]; field_simp
  -- law of `B₁ + Re(R/z)` for fixed `z ≠ 0`
  have hinner : ∀ z : ℂ, z ≠ 0 → μR.map (fun r => B1 + (r / z).re) =
      volume.withDensity (fun φ => ENNReal.ofReal (K (Complex.normSq z) φ)) := by
    intro z hz
    have hnz : 0 < Complex.normSq z := Complex.normSq_pos.2 hz
    rw [hμR, Measure.map_map (by fun_prop) (by fun_prop)]
    have hfun : (fun r : ℂ => B1 + (r / z).re) ∘ Complex.measurableEquivRealProd.symm =
        fun p : ℝ × ℝ => B1 + (z.re / Complex.normSq z * p.1 + z.im / Complex.normSq z * p.2) := by
      funext p; simp [Complex.div_re, Complex.measurableEquivRealProd_symm_apply]; ring
    have hv : ((((z.re / Complex.normSq z) ^ 2 + (z.im / Complex.normSq z) ^ 2).toNNReal * s1 :
        NNReal) : ℝ) =
        (B2 - B1 ^ 2) / (2 * N * Complex.normSq z) := by
      have hn : z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by rw [Complex.normSq_apply]; ring
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), hs1r, div_pow, div_pow, ← add_div, hn]
      field_simp
    rw [hfun, gauss_lin, gaussianReal_of_var_ne_zero _ (by rw [← NNReal.coe_ne_zero, hv]; positivity)]
    congr 1; funext φ
    rw [gaussianPDF]
    congr 1
    rw [gaussianPDFReal, hv]
    congr 1
    · rw [← Real.sqrt_inv]; congr 1; field_simp
    · congr 1; field_simp
  have h0 : ∀ᵐ z ∂μZ, z ≠ 0 := by
    have h : (μZ.map Complex.normSq) {0} = 0 := by
      rw [hrad]; exact withDensity_absolutelyContinuous _ _ Real.volume_singleton
    rw [Measure.map_apply Complex.continuous_normSq.measurable (measurableSet_singleton 0),
      show Complex.normSq ⁻¹' {0} = {(0 : ℂ)} by ext; simp] at h
    filter_upwards [compl_mem_ae_iff.2 h] with z hz
    exact hz
  ext s hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs]
  have hf : Measurable (s.indicator (1 : ℝ × ℝ → ENNReal)) := measurable_one.indicator hs
  generalize s.indicator (1 : ℝ × ℝ → ENNReal) = f at hf ⊢
  have hF : Measurable (fun p : ℂ × ℂ => (Complex.normSq p.1, B1 + (p.2 / p.1).re)) := by
    fun_prop
  rw [lintegral_map hf hF,
    lintegral_prod (f := fun p : ℂ × ℂ => f (Complex.normSq p.1, B1 + (p.2 / p.1).re))
      (hf.comp hF).aemeasurable]
  have step1 : ∀ᵐ z ∂μZ, ∫⁻ r, f (Complex.normSq z, B1 + (r / z).re) ∂μR =
      ∫⁻ φ, ENNReal.ofReal (K (Complex.normSq z) φ) * f (Complex.normSq z, φ) := by
    filter_upwards [h0] with z hz
    rw [← lintegral_map (f := fun φ => f (Complex.normSq z, φ)) (by fun_prop) (by fun_prop),
      hinner z hz, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    rfl
  rw [lintegral_congr_ae step1]
  have hH : Measurable fun I => ∫⁻ φ, ENNReal.ofReal (K I φ) * f (I, φ) :=
    Measurable.lintegral_prod_right' (f := fun q : ℝ × ℝ => ENNReal.ofReal (K q.1 q.2) * f q)
      (hK.mul hf)
  have hρ : Measurable fun x : ℝ => ENNReal.ofReal
      (if 0 < x then (2 * (s0 : ℝ))⁻¹ * Real.exp (-(2 * (s0 : ℝ))⁻¹ * x) else 0) :=
    ENNReal.measurable_ofReal.comp
      (Measurable.ite (p := fun x : ℝ => 0 < x) measurableSet_Ioi (by fun_prop) measurable_const)
  have hκ : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (eq13Kernel N B1 B2 q.1 q.2) := by
    unfold eq13Kernel
    exact ENNReal.measurable_ofReal.comp (Measurable.ite (p := fun q : ℝ × ℝ => 0 < q.1)
      (measurableSet_lt measurable_const measurable_fst) (by fun_prop) measurable_const)
  rw [← lintegral_map (f := fun I => ∫⁻ φ, ENNReal.ofReal (K I φ) * f (I, φ)) hH
      Complex.continuous_normSq.measurable, hrad,
    lintegral_withDensity_eq_lintegral_mul _ hρ hH,
    lintegral_withDensity_eq_lintegral_mul _ hκ hf, Measure.volume_eq_prod,
    lintegral_prod _ (hκ.mul hf).aemeasurable]
  refine lintegral_congr fun I => ?_
  simp only [Pi.mul_apply]
  rw [← lintegral_const_mul _ (by fun_prop)]
  refine lintegral_congr fun φ => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by split_ifs <;> positivity)]
  congr 2
  rw [hrate]
  unfold eq13Kernel
  split_ifs with hI
  · have hsq : √((N : ℝ) ^ 3 * I / Real.pi) * (√(B2 - B1 ^ 2))⁻¹ =
        N * √(N * I / (Real.pi * (B2 - B1 ^ 2))) := by
      rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity),
        show (N : ℝ) ^ 3 * I / Real.pi * (B2 - B1 ^ 2)⁻¹ =
          N ^ 2 * (N * I / (Real.pi * (B2 - B1 ^ 2))) by field_simp,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hNpos.le]
    simp only [hK_def]
    rw [show -(N : ℝ) * I * (φ - B1) ^ 2 / (B2 - B1 ^ 2) = -(N * I * (φ - B1) ^ 2 / (B2 - B1 ^ 2))
      by ring]
    linear_combination (-(Real.exp (-(N : ℝ) * I) *
      Real.exp (-(N * I * (φ - B1) ^ 2 / (B2 - B1 ^ 2))))) * hsq
  · simp


private theorem condGauss_eq13 (N : ℕ) (hN : 1 ≤ N) (B1 B2 : ℝ) (hB : B1 ^ 2 < B2) :
    ((((gaussianReal 0 ((1 : ℝ).toNNReal / (2 * N))).prod
          (gaussianReal 0 ((1 : ℝ).toNNReal / (2 * N)))).map
            Complex.measurableEquivRealProd.symm).prod
        (((gaussianReal 0 ((B2 - B1 ^ 2).toNNReal / (2 * N))).prod
          (gaussianReal 0 ((B2 - B1 ^ 2).toNNReal / (2 * N)))).map
            Complex.measurableEquivRealProd.symm)).map
      (fun p : ℂ × ℂ => (Complex.normSq p.1, B1 + (p.2 / p.1).re)) =
    (volume : Measure (ℝ × ℝ)).withDensity
      (fun q => ENNReal.ofReal (eq13Kernel N B1 B2 q.1 q.2)) :=
  condGauss_eq13_aux N hN B1 B2 hB

end CondGauss


/-- The incident column as a function of `g` alone. -/
private noncomputable def uOf {N : ℕ} (g : Fin N → ℂ) (i : Fin N) : ℂ :=
  g i / ((Real.sqrt (∑ j, Complex.normSq (g j)) : ℝ) : ℂ)

private lemma sum_normSq_uOf {N : ℕ} (g : Fin N → ℂ) (hg : g ≠ 0) :
    ∑ i, Complex.normSq (uOf g i) = 1 := by
  have hS : (∑ j, Complex.normSq (g j)) ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, g i ≠ 0 := by
      by_contra h; push Not at h; exact hg (funext h)
    exact (lt_of_lt_of_le (Complex.normSq_pos.2 hi) (Finset.single_le_sum
      (f := fun j => Complex.normSq (g j)) (fun j _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i))).ne'
  simp_rw [uOf, map_div₀, Complex.normSq_ofReal,
    Real.mul_self_sqrt (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (g j))]
  rw [← Finset.sum_div, div_self hS]

/-- The two lowest coordinates of the Gaussian vector are nonzero almost surely. -/
private lemma ae_coords_ne_zero (N : ℕ) (hN : 2 ≤ N) :
    ∀ᵐ g ∂(gaussVec N), g ⟨0, by omega⟩ ≠ 0 ∧ g ⟨1, by omega⟩ ≠ 0 := by
  set i0 : Fin N := ⟨0, by omega⟩
  set i1 : Fin N := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hab : ∑ i, (Pi.single i0 (1 : ℂ) : Fin N → ℂ) i * (starRingEnd ℂ)
      ((Pi.single i1 (1 : ℂ) : Fin N → ℂ) i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h : i = i0
    · subst h; simp [Pi.single_apply, hne]
    · simp [Pi.single_apply, h]
  have hlaw := gaussVec_map_pair N _ _ hab
  have hpair : (fun v : Fin N → ℂ => (∑ i, (Pi.single i0 (1 : ℂ) : Fin N → ℂ) i * v i,
      ∑ i, (Pi.single i1 (1 : ℂ) : Fin N → ℂ) i * v i)) = fun v => (v i0, v i1) := by
    funext v; simp [Pi.single_apply]
  rw [hpair] at hlaw
  set s : NNReal := (∑ i, Complex.normSq ((Pi.single i0 (1 : ℂ) : Fin N → ℂ) i)).toNNReal / (2 * N)
  have hs1 : (∑ i, Complex.normSq ((Pi.single i1 (1 : ℂ) : Fin N → ℂ) i)).toNNReal / (2 * N) = s := by
    simp [s, Pi.single_apply]
  rw [hs1] at hlaw
  have hs : s ≠ 0 := by
    simp only [s, Pi.single_apply, apply_ite, map_one, map_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Real.toNNReal_one]
    exact div_ne_zero one_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast (show N ≠ 0 by omega)))
  have h0 : (((gaussianReal 0 s).prod (gaussianReal 0 s)).map Complex.measurableEquivRealProd.symm) {0} = 0 := by
    rw [Measure.map_apply Complex.measurableEquivRealProd.symm.measurable (measurableSet_singleton 0)]
    have : Complex.measurableEquivRealProd.symm ⁻¹' {(0 : ℂ)} = {(0 : ℝ)} ×ˢ {(0 : ℝ)} := by
      ext p; simp [Complex.measurableEquivRealProd_symm_apply, Complex.ext_iff, Prod.ext_iff]
    rw [this, Measure.prod_prod, gaussianReal_absolutelyContinuous 0 hs Real.volume_singleton, zero_mul]
  have hmeas : Measurable (fun v : Fin N → ℂ => (v i0, v i1)) := by fun_prop
  rw [ae_iff]
  have hsub : {g : Fin N → ℂ | ¬(g i0 ≠ 0 ∧ g i1 ≠ 0)} =
      (fun v : Fin N → ℂ => (v i0, v i1)) ⁻¹' (({0} ×ˢ univ) ∪ (univ ×ˢ {0})) := by
    ext g; simp [or_iff_not_imp_left]
  rw [hsub, ← Measure.map_apply hmeas (((measurableSet_singleton 0).prod MeasurableSet.univ).union
    (MeasurableSet.univ.prod (measurableSet_singleton 0))), hlaw]
  refine measure_union_null ?_ ?_ <;> rw [Measure.prod_prod] <;> simp [h0]

/-- Two rates of the Laguerre ensemble coincide with probability zero. -/
private lemma ae_rates_ne (N : ℕ) (hN : 2 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    ∀ᵐ μ ∂(laguerreEnsemble N γ), μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩ := by
  set i0 : Fin N := ⟨0, by omega⟩
  set i1 : Fin N := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set L : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i0) - LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i1
  have hker : {μ : Fin N → ℝ | ¬(μ i0 ≠ μ i1)} = (LinearMap.ker L : Set (Fin N → ℝ)) := by
    ext μ; simp [L, sub_eq_zero]
  have hnt : LinearMap.ker L ≠ ⊤ := by
    intro h
    have : (Pi.single i0 (1 : ℝ) : Fin N → ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simp [L, Pi.single_apply, hne.symm] at this
  have hvol : (volume : Measure (Fin N → ℝ)) (LinearMap.ker L) = 0 :=
    Measure.addHaar_submodule _ _ hnt
  rw [ae_iff, hker]
  unfold laguerreEnsemble
  rw [Measure.smul_apply, withDensity_absolutelyContinuous _ _ hvol, smul_zero]

/-- `B₂ - B₁²` is the variance of `τ` under the weights `|u_i|²`, positive in the generic case. -/
private lemma specMoment_sq_lt {N : ℕ} (hN : 2 ≤ N) (ω : Sample N)
    (hg : ω.1 ⟨0, by omega⟩ ≠ 0 ∧ ω.1 ⟨1, by omega⟩ ≠ 0)
    (hμ : ω.2.2 ⟨0, by omega⟩ ≠ ω.2.2 ⟨1, by omega⟩) :
    specMoment 1 ω ^ 2 < specMoment 2 ω := by
  obtain ⟨g, v, μ⟩ := ω
  set i0 : Fin N := ⟨0, by omega⟩
  set i1 : Fin N := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have hg0 : g ≠ 0 := fun h => hg.1 (by simp [h])
  set w : Fin N → ℝ := fun i => Complex.normSq (uOf g i)
  set t : Fin N → ℝ := fun i => (μ i)⁻¹
  have hw1 : ∑ i, w i = 1 := sum_normSq_uOf g hg0
  have hB1 : specMoment 1 ((g, v, μ) : Sample N) = ∑ i, w i * t i := by
    simp [specMoment, uVec, tau, w, t, uOf]
  have hB2 : specMoment 2 ((g, v, μ) : Sample N) = ∑ i, w i * t i ^ 2 := by
    simp [specMoment, uVec, tau, w, t, uOf]
  rw [hB1, hB2]
  set B := ∑ i, w i * t i
  have hvar : ∑ i, w i * t i ^ 2 - B ^ 2 = ∑ i, w i * (t i - B) ^ 2 := by
    have hexp : ∀ i, w i * (t i - B) ^ 2 = w i * t i ^ 2 - 2 * B * (w i * t i) + B ^ 2 * w i := by
      intro i; ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1]
    ring
  have hwnn : ∀ i, 0 ≤ w i := fun i => Complex.normSq_nonneg _
  have hwpos : ∀ i, g i ≠ 0 → 0 < w i := by
    intro i hi
    have hSpos : 0 < Real.sqrt (∑ j, Complex.normSq (g j)) := Real.sqrt_pos.2 (lt_of_lt_of_le
      (Complex.normSq_pos.2 hi) (Finset.single_le_sum (f := fun j => Complex.normSq (g j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)))
    exact Complex.normSq_pos.2 (div_ne_zero hi (Complex.ofReal_ne_zero.2 hSpos.ne'))
  have ht : t i0 ≠ t i1 := fun h => hμ (inv_injective h)
  have hpair : w i0 * (t i0 - B) ^ 2 + w i1 * (t i1 - B) ^ 2 ≤ ∑ i, w i * (t i - B) ^ 2 := by
    rw [← Finset.sum_pair hne (f := fun i => w i * (t i - B) ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => mul_nonneg (hwnn i) (sq_nonneg _)
  have hpos : 0 < w i0 * (t i0 - B) ^ 2 + w i1 * (t i1 - B) ^ 2 := by
    have h0 := hwpos i0 hg.1
    have h1 := hwpos i1 hg.2
    by_cases hb : t i0 = B
    · have : t i1 - B ≠ 0 := fun h => ht (by linarith)
      have := mul_pos h1 (pow_pos (abs_pos.2 this) 2)
      rw [sq_abs] at this
      nlinarith [mul_nonneg h0.le (sq_nonneg (t i0 - B))]
    · have : t i0 - B ≠ 0 := sub_ne_zero.2 hb
      have := mul_pos h0 (pow_pos (abs_pos.2 this) 2)
      rw [sq_abs] at this
      nlinarith [mul_nonneg h1.le (sq_nonneg (t i1 - B))]
  linarith

/-- Conditionally on `g` and the rates, `(I, φ')` has the eq. (13) density. -/
private lemma cond_law {N : ℕ} (hN : 2 ≤ N) (g : Fin N → ℂ) (μ : Fin N → ℝ)
    (hg : g ⟨0, by omega⟩ ≠ 0 ∧ g ⟨1, by omega⟩ ≠ 0) (hμ : μ ⟨0, by omega⟩ ≠ μ ⟨1, by omega⟩) :
    (gaussVec N).map (fun v => (intensityNe ((g, v, μ) : Sample N), delayNe ((g, v, μ) : Sample N))) =
      (volume : Measure (ℝ × ℝ)).withDensity (fun q => ENNReal.ofReal (eq13Kernel N
        (specMoment 1 ((g, 0, μ) : Sample N)) (specMoment 2 ((g, 0, μ) : Sample N)) q.1 q.2)) := by
  have hg0 : g ≠ 0 := fun h => hg.1 (by simp [h])
  set ω0 : Sample N := (g, 0, μ)
  set B1 := specMoment 1 ω0 with hB1def
  set B2 := specMoment 2 ω0 with hB2def
  set τ : Fin N → ℝ := fun i => (μ i)⁻¹
  set a : Fin N → ℂ := uOf g
  set b : Fin N → ℂ := fun i => ((τ i - B1 : ℝ) : ℂ) * uOf g i
  have hw1 := sum_normSq_uOf g hg0
  have hB1 : B1 = ∑ i, Complex.normSq (uOf g i) * τ i := by
    simp [hB1def, ω0, specMoment, uVec, tau, τ, uOf]
  have hB2 : B2 = ∑ i, Complex.normSq (uOf g i) * τ i ^ 2 := by
    simp [hB2def, ω0, specMoment, uVec, tau, τ, uOf]
  have hab : ∑ i, a i * (starRingEnd ℂ) (b i) = 0 := by
    have : ∀ i, a i * (starRingEnd ℂ) (b i) =
        ((Complex.normSq (uOf g i) * τ i - B1 * Complex.normSq (uOf g i) : ℝ) : ℂ) := by
      intro i
      simp only [a, b, map_mul, Complex.conj_ofReal]
      rw [mul_left_comm, Complex.mul_conj]
      push_cast; ring
    simp_rw [this]
    rw [← Complex.ofReal_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, ← hB1]
    simp
  have hsa : ∑ i, Complex.normSq (a i) = 1 := hw1
  have hsb : ∑ i, Complex.normSq (b i) = B2 - B1 ^ 2 := by
    have : ∀ i, Complex.normSq (b i) = Complex.normSq (uOf g i) * τ i ^ 2
        - 2 * B1 * (Complex.normSq (uOf g i) * τ i) + B1 ^ 2 * Complex.normSq (uOf g i) := by
      intro i; simp only [b, map_mul, Complex.normSq_ofReal]; ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw1, ← hB1, ← hB2]
    ring
  have hpair := gaussVec_map_pair N a b hab
  rw [hsa, hsb] at hpair
  have hlt : B1 ^ 2 < B2 := specMoment_sq_lt hN ω0 hg hμ
  have hcond := condGauss_eq13 N (by omega) B1 B2 hlt
  have hv1 : ((1 : ℝ).toNNReal / (2 * N) : NNReal) ≠ 0 := by
    rw [Real.toNNReal_one]
    exact div_ne_zero one_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast (show N ≠ 0 by omega)))
  -- `A₀ ≠ 0` almost surely
  have hA0 : ∀ᵐ v ∂(gaussVec N), ∑ i, a i * v i ≠ 0 := by
    have hmeas : Measurable (fun v : Fin N → ℂ => (∑ i, a i * v i, ∑ i, b i * v i)) := by fun_prop
    have h0 : (((gaussianReal 0 ((1 : ℝ).toNNReal / (2 * N))).prod
        (gaussianReal 0 ((1 : ℝ).toNNReal / (2 * N)))).map Complex.measurableEquivRealProd.symm) {0} = 0 := by
      rw [Measure.map_apply Complex.measurableEquivRealProd.symm.measurable (measurableSet_singleton 0)]
      have : Complex.measurableEquivRealProd.symm ⁻¹' {(0 : ℂ)} = {(0 : ℝ)} ×ˢ {(0 : ℝ)} := by
        ext p; simp [Complex.measurableEquivRealProd_symm_apply, Complex.ext_iff, Prod.ext_iff]
      rw [this, Measure.prod_prod, gaussianReal_absolutelyContinuous 0 hv1 Real.volume_singleton, zero_mul]
    rw [ae_iff]
    have hsub : {v : Fin N → ℂ | ¬(∑ i, a i * v i ≠ 0)} =
        (fun v : Fin N → ℂ => (∑ i, a i * v i, ∑ i, b i * v i)) ⁻¹' ({0} ×ˢ univ) := by
      ext v; simp
    rw [hsub, ← Measure.map_apply hmeas ((measurableSet_singleton 0).prod MeasurableSet.univ), hpair,
      Measure.prod_prod, h0, zero_mul]
  -- pointwise: `I = |A₀|²` and `φ' = B₁ + Re(R/A₀)` with `R = A₁ - B₁ A₀`
  have hF : (fun v => (intensityNe ((g, v, μ) : Sample N), delayNe ((g, v, μ) : Sample N))) =ᵐ[gaussVec N]
      (fun p : ℂ × ℂ => (Complex.normSq p.1, B1 + (p.2 / p.1).re)) ∘
        (fun v : Fin N → ℂ => (∑ i, a i * v i, ∑ i, b i * v i)) := by
    filter_upwards [hA0] with v hv
    have hA0v : ampA 0 ((g, v, μ) : Sample N) = ∑ i, a i * v i := by
      simp [ampA, uVec, vVec, a, uOf]
    have hA1v : ampA 1 ((g, v, μ) : Sample N) = (B1 : ℂ) * ∑ i, a i * v i + ∑ i, b i * v i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      simp only [ampA, uVec, vVec, tau, pow_one, a, b, uOf, τ]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    simp only [Function.comp_apply, intensityNe, delayNe, hA0v, hA1v]
    congr 1
    rw [add_div, mul_div_assoc, div_self hv, mul_one, Complex.add_re, Complex.ofReal_re]
  have hΦ : Measurable (fun p : ℂ × ℂ => (Complex.normSq p.1, B1 + (p.2 / p.1).re)) := by fun_prop
  have hpm : Measurable (fun v : Fin N → ℂ => (∑ i, a i * v i, ∑ i, b i * v i)) := by fun_prop
  rw [Measure.map_congr hF, ← Measure.map_map hΦ hpm, hpair, hcond]

private theorem joint_aux (N : ℕ) (hN : 2 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    (localizedModel N γ).map (fun ω => (intensityNe ω, delayNe ω)) =
      (volume : Measure (ℝ × ℝ)).withDensity (fun q =>
        ∫⁻ ω, ENNReal.ofReal (eq13Kernel N (specMoment 1 ω) (specMoment 2 ω) q.1 q.2)
          ∂(localizedModel N γ)) := by
  have hG := gaussVec_isProbabilityMeasure N
  have hL := laguerreEnsemble_isProbabilityMeasure N γ hγ
  have hM := localizedModel_isProbabilityMeasure N γ hγ
  have hk : Measurable (fun p : Sample N × (ℝ × ℝ) => ENNReal.ofReal
      (eq13Kernel N (specMoment 1 p.1) (specMoment 2 p.1) p.2.1 p.2.2)) := by
    unfold eq13Kernel specMoment uVec tau
    exact Measurable.ennreal_ofReal (Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      (by fun_prop) measurable_const)
  have hFm : Measurable (fun ω : Sample N => (intensityNe ω, delayNe ω)) := by
    unfold intensityNe delayNe ampA uVec vVec tau; fun_prop
  ext S hS
  rw [Measure.map_apply hFm hS, withDensity_apply _ hS]
  -- `h ω = ∫_S kernel(ω, q) dq`, which does not depend on the detected column
  set h : Sample N → ENNReal := fun ω => ∫⁻ q in S, ENNReal.ofReal
    (eq13Kernel N (specMoment 1 ω) (specMoment 2 ω) q.1 q.2) with hh
  have hhm : Measurable h := hk.lintegral_prod_right'
  have hrhs : ∫⁻ q in S, ∫⁻ ω, ENNReal.ofReal (eq13Kernel N (specMoment 1 ω) (specMoment 2 ω) q.1 q.2)
      ∂(localizedModel N γ) = ∫⁻ ω, h ω ∂(localizedModel N γ) :=
    lintegral_lintegral_swap (f := fun (q : ℝ × ℝ) (ω : Sample N) => ENNReal.ofReal
      (eq13Kernel N (specMoment 1 ω) (specMoment 2 ω) q.1 q.2))
      (hk.comp (measurable_snd.prodMk measurable_fst)).aemeasurable
  rw [hrhs, ← lintegral_indicator_one (hFm hS)]
  have hind : Measurable (((fun ω : Sample N => (intensityNe ω, delayNe ω)) ⁻¹' S).indicator
      (1 : Sample N → ENNReal)) := measurable_one.indicator (hFm hS)
  unfold localizedModel
  rw [lintegral_prod _ hind.aemeasurable, lintegral_prod _ hhm.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_coords_ne_zero N hN] with g hg
  rw [lintegral_prod_symm (fun p => ((fun ω : Sample N => (intensityNe ω, delayNe ω)) ⁻¹' S).indicator 1 (g, p))
      (hind.comp measurable_prodMk_left).aemeasurable,
    lintegral_prod_symm (fun p => h (g, p)) (hhm.comp measurable_prodMk_left).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_rates_ne N hN γ hγ] with μ hμ
  -- inner integral over the detected column `v`
  have hcl := cond_law hN g μ hg hμ
  have hFv : Measurable (fun v => (intensityNe ((g, v, μ) : Sample N), delayNe ((g, v, μ) : Sample N))) :=
    hFm.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  calc ∫⁻ v, ((fun ω : Sample N => (intensityNe ω, delayNe ω)) ⁻¹' S).indicator 1 (g, v, μ) ∂(gaussVec N)
      = (gaussVec N) ((fun v => (intensityNe ((g, v, μ) : Sample N),
          delayNe ((g, v, μ) : Sample N))) ⁻¹' S) := by
        rw [← lintegral_indicator_one (hFv hS)]; rfl
    _ = ((volume : Measure (ℝ × ℝ)).withDensity (fun q => ENNReal.ofReal (eq13Kernel N
          (specMoment 1 ((g, 0, μ) : Sample N)) (specMoment 2 ((g, 0, μ) : Sample N)) q.1 q.2))) S := by
        rw [← Measure.map_apply hFv hS, hcl]
    _ = h ((g, 0, μ) : Sample N) := withDensity_apply _ hS
    _ = ∫⁻ v, h ((g, v, μ) : Sample N) ∂(gaussVec N) := by
        rw [show (∫⁻ v, h ((g, v, μ) : Sample N) ∂(gaussVec N)) =
            ∫⁻ _v, h ((g, 0, μ) : Sample N) ∂(gaussVec N) from rfl, lintegral_const, measure_univ, mul_one]

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (N : ℕ) (hN : 2 ≤ N) (γ : ℝ) (hγ : 0 < γ) :
    (localizedModel N γ).map (fun ω => (intensityNe ω, delayNe ω)) =
      (volume : Measure (ℝ × ℝ)).withDensity (fun q =>
        ∫⁻ ω, ENNReal.ofReal (eq13Kernel N (specMoment 1 ω) (specMoment 2 ω) q.1 q.2)
          ∂(localizedModel N γ)) :=
  joint_aux N hN γ hγ
