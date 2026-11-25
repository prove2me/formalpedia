-- Prove2me | solution 1 for Arxiv0812_1178.cartesian_moments_polar_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T17:42:14.533226+00:00
-- url     : https://prove2.me/submissions/f92b6cac-f068-4229-af16-a72e9c8362f7

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix Arxiv0812_1178
open scoped RealInnerProductSpace

private lemma radNoise_eq {ι : Type*} (abar phibar anoise phinoise : ι → ℝ) (i : ι) :
    radNoise abar phibar anoise phinoise i =
      (abar i + anoise i) * Real.cos (phinoise i) - abar i := by
  unfold radNoise polarNoise
  have h1 : Complex.exp (Complex.I * ((phibar i + phinoise i : ℝ) : ℂ)) *
      Complex.exp (-(Complex.I * (phibar i : ℂ))) =
      Complex.exp ((phinoise i : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (Complex.I * (phibar i : ℂ)) *
      Complex.exp (-(Complex.I * (phibar i : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [sub_mul, mul_assoc, h1, mul_assoc, h2, mul_one, Complex.sub_re,
    Complex.mul_re, Complex.exp_ofReal_mul_I_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma tanNoise_eq {ι : Type*} (abar phibar anoise phinoise : ι → ℝ) (i : ι) :
    tanNoise abar phibar anoise phinoise i =
      (abar i + anoise i) * Real.sin (phinoise i) := by
  unfold tanNoise polarNoise
  have h1 : Complex.exp (Complex.I * ((phibar i + phinoise i : ℝ) : ℂ)) *
      Complex.exp (-(Complex.I * (phibar i : ℂ))) =
      Complex.exp ((phinoise i : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (Complex.I * (phibar i : ℂ)) *
      Complex.exp (-(Complex.I * (phibar i : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [sub_mul, mul_assoc, h1, mul_assoc, h2, mul_one, Complex.sub_im,
    Complex.mul_im, Complex.exp_ofReal_mul_I_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma integral_cos_sin_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (x : EuclideanSpace ℝ ι) :
    (∫ u, Real.cos ⟪u, x⟫ ∂(multivariateGaussian 0 S) =
      Real.exp (-(x ⬝ᵥ S *ᵥ x / 2))) ∧
    (∫ u, Real.sin ⟪u, x⟫ ∂(multivariateGaussian 0 S) = 0) := by
  have hcf := charFun_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hS x
  rw [charFun_apply] at hcf
  have hsimp : Complex.exp (⟪x, (0 : EuclideanSpace ℝ ι)⟫ * Complex.I -
      ↑(x ⬝ᵥ S *ᵥ x) / 2) = (Real.exp (-(x ⬝ᵥ S *ᵥ x / 2)) : ℂ) := by
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hsimp] at hcf
  have hint : Integrable (fun u : EuclideanSpace ℝ ι => Complex.exp (↑⟪u, x⟫ * Complex.I))
      (multivariateGaussian 0 S) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable ?_) 1 ?_
    · exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_id.inner continuous_const)).mul continuous_const)
    · filter_upwards with u
      rw [Complex.norm_exp_ofReal_mul_I]
  have hre := congr_arg Complex.re hcf
  have him := congr_arg Complex.im hcf
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint] at hre
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint] at him
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  exact ⟨hre, him⟩

theorem solution {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (abar phibar : ι → ℝ)
    (Ra Rφ : Matrix ι ι ℝ) (hRa : Ra.PosSemidef) (hRφ : Rφ.PosSemidef)
    (anoise phinoise : Ω → EuclideanSpace ℝ ι) (ham : Measurable anoise)
    (hφm : Measurable phinoise) (hag : Pr.map anoise = multivariateGaussian 0 Ra)
    (hφg : Pr.map phinoise = multivariateGaussian 0 Rφ) (hind : IndepFun anoise phinoise Pr) :
    (∀ i, ∫ ω, radNoise abar phibar (fun j => anoise ω j) (fun j => phinoise ω j) i ∂Pr =
      abar i * (Real.exp (-(Rφ i i / 2)) - 1)) ∧
    (∀ i, ∫ ω, tanNoise abar phibar (fun j => anoise ω j) (fun j => phinoise ω j) i ∂Pr = 0) ∧
    (∀ i j, covariance
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr =
      (abar i * abar j * (Real.cosh (Rφ i j) - 1) + Ra i j * Real.cosh (Rφ i j)) *
        Real.exp (-((Rφ i i + Rφ j j) / 2))) ∧
    (∀ i j, covariance
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr = 0) ∧
    (∀ i j, covariance
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr =
      (abar i * abar j + Ra i j) * Real.sinh (Rφ i j) * Real.exp (-((Rφ i i + Rφ j j) / 2))) := by
  have hRφ_sym : ∀ i j, Rφ j i = Rφ i j := fun i j => by
    have := congr_fun (congr_fun hRφ.isHermitian.eq j) i
    simpa using this.symm
  let e : ι → EuclideanSpace ℝ ι := fun i => WithLp.toLp 2 (Pi.single i (1 : ℝ))
  have hinner_e : ∀ (u : EuclideanSpace ℝ ι) (i : ι), ⟪u, e i⟫ = u i := by
    intro u i
    simp [e, PiLp.inner_apply, RCLike.inner_apply]
  have hquad_e : ∀ i j : ι, (e i).ofLp ⬝ᵥ Rφ *ᵥ (e j).ofLp = Rφ i j := by
    intro i j
    simp [e, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hcos1 : ∀ i, ∫ ω, Real.cos (phinoise ω i) ∂Pr = Real.exp (-(Rφ i i / 2)) := by
    intro i
    have hcont : Continuous (fun u : EuclideanSpace ℝ ι => Real.cos (u i)) :=
      Real.continuous_cos.comp (EuclideanSpace.proj i).continuous
    rw [← integral_map hφm.aemeasurable hcont.aestronglyMeasurable, hφg]
    have := (integral_cos_sin_multivariateGaussian hRφ (e i)).1
    simpa [hinner_e, hquad_e] using this
  have hsin1 : ∀ i, ∫ ω, Real.sin (phinoise ω i) ∂Pr = 0 := by
    intro i
    have hcont : Continuous (fun u : EuclideanSpace ℝ ι => Real.sin (u i)) :=
      Real.continuous_sin.comp (EuclideanSpace.proj i).continuous
    rw [← integral_map hφm.aemeasurable hcont.aestronglyMeasurable, hφg]
    have := (integral_cos_sin_multivariateGaussian hRφ (e i)).2
    simpa [hinner_e] using this
  have hcos_add : ∀ i j, ∫ ω, Real.cos (phinoise ω i + phinoise ω j) ∂Pr =
      Real.exp (-((Rφ i i + 2 * Rφ i j + Rφ j j) / 2)) := by
    intro i j
    have hcont : Continuous (fun u : EuclideanSpace ℝ ι => Real.cos (u i + u j)) :=
      Real.continuous_cos.comp ((EuclideanSpace.proj i).continuous.add (EuclideanSpace.proj j).continuous)
    rw [← integral_map hφm.aemeasurable hcont.aestronglyMeasurable, hφg]
    have h := (integral_cos_sin_multivariateGaussian hRφ (e i + e j)).1
    have hi : ∀ u : EuclideanSpace ℝ ι, ⟪u, e i + e j⟫ = u i + u j := fun u => by
      rw [inner_add_right, hinner_e, hinner_e]
    have hq : (e i + e j).ofLp ⬝ᵥ Rφ *ᵥ (e i + e j).ofLp = Rφ i i + 2 * Rφ i j + Rφ j j := by
      have : (e i + e j).ofLp = (e i).ofLp + (e j).ofLp := rfl
      rw [this, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
        hquad_e, hquad_e, hquad_e, hquad_e, hRφ_sym i j]
      ring
    rw [hq] at h
    simpa [hi] using h
  have hsin_add : ∀ i j, ∫ ω, Real.sin (phinoise ω i + phinoise ω j) ∂Pr = 0 := by
    intro i j
    have hcont : Continuous (fun u : EuclideanSpace ℝ ι => Real.sin (u i + u j)) :=
      Real.continuous_sin.comp ((EuclideanSpace.proj i).continuous.add (EuclideanSpace.proj j).continuous)
    rw [← integral_map hφm.aemeasurable hcont.aestronglyMeasurable, hφg]
    have h := (integral_cos_sin_multivariateGaussian hRφ (e i + e j)).2
    have hi : ∀ u : EuclideanSpace ℝ ι, ⟪u, e i + e j⟫ = u i + u j := fun u => by
      rw [inner_add_right, hinner_e, hinner_e]
    simpa [hi] using h
  have hcos_sub : ∀ i j, ∫ ω, Real.cos (phinoise ω i - phinoise ω j) ∂Pr =
      Real.exp (-((Rφ i i - 2 * Rφ i j + Rφ j j) / 2)) := by
    intro i j
    have hcont : Continuous (fun u : EuclideanSpace ℝ ι => Real.cos (u i - u j)) :=
      Real.continuous_cos.comp ((EuclideanSpace.proj i).continuous.sub (EuclideanSpace.proj j).continuous)
    rw [← integral_map hφm.aemeasurable hcont.aestronglyMeasurable, hφg]
    have h := (integral_cos_sin_multivariateGaussian hRφ (e i - e j)).1
    have hi : ∀ u : EuclideanSpace ℝ ι, ⟪u, e i - e j⟫ = u i - u j := fun u => by
      rw [inner_sub_right, hinner_e, hinner_e]
    have hq : (e i - e j).ofLp ⬝ᵥ Rφ *ᵥ (e i - e j).ofLp = Rφ i i - 2 * Rφ i j + Rφ j j := by
      have : (e i - e j).ofLp = (e i).ofLp - (e j).ofLp := rfl
      rw [this, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        hquad_e, hquad_e, hquad_e, hquad_e, hRφ_sym i j]
      ring
    rw [hq] at h
    simpa [hi] using h
  have hsin_sub : ∀ i j, ∫ ω, Real.sin (phinoise ω i - phinoise ω j) ∂Pr = 0 := by
    intro i j
    have hcont : Continuous (fun u : EuclideanSpace ℝ ι => Real.sin (u i - u j)) :=
      Real.continuous_sin.comp ((EuclideanSpace.proj i).continuous.sub (EuclideanSpace.proj j).continuous)
    rw [← integral_map hφm.aemeasurable hcont.aestronglyMeasurable, hφg]
    have h := (integral_cos_sin_multivariateGaussian hRφ (e i - e j)).2
    have hi : ∀ u : EuclideanSpace ℝ ι, ⟪u, e i - e j⟫ = u i - u j := fun u => by
      rw [inner_sub_right, hinner_e, hinner_e]
    simpa [hi] using h
  have hint_cos_add : ∀ i j, Integrable (fun ω => Real.cos (phinoise ω i + phinoise ω j)) Pr := by
    intro i j
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ω => by simpa using Real.abs_cos_le_one _)
    have hm : Measurable (fun ω => Real.cos (phinoise ω i + phinoise ω j)) :=
      Real.continuous_cos.measurable.comp
        (((EuclideanSpace.proj i).continuous.measurable.comp hφm).add
          ((EuclideanSpace.proj j).continuous.measurable.comp hφm))
    exact hm.aestronglyMeasurable
  have hint_cos_sub : ∀ i j, Integrable (fun ω => Real.cos (phinoise ω i - phinoise ω j)) Pr := by
    intro i j
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ω => by simpa using Real.abs_cos_le_one _)
    have hm : Measurable (fun ω => Real.cos (phinoise ω i - phinoise ω j)) :=
      Real.continuous_cos.measurable.comp
        (((EuclideanSpace.proj i).continuous.measurable.comp hφm).sub
          ((EuclideanSpace.proj j).continuous.measurable.comp hφm))
    exact hm.aestronglyMeasurable
  have hint_sin_add : ∀ i j, Integrable (fun ω => Real.sin (phinoise ω i + phinoise ω j)) Pr := by
    intro i j
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ω => by simpa using Real.abs_sin_le_one _)
    have hm : Measurable (fun ω => Real.sin (phinoise ω i + phinoise ω j)) :=
      Real.continuous_sin.measurable.comp
        (((EuclideanSpace.proj i).continuous.measurable.comp hφm).add
          ((EuclideanSpace.proj j).continuous.measurable.comp hφm))
    exact hm.aestronglyMeasurable
  have hint_sin_sub : ∀ i j, Integrable (fun ω => Real.sin (phinoise ω i - phinoise ω j)) Pr := by
    intro i j
    refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ω => by simpa using Real.abs_sin_le_one _)
    have hm : Measurable (fun ω => Real.sin (phinoise ω i - phinoise ω j)) :=
      Real.continuous_sin.measurable.comp
        (((EuclideanSpace.proj i).continuous.measurable.comp hφm).sub
          ((EuclideanSpace.proj j).continuous.measurable.comp hφm))
    exact hm.aestronglyMeasurable
  have hcos_cos : ∀ i j, ∫ ω, Real.cos (phinoise ω i) * Real.cos (phinoise ω j) ∂Pr =
      Real.cosh (Rφ i j) * Real.exp (-((Rφ i i + Rφ j j) / 2)) := by
    intro i j
    have hpt : (fun ω => Real.cos (phinoise ω i) * Real.cos (phinoise ω j)) =
        fun ω => (Real.cos (phinoise ω i + phinoise ω j) + Real.cos (phinoise ω i - phinoise ω j)) / 2 := by
      ext ω
      rw [Real.cos_add, Real.cos_sub]
      ring
    rw [hpt, integral_div, integral_add (hint_cos_add i j) (hint_cos_sub i j),
      hcos_add, hcos_sub, Real.cosh_eq]
    have ha : -((Rφ i i + 2 * Rφ i j + Rφ j j) / 2) = -(Rφ i j) + -((Rφ i i + Rφ j j) / 2) := by ring
    have hs : -((Rφ i i - 2 * Rφ i j + Rφ j j) / 2) = Rφ i j + -((Rφ i i + Rφ j j) / 2) := by ring
    rw [ha, hs, Real.exp_add, Real.exp_add]
    ring
  have hsin_sin : ∀ i j, ∫ ω, Real.sin (phinoise ω i) * Real.sin (phinoise ω j) ∂Pr =
      Real.sinh (Rφ i j) * Real.exp (-((Rφ i i + Rφ j j) / 2)) := by
    intro i j
    have hpt : (fun ω => Real.sin (phinoise ω i) * Real.sin (phinoise ω j)) =
        fun ω => (Real.cos (phinoise ω i - phinoise ω j) - Real.cos (phinoise ω i + phinoise ω j)) / 2 := by
      ext ω
      rw [Real.cos_sub, Real.cos_add]
      ring
    rw [hpt, integral_div, integral_sub (hint_cos_sub i j) (hint_cos_add i j),
      hcos_sub, hcos_add, Real.sinh_eq]
    have ha : -((Rφ i i + 2 * Rφ i j + Rφ j j) / 2) = -(Rφ i j) + -((Rφ i i + Rφ j j) / 2) := by ring
    have hs : -((Rφ i i - 2 * Rφ i j + Rφ j j) / 2) = Rφ i j + -((Rφ i i + Rφ j j) / 2) := by ring
    rw [ha, hs, Real.exp_add, Real.exp_add]
    ring
  have hcos_sin : ∀ i j, ∫ ω, Real.cos (phinoise ω i) * Real.sin (phinoise ω j) ∂Pr = 0 := by
    intro i j
    have hpt : (fun ω => Real.cos (phinoise ω i) * Real.sin (phinoise ω j)) =
        fun ω => (Real.sin (phinoise ω i + phinoise ω j) - Real.sin (phinoise ω i - phinoise ω j)) / 2 := by
      ext ω
      rw [Real.sin_add, Real.sin_sub]
      ring
    rw [hpt, integral_div, integral_sub (hint_sin_add i j) (hint_sin_sub i j),
      hsin_add, hsin_sub]
    ring
  have ha_memLp : ∀ i, MemLp (fun ω => anoise ω i) 2 Pr := by
    intro i
    have hcomp : MemLp (fun u : EuclideanSpace ℝ ι => u i) 2 (Pr.map anoise) := by
      rw [hag]
      refine (IsGaussian.memLp_two_id (μ := multivariateGaussian 0 Ra)).mono
        (EuclideanSpace.proj i).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => ?_)
      exact PiLp.norm_apply_le u i
    exact (memLp_map_measure_iff hcomp.aestronglyMeasurable ham.aemeasurable).mp hcomp
  have ha_int : ∀ i, Integrable (fun ω => anoise ω i) Pr :=
    fun i => (ha_memLp i).integrable one_le_two
  have ha_mean : ∀ i, ∫ ω, anoise ω i ∂Pr = 0 := by
    intro i
    have hcont : Continuous (fun u : EuclideanSpace ℝ ι => u i) := (EuclideanSpace.proj i).continuous
    rw [← integral_map ham.aemeasurable hcont.aestronglyMeasurable, hag]
    have := (EuclideanSpace.proj i).integral_comp_id_comm
      (IsGaussian.integrable_id (μ := multivariateGaussian 0 Ra))
    simpa [integral_id_multivariateGaussian] using this
  have ha_cov : ∀ i j, ∫ ω, anoise ω i * anoise ω j ∂Pr = Ra i j := by
    intro i j
    have hcov := covariance_eq_sub (ha_memLp i) (ha_memLp j)
    simp only [Pi.mul_apply, ha_mean i, ha_mean j, mul_zero, sub_zero] at hcov
    rw [← hcov]
    have hci : Continuous (fun u : EuclideanSpace ℝ ι => u i) := (EuclideanSpace.proj i).continuous
    have hcj : Continuous (fun u : EuclideanSpace ℝ ι => u j) := (EuclideanSpace.proj j).continuous
    rw [show (fun ω => anoise ω i) = (fun u : EuclideanSpace ℝ ι => u i) ∘ anoise from rfl,
      show (fun ω => anoise ω j) = (fun u : EuclideanSpace ℝ ι => u j) ∘ anoise from rfl,
      ← covariance_map hci.aestronglyMeasurable hcj.aestronglyMeasurable ham.aemeasurable,
      hag, covariance_eval_multivariateGaussian hRa]
  have ha_add_mean : ∀ i, ∫ ω, (abar i + anoise ω i) ∂Pr = abar i := by
    intro i
    rw [integral_add (integrable_const _) (ha_int i), integral_const, ha_mean i]
    simp
  have ha_add_mul : ∀ i j,
      ∫ ω, (abar i + anoise ω i) * (abar j + anoise ω j) ∂Pr = abar i * abar j + Ra i j := by
    intro i j
    have hexp : (fun ω => (abar i + anoise ω i) * (abar j + anoise ω j)) =
        fun ω => (abar i * abar j + abar i * anoise ω j) +
          (anoise ω i * abar j + anoise ω i * anoise ω j) := by
      ext ω; ring
    have hprod_int : Integrable (fun ω => anoise ω i * anoise ω j) Pr :=
      (ha_memLp i).integrable_mul (ha_memLp j)
    have h1 : Integrable (fun ω => abar i * abar j + abar i * anoise ω j) Pr :=
      (integrable_const _).add ((ha_int j).const_mul _)
    have h2 : Integrable (fun ω => anoise ω i * abar j + anoise ω i * anoise ω j) Pr :=
      ((ha_int i).mul_const _).add hprod_int
    rw [hexp, integral_add h1 h2,
      integral_add (integrable_const _) ((ha_int j).const_mul _),
      integral_add ((ha_int i).mul_const _) hprod_int,
      integral_const, integral_const_mul, integral_mul_const, ha_mean i, ha_mean j, ha_cov i j]
    simp
  have hmemLp_rad0 : ∀ i, MemLp (fun ω => (abar i + anoise ω i) * Real.cos (phinoise ω i)) 2 Pr := by
    intro i
    have hbase : MemLp (fun ω => abar i + anoise ω i) 2 Pr :=
      (memLp_const (abar i)).add (ha_memLp i)
    refine hbase.mono ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((continuous_const.add (EuclideanSpace.proj i).continuous).measurable.comp ham |>.mul
        (Real.continuous_cos.measurable.comp ((EuclideanSpace.proj i).continuous.measurable.comp hφm))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      calc |abar i + anoise ω i| * |Real.cos (phinoise ω i)|
          ≤ |abar i + anoise ω i| * 1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |abar i + anoise ω i| := mul_one _
  have hmemLp_tan0 : ∀ i, MemLp (fun ω => (abar i + anoise ω i) * Real.sin (phinoise ω i)) 2 Pr := by
    intro i
    have hbase : MemLp (fun ω => abar i + anoise ω i) 2 Pr :=
      (memLp_const (abar i)).add (ha_memLp i)
    refine hbase.mono ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((continuous_const.add (EuclideanSpace.proj i).continuous).measurable.comp ham |>.mul
        (Real.continuous_sin.measurable.comp ((EuclideanSpace.proj i).continuous.measurable.comp hφm))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      calc |abar i + anoise ω i| * |Real.sin (phinoise ω i)|
          ≤ |abar i + anoise ω i| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
        _ = |abar i + anoise ω i| := mul_one _
  have hE_rad0 : ∀ i, ∫ ω, (abar i + anoise ω i) * Real.cos (phinoise ω i) ∂Pr =
      abar i * Real.exp (-(Rφ i i / 2)) := by
    intro i
    have hca : Continuous (fun u : EuclideanSpace ℝ ι => abar i + u i) :=
      continuous_const.add (EuclideanSpace.proj i).continuous
    have hcφ : Continuous (fun u : EuclideanSpace ℝ ι => Real.cos (u i)) :=
      Real.continuous_cos.comp (EuclideanSpace.proj i).continuous
    rw [hind.integral_fun_comp_mul_comp ham.aemeasurable hφm.aemeasurable
        hca.aestronglyMeasurable hcφ.aestronglyMeasurable,
      ha_add_mean i, hcos1 i]
  have hE_tan0 : ∀ i, ∫ ω, (abar i + anoise ω i) * Real.sin (phinoise ω i) ∂Pr = 0 := by
    intro i
    have hca : Continuous (fun u : EuclideanSpace ℝ ι => abar i + u i) :=
      continuous_const.add (EuclideanSpace.proj i).continuous
    have hcφ : Continuous (fun u : EuclideanSpace ℝ ι => Real.sin (u i)) :=
      Real.continuous_sin.comp (EuclideanSpace.proj i).continuous
    rw [hind.integral_fun_comp_mul_comp ham.aemeasurable hφm.aemeasurable
        hca.aestronglyMeasurable hcφ.aestronglyMeasurable,
      ha_add_mean i, hsin1 i, mul_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp_rw [radNoise_eq]
    rw [integral_sub ((hmemLp_rad0 i).integrable one_le_two) (integrable_const _),
      hE_rad0 i, integral_const]
    simp [mul_sub]
  · intro i
    simp_rw [tanNoise_eq]
    exact hE_tan0 i
  · intro i j
    simp_rw [radNoise_eq]
    rw [covariance_sub_const_left ((hmemLp_rad0 i).integrable one_le_two),
      covariance_sub_const_right ((hmemLp_rad0 j).integrable one_le_two),
      covariance_eq_sub (hmemLp_rad0 i) (hmemLp_rad0 j),
      hE_rad0 i, hE_rad0 j]
    simp only [Pi.mul_apply]
    have hmul : (fun ω => (abar i + anoise ω i) * Real.cos (phinoise ω i) *
          ((abar j + anoise ω j) * Real.cos (phinoise ω j))) =
        fun ω => ((abar i + anoise ω i) * (abar j + anoise ω j)) *
          (Real.cos (phinoise ω i) * Real.cos (phinoise ω j)) := by
      ext ω; ring
    rw [hmul]
    have hca : Continuous (fun u : EuclideanSpace ℝ ι => (abar i + u i) * (abar j + u j)) :=
      (continuous_const.add (EuclideanSpace.proj i).continuous).mul
        (continuous_const.add (EuclideanSpace.proj j).continuous)
    have hcφ : Continuous (fun u : EuclideanSpace ℝ ι => Real.cos (u i) * Real.cos (u j)) :=
      (Real.continuous_cos.comp (EuclideanSpace.proj i).continuous).mul
        (Real.continuous_cos.comp (EuclideanSpace.proj j).continuous)
    rw [hind.integral_fun_comp_mul_comp ham.aemeasurable hφm.aemeasurable
        hca.aestronglyMeasurable hcφ.aestronglyMeasurable,
      ha_add_mul i j, hcos_cos i j]
    have hexp : Real.exp (-(Rφ i i / 2)) * Real.exp (-(Rφ j j / 2)) =
        Real.exp (-((Rφ i i + Rφ j j) / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (abar i * abar j + Ra i j) * (Real.cosh (Rφ i j) * Real.exp (-((Rφ i i + Rφ j j) / 2))) -
          abar i * Real.exp (-(Rφ i i / 2)) * (abar j * Real.exp (-(Rφ j j / 2)))
        = (abar i * abar j + Ra i j) * (Real.cosh (Rφ i j) * Real.exp (-((Rφ i i + Rφ j j) / 2))) -
          abar i * abar j * (Real.exp (-(Rφ i i / 2)) * Real.exp (-(Rφ j j / 2))) := by ring
      _ = (abar i * abar j * (Real.cosh (Rφ i j) - 1) + Ra i j * Real.cosh (Rφ i j)) *
          Real.exp (-((Rφ i i + Rφ j j) / 2)) := by rw [hexp]; ring
  · intro i j
    simp_rw [radNoise_eq, tanNoise_eq]
    rw [covariance_sub_const_left ((hmemLp_rad0 i).integrable one_le_two),
      covariance_eq_sub (hmemLp_rad0 i) (hmemLp_tan0 j),
      hE_tan0 j, mul_zero, sub_zero]
    simp only [Pi.mul_apply]
    have hmul : (fun ω => (abar i + anoise ω i) * Real.cos (phinoise ω i) *
          ((abar j + anoise ω j) * Real.sin (phinoise ω j))) =
        fun ω => ((abar i + anoise ω i) * (abar j + anoise ω j)) *
          (Real.cos (phinoise ω i) * Real.sin (phinoise ω j)) := by
      ext ω; ring
    rw [hmul]
    have hca : Continuous (fun u : EuclideanSpace ℝ ι => (abar i + u i) * (abar j + u j)) :=
      (continuous_const.add (EuclideanSpace.proj i).continuous).mul
        (continuous_const.add (EuclideanSpace.proj j).continuous)
    have hcφ : Continuous (fun u : EuclideanSpace ℝ ι => Real.cos (u i) * Real.sin (u j)) :=
      (Real.continuous_cos.comp (EuclideanSpace.proj i).continuous).mul
        (Real.continuous_sin.comp (EuclideanSpace.proj j).continuous)
    rw [hind.integral_fun_comp_mul_comp ham.aemeasurable hφm.aemeasurable
        hca.aestronglyMeasurable hcφ.aestronglyMeasurable,
      hcos_sin i j, mul_zero]
  · intro i j
    simp_rw [tanNoise_eq]
    rw [covariance_eq_sub (hmemLp_tan0 i) (hmemLp_tan0 j),
      hE_tan0 i, zero_mul, sub_zero]
    simp only [Pi.mul_apply]
    have hmul : (fun ω => (abar i + anoise ω i) * Real.sin (phinoise ω i) *
          ((abar j + anoise ω j) * Real.sin (phinoise ω j))) =
        fun ω => ((abar i + anoise ω i) * (abar j + anoise ω j)) *
          (Real.sin (phinoise ω i) * Real.sin (phinoise ω j)) := by
      ext ω; ring
    rw [hmul]
    have hca : Continuous (fun u : EuclideanSpace ℝ ι => (abar i + u i) * (abar j + u j)) :=
      (continuous_const.add (EuclideanSpace.proj i).continuous).mul
        (continuous_const.add (EuclideanSpace.proj j).continuous)
    have hcφ : Continuous (fun u : EuclideanSpace ℝ ι => Real.sin (u i) * Real.sin (u j)) :=
      (Real.continuous_sin.comp (EuclideanSpace.proj i).continuous).mul
        (Real.continuous_sin.comp (EuclideanSpace.proj j).continuous)
    rw [hind.integral_fun_comp_mul_comp ham.aemeasurable hφm.aemeasurable
        hca.aestronglyMeasurable hcφ.aestronglyMeasurable,
      ha_add_mul i j, hsin_sin i j]
    ring
