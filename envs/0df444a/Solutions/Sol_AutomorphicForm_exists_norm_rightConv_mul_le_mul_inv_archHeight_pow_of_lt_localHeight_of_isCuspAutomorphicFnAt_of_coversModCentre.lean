-- Prove2me | solution 1 for AutomorphicForm.exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/43ede3f3-7075-5ac0-a0e9-192e8f4486ee

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn
import Theorems.Thm_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open scoped ENNReal NNReal ProbabilityTheory

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

namespace CuspDecayAux

variable (K : Type) [Field K] [NumberField K]

theorem rightConv_eq_integral_mul_comp_inv_mul (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f g = ∫ y, φ y * f (g⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  calc rightConv K φ f g = ∫ x, φ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := rfl
    _ = ∫ x, (fun y => φ y * f (g⁻¹ * y)) (g * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        simp only [inv_mul_cancel_left]
    _ = ∫ y, φ y * f (g⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        integral_mul_left_eq_self (fun y => φ y * f (g⁻¹ * y)) g
theorem unipotentGL2_algebraMap_eq_globalPoints (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPoints, unipotentGL2_coe, Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply]

theorem apply_unipotentGL2_algebraMap_mul_of_forall_apply_globalPoints_mul (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hφ : ∀ (γ : GL (Fin 2) K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)), φ (globalPoints (𝓞 K) K γ * y) = φ y) :
    ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)), φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y := by
  intro β y
  rw [unipotentGL2_algebraMap_eq_globalPoints, hφ]

theorem locallyIntegrable_adelicGLHaar_of_continuous (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hφ : Continuous φ) :
    LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  exact hφ.locallyIntegrable

theorem mem_integralWindowedSiegelSet_zero_of_mem_centreCutSiegelSet (c u d₁ d₂ : ℝ) {s : AdelicGL2 (𝓞 K) K} (hs : s ∈ centreCutSiegelSet K c u d₁ d₂) :
    s ∈ integralWindowedSiegelSet K 0 u :=
  ⟨hs.1, (archHeight_pos K _).le, hs.2.2.1⟩

theorem lintegral_nnnorm_sq_rpow_half_eq_eLpNorm_restrict (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (W : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) :
    (∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ^ (1 / 2 : ℝ) =
      eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict W) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun y => ?_
  rw [enorm_eq_nnnorm]
  exact (ENNReal.rpow_ofNat _ 2).symm

theorem setIntegral_norm_le_sqrt_mul_rpow_half_toReal (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hφ : Continuous φ)
    (R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) (V : ℝ) (hV : 0 ≤ V)
    (hR : (adelicGLHaar (Fin 2) (𝓞 K) K) R ≤ ENNReal.ofReal V)
    (B : ℝ≥0∞) (hB : ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤ B) (hBfin : B ≠ ⊤) :
    ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤ Real.sqrt V * (B ^ (1 / 2 : ℝ)).toReal := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  have hRfin : μ R < ⊤ := lt_of_le_of_lt hR ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (μ.restrict R) := isFiniteMeasure_restrict.mpr hRfin.ne

  have hL2 : eLpNorm φ 2 (μ.restrict R) < ⊤ := by
    rw [← lintegral_nnnorm_sq_rpow_half_eq_eLpNorm_restrict K φ R]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_top_of_le_ne_top hBfin hB)
  have hmem : MemLp φ 2 (μ.restrict R) := ⟨hφ.aestronglyMeasurable, hL2⟩
  have hG2 : MemLp (fun y => ‖φ y‖) (ENNReal.ofReal 2) (μ.restrict R) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact hmem.norm
  have h12 : MemLp (fun _ : GL (Fin 2) (AdeleRing (𝓞 K) K) => (1 : ℝ)) (ENNReal.ofReal 2) (μ.restrict R) :=
    memLp_const 1

  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict R) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun _ => zero_le_one) (Filter.Eventually.of_forall fun _ => norm_nonneg _) h12 hG2
  simp only [one_mul, Real.one_rpow] at hcs

  have hfac1 : (∫ _ in R, (1 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ Real.sqrt V := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.sqrt_eq_rpow]
    refine Real.rpow_le_rpow ENNReal.toReal_nonneg ?_ (by norm_num)
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal hV hR
  have hfac2 : (∫ y in R, ‖φ y‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ (B ^ (1 / 2 : ℝ)).toReal := by
    have e : (∫ y in R, ‖φ y‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = (eLpNorm φ 2 (μ.restrict R)).toReal := by
      rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofReal
        (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _),
        ENNReal.toReal_ofNat, ← one_div]
    rw [e, ← lintegral_nnnorm_sq_rpow_half_eq_eLpNorm_restrict K φ R]
    exact ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBfin)
      (ENNReal.rpow_le_rpow hB (by norm_num))
  calc ∫ y in R, ‖φ y‖ ∂μ
      ≤ (∫ _ in R, (1 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ y in R, ‖φ y‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hcs
    _ ≤ Real.sqrt V * (B ^ (1 / 2 : ℝ)).toReal :=
        mul_le_mul hfac1 hfac2 (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _)
          (Real.sqrt_nonneg V)
end CuspDecayAux

open CuspDecayAux

theorem CuspDecayAux.archHeight_gt_of_localHeight_gt (K : Type) [Field K] [NumberField K]
    {c' : ℝ} (hc' : 0 < c') (Hc : ℝ) (s : AdelicGL2 (𝓞 K) K)
    (hfloor : ∀ w : InfinitePlace K, c' ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)))
    (w₀ : InfinitePlace K)
    (hw₀ : max 1 (|Hc| / (min c' 1) ^ (∑ w : InfinitePlace K, w.mult) + 1)
      < localHeight (archComponent K w₀ (glArch (𝓞 K) K s))) :
    Hc < archHeight K (glArch (𝓞 K) K s) := by
  classical
  set L : ℝ := min c' 1 with hL
  have hL0 : 0 < L := lt_min hc' one_pos
  have hL1 : L ≤ 1 := min_le_right _ _
  set n : ℕ := ∑ w : InfinitePlace K, w.mult with hn
  have hLn0 : 0 < L ^ n := pow_pos hL0 n
  have hLn1 : L ^ n ≤ 1 := pow_le_one₀ hL0.le hL1
  set lh : InfinitePlace K → ℝ := fun w => localHeight (archComponent K w (glArch (𝓞 K) K s)) with hlh
  have hlhL : ∀ w, L ≤ lh w := fun w => (min_le_left _ _).trans (hfloor w)
  have hlh0 : ∀ w, 0 < lh w := fun w => hL0.trans_le (hlhL w)
  have h1 : 1 ≤ lh w₀ := le_trans (le_max_left _ _) hw₀.le

  have hsplit : archHeight K (glArch (𝓞 K) K s) = lh w₀ ^ w₀.mult * ∏ w ∈ Finset.univ.erase w₀, lh w ^ w.mult := by
    unfold archHeight
    rw [← Finset.mul_prod_erase Finset.univ (fun w => lh w ^ w.mult) (Finset.mem_univ w₀)]
  have hrest : L ^ n ≤ ∏ w ∈ Finset.univ.erase w₀, lh w ^ w.mult := by
    calc L ^ n ≤ L ^ (∑ w ∈ Finset.univ.erase w₀, w.mult) :=
          pow_le_pow_of_le_one hL0.le hL1 (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
      _ = ∏ w ∈ Finset.univ.erase w₀, L ^ w.mult := (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ w ∈ Finset.univ.erase w₀, lh w ^ w.mult :=
          Finset.prod_le_prod (fun w _ => pow_nonneg hL0.le _) fun w _ => pow_le_pow_left₀ hL0.le (hlhL w) _
  have hm₀ : lh w₀ ≤ lh w₀ ^ w₀.mult := le_self_pow₀ h1 (InfinitePlace.mult_pos).ne'
  have hmain : lh w₀ * L ^ n ≤ archHeight K (glArch (𝓞 K) K s) := by
    rw [hsplit]; exact mul_le_mul hm₀ hrest hLn0.le (le_trans zero_le_one (h1.trans hm₀))
  have hw₀' : |Hc| / L ^ n + 1 < lh w₀ := lt_of_le_of_lt (le_max_right _ _) hw₀
  have : Hc < lh w₀ * L ^ n := by
    have h2 : (|Hc| / L ^ n + 1) * L ^ n < lh w₀ * L ^ n := mul_lt_mul_of_pos_right hw₀' hLn0
    have h3 : (|Hc| / L ^ n + 1) * L ^ n = |Hc| + L ^ n := by field_simp
    rw [h3] at h2
    linarith [le_abs_self Hc]
  exact this.trans_le hmain

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : IsFactorizableTestFn K f)
    (c' u' d₁' d₂' : ℝ) (t : AdelicGL2 (𝓞 K) K) (hc' : 0 < c') (hd₁' : 0 < d₁') (k : ℕ) :
    ∃ Ccap C : ℝ, ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      (∃ w : InfinitePlace K, Ccap < localHeight (archComponent K w (glArch (𝓞 K) K s))) →
        ‖rightConv K φ f (s * t)‖ ≤ C * (archHeight K (glArch (𝓞 K) K s))⁻¹ ^ k := by
  classical

  set fx : AdelicGL2 (𝓞 K) K → ℂ := fun y => f (t⁻¹ * y) with hfx_def
  have hfx : IsFactorizableTestFn K fx := isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn K f hf t
  obtain ⟨hcont_fx, hcpt_fx⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K fx hfx
  have hC : IsCompact (tsupport fx) := hcpt_fx

  obtain ⟨T₁, A, M, hmass⟩ :=
    exists_forall_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
      K c u d₁ d₂ T hd hcov χ hC c' u' d₁' d₂' hc' hd₁'
  obtain ⟨Cd, hdec⟩ := norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn K fx hfx 0 u' (A + k)
  obtain ⟨V, hV0, hvol⟩ := exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact K c' u' d₁' d₂' hc' hC

  have hLsMem := by
    letI := (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).mS
    exact (lsXiMemberAt_iff (𝓞 K) K _ _ χ _ φ).mp hφ.1
  have hLs : IsLsXiFunction (𝓞 K) K ⊤ χ φ := hLsMem.1
  have hWfin : ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖φ y‖₊ : ℝ≥0∞) ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≠ ⊤ := by
    have h2 : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) :=
      hLsMem.2
    have h3 := h2.eLpNorm_lt_top
    rw [← lintegral_nnnorm_sq_rpow_half_eq_eLpNorm_restrict] at h3
    intro h
    rw [h, ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at h3
    exact lt_irrefl _ h3
  have hcusp : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ := hφ.2
  set E := (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))).toReal with hE
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg

  set Hc : ℝ := max T₁ 1 with hHc
  refine ⟨max 1 (|Hc| / (min c' 1) ^ (∑ w : InfinitePlace K, w.mult) + 1), |Cd| * Real.sqrt V * Real.sqrt |M| * E, ?_⟩
  intro s hs hguard
  obtain ⟨w₀, hw₀⟩ := hguard
  have hfloor : ∀ w : InfinitePlace K, c' ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) :=
    (mem_centreCutSiegelSet_iff.mp hs).2.1
  have hH : Hc < archHeight K (glArch (𝓞 K) K s) :=
    CuspDecayAux.archHeight_gt_of_localHeight_gt K hc' Hc s hfloor w₀ hw₀
  set Hs := archHeight K (glArch (𝓞 K) K s) with hHs
  have hT₁ : T₁ < Hs := lt_of_le_of_lt (le_max_left _ _) hH
  have h1 : 1 ≤ Hs := ((le_max_right _ _).trans hH.le)
  have hHpos : 0 < Hs := one_pos.trans_le h1

  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, rightConv_eq_integral_mul_comp_inv_mul]

  have hε : ∀ y : GL (Fin 2) (AdeleRing (𝓞 K) K),
      ‖(∑' β : K, fx (s⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
          - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, fx (s⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)‖
        ≤ |Cd| * Hs⁻¹ ^ (A + k) := fun y =>
    (hdec s (mem_integralWindowedSiegelSet_zero_of_mem_centreCutSiegelSet K c' u' d₁' d₂' hs) h1 y).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hunf := norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn K φ fx s
    (apply_unipotentGL2_algebraMap_mul_of_forall_apply_globalPoints_mul K φ hLs.left_invariant)
    (locallyIntegrable_adelicGLHaar_of_continuous K φ hcont) hcusp hcont_fx hcpt_fx (|Cd| * Hs⁻¹ ^ (A + k)) hε
  refine hunf.trans ?_

  have hm := hmass φ hLs hcont s hs hT₁
  have hcs := setIntegral_norm_le_sqrt_mul_rpow_half_toReal K φ hcont _ V hV0 (hvol s hs) _ hm
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWfin)
  refine (mul_le_mul_of_nonneg_left hcs (by positivity)).trans ?_
  have hsplit : ((ENNReal.ofReal (M * Hs ^ A) *
      ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ^ (1 / 2 : ℝ)).toReal =
        Real.sqrt (max (M * Hs ^ A) 0) * E := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2), ENNReal.toReal_mul, lintegral_nnnorm_sq_rpow_half_eq_eLpNorm_restrict, ← hE,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal', Real.sqrt_eq_rpow]
  rw [hsplit]
  have hq : Real.sqrt (max (M * Hs ^ A) 0) ≤ Real.sqrt |M| * Real.sqrt (Hs ^ A) := by
    rw [← Real.sqrt_mul (abs_nonneg M)]
    apply Real.sqrt_le_sqrt
    refine max_le ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
  have hP1 : 1 ≤ Hs ^ A := one_le_pow₀ h1
  have hkey : Hs⁻¹ ^ A * Real.sqrt (Hs ^ A) ≤ 1 := by
    rw [inv_pow, inv_mul_eq_div, div_le_one (by positivity)]
    calc Real.sqrt (Hs ^ A) ≤ Real.sqrt (Hs ^ A) * Real.sqrt (Hs ^ A) :=
          le_mul_of_one_le_right (Real.sqrt_nonneg _) (Real.one_le_sqrt.mpr hP1)
      _ = Hs ^ A := Real.mul_self_sqrt (by positivity)
  have hpow : Hs⁻¹ ^ (A + k) = Hs⁻¹ ^ A * Hs⁻¹ ^ k := pow_add _ _ _
  calc |Cd| * Hs⁻¹ ^ (A + k) * (Real.sqrt V * (Real.sqrt (max (M * Hs ^ A) 0) * E))
      ≤ |Cd| * Hs⁻¹ ^ (A + k) * (Real.sqrt V * ((Real.sqrt |M| * Real.sqrt (Hs ^ A)) * E)) := by gcongr
    _ = |Cd| * Real.sqrt V * Real.sqrt |M| * E * (Hs⁻¹ ^ A * Real.sqrt (Hs ^ A)) * Hs⁻¹ ^ k := by rw [hpow]; ring
    _ ≤ |Cd| * Real.sqrt V * Real.sqrt |M| * E * 1 * Hs⁻¹ ^ k := by gcongr
    _ = |Cd| * Real.sqrt V * Real.sqrt |M| * E * Hs⁻¹ ^ k := by ring

end S_AutomorphicForm_exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_rightConv_mul_le_mul_inv_archHeight_pow_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre (solution)
