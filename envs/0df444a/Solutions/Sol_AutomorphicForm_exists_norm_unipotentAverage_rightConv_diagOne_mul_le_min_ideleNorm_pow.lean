-- Prove2me | solution 1 for AutomorphicForm.exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6e19dc07-96ca-5548-ad26-c6f0bce4969a

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdelicFourier_integrable_of_mem_schwartzBruhat
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm
import Theorems.Thm_NumberField_AdelicFourier_exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight

noncomputable section

namespace C5aTop

variable (F : Type) [Field F] [NumberField F]

def weylF : GL (Fin 2) F :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem diagOne_eq_flip (a : (AdeleRing (𝓞 F) F)ˣ) :
    (diagOne a : AdelicGL2 (𝓞 F) F)
      = centralScalar (𝓞 F) F a * (globalPoints (𝓞 F) F (weylF F) * (diagOne a⁻¹ * globalPoints (𝓞 F) F (weylF F))) := by
  have hinv : (((diagOne a)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal ![((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1] := rfl
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Units.val_mul, globalPoints, centralScalar, weylF, diagOne_coe_apply, hinv,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

end C5aTop

namespace C5aTop

variable {F : Type} [Field F] [NumberField F]

theorem rightConv_globalPoints_mul {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (globalPoints (𝓞 F) F γ * g) = rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  congr 1
  funext x
  exact hφ γ x

theorem rightConv_centralScalar_mul {φ : AdelicGL2 (𝓞 F) F → ℂ} {z : (AdeleRing (𝓞 F) F)ˣ} {cz : ℂ}
    (hφ : ∀ g : AdelicGL2 (𝓞 F) F, φ (centralScalar (𝓞 F) F z * g) = cz * φ g)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (centralScalar (𝓞 F) F z * g) = cz * rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  simp only [rightConv, hφ, mul_assoc]
  exact integral_const_mul _ _

theorem det_diagOne_mul (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (diagOne a * g) = a * Matrix.GeneralLinearGroup.det g := by
  have h1 : Matrix.GeneralLinearGroup.det (diagOne a : AdelicGL2 (𝓞 F) F) = a := by
    refine Units.ext ?_
    simp [diagOne, Matrix.GeneralLinearGroup.val_det_apply]
  rw [map_mul, h1]

theorem det_mul_unipotentGL2 (g : AdelicGL2 (𝓞 F) F) (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (g * unipotentGL2 x) = Matrix.GeneralLinearGroup.det g := by
  have h2 : Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 := by
    refine Units.ext ?_
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]
  rw [map_mul, h2, mul_one]

theorem ideleNorm_inv (z : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F z⁻¹ = (ideleNorm F z)⁻¹ := by
  have h := ideleNorm_mul (F := F) z z⁻¹
  have h1 : ideleNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by simp [ideleNorm]
  rw [mul_inv_cancel, h1] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

end C5aTop

open C5aTop in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * rightConv F φ f (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (k : ℕ) :
    ∃ Cst : ℝ, ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), g ∈ C →
      ‖Φ (diagOne a * g)‖ ≤ Cst * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F

  by_cases hφ0 : ¬ ∃ g, φ g ≠ 0
  · push Not at hφ0
    refine ⟨0, fun a g _ => ?_⟩
    have hz : φ = fun _ => (0 : ℂ) := funext hφ0
    rw [hΦ, hz, rightConv_zero_left]
    simp
  push Not at hφ0
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · exact ⟨0, fun a g hg => by simp [hCe] at hg⟩

  have hls : IsLsXiFunction (𝓞 F) F _ ξ φ := by
    letI := (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).mS
    exact ((lsXiMemberAt_iff _ _ _ _ ξ _ φ).mp hφ.1).1
  obtain ⟨hcls, hξc⟩ :=
    AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous F ξ φ hls hcont hφ0
  let μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
    { toFun := fun z => ξ ⟨z, Subgroup.mem_top z⟩
      map_one' := by
        show ξ 1 = 1
        exact map_one ξ
      map_mul' := fun z z' => by
        show ξ (⟨z, Subgroup.mem_top z⟩ * ⟨z', Subgroup.mem_top z'⟩) = _
        exact map_mul ξ _ _ }
  obtain ⟨t, ht⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F μ (fun u => hcls u) hξc

  have hΦleft : ∀ (γ : GL (Fin 2) F) (h : AdelicGL2 (𝓞 F) F), Φ (globalPoints (𝓞 F) F γ * h) = Φ h := by
    intro γ h
    rw [hΦ, hΦ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show B x * rightConv F φ f (globalPoints (𝓞 F) F γ * h * unipotentGL2 x) = B x * rightConv F φ f (h * unipotentGL2 x)
    rw [mul_assoc, rightConv_globalPoints_mul hls.left_invariant]
  have hΦcen : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F),
      Φ (centralScalar (𝓞 F) F z * h) = ((μ z : ℂˣ) : ℂ) * Φ h := by
    intro z h
    rw [hΦ, hΦ, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show B x * rightConv F φ f (centralScalar (𝓞 F) F z * h * unipotentGL2 x)
      = ((μ z : ℂˣ) : ℂ) * (B x * rightConv F φ f (h * unipotentGL2 x))
    rw [mul_assoc, rightConv_centralScalar_mul (fun g' => hls.central_transform ⟨z, Subgroup.mem_top z⟩ g'), ← mul_assoc,
      ← mul_assoc, mul_comm (B x)]
    rfl

  have hdetc := (NumberField.TateGlobal.continuous_ideleNorm_det F).continuousOn (s := C)
  obtain ⟨gmin, hgmin, hmin⟩ := hC.exists_isMinOn hCne hdetc
  obtain ⟨gmax, hgmax, hmax⟩ := hC.exists_isMaxOn hCne hdetc
  set α : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det gmin) with hαdef
  set β : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det gmax) with hβdef
  have hα : 0 < α := ideleNorm_pos _

  set wC : Set (AdelicGL2 (𝓞 F) F) := (fun g => globalPoints (𝓞 F) F (weylF F) * g) '' C with hwCdef
  have hwC : IsCompact wC := hC.image (continuous_const.mul continuous_id)

  set τ : ℕ := ⌈|t|⌉₊ with hτdef
  obtain ⟨A₀, Cst₄, M, hD4⟩ :=
    AutomorphicForm.exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm F c u d₁ d₂ T hd hcov ξ φ hφ
      hcont f hf C hC k
  obtain ⟨A₀', Cst₄', M', hD4'⟩ :=
    AutomorphicForm.exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm F c u d₁ d₂ T hd hcov ξ φ hφ
      hcont f hf wC hwC (k + τ)
  obtain ⟨I, hD5⟩ :=
    NumberField.AdelicFourier.exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat
      F (adelicAddHaar (𝓞 F) F) hB C hC M
  obtain ⟨I', hD5'⟩ :=
    NumberField.AdelicFourier.exists_forall_integral_norm_mul_inv_adelicHeight_mul_unipotentGL2_pow_le_of_mem_schwartzBruhat
      F (adelicAddHaar (𝓞 F) F) hB wC hwC M'
  set A₁ : ℝ := max (max A₀ A₀') 1 with hA₁def
  have hA₁1 : 1 ≤ A₁ := le_max_right _ _
  have hA₁0 : 0 < A₁ := lt_of_lt_of_le one_pos hA₁1
  obtain ⟨M₁, hD1⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf
      (α / A₁) (β * A₁) (div_pos hα hA₁0)
  have hBint : Integrable (fun x => ‖B x‖) (adelicAddHaar (𝓞 F) F) :=
    (NumberField.AdelicFourier.integrable_of_mem_schwartzBruhat F (adelicAddHaar (𝓞 F) F) hB).norm
  set IB : ℝ := ∫ x, ‖B x‖ ∂(adelicAddHaar (𝓞 F) F) with hIBdef

  have hΦle : ∀ (h : AdelicGL2 (𝓞 F) F) (G : AdeleRing (𝓞 F) F → ℝ), Integrable G (adelicAddHaar (𝓞 F) F) →
      (∀ x, ‖B x‖ * ‖rightConv F φ f (h * unipotentGL2 x)‖ ≤ G x) → ‖Φ h‖ ≤ ∫ x, G x ∂(adelicAddHaar (𝓞 F) F) := by
    intro h G hG hle
    rw [hΦ]
    refine norm_integral_le_of_norm_le hG (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact hle x

  set K₁ : ℝ := max Cst₄ 0 * max I 0 with hK₁def
  set K₂ : ℝ := max Cst₄' 0 * max I' 0 with hK₂def
  set K₃ : ℝ := max M₁ 0 * IB * A₁ ^ k with hK₃def
  refine ⟨K₁ + K₂ + K₃, fun a g hg => ?_⟩
  have ha0 : 0 < ideleNorm F a := ideleNorm_pos a
  have hmin0 : 0 ≤ min (ideleNorm F a) (ideleNorm F a)⁻¹ := le_min ha0.le (inv_nonneg.mpr ha0.le)
  have hIB0 : 0 ≤ IB := integral_nonneg fun _ => norm_nonneg _
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  have hK₃0 : 0 ≤ K₃ := by positivity

  rcases le_or_gt A₁ (ideleNorm F a) with hhigh | hnothigh
  ·
    have h1a : 1 ≤ ideleNorm F a := hA₁1.trans hhigh
    have hmin : min (ideleNorm F a) (ideleNorm F a)⁻¹ = (ideleNorm F a)⁻¹ :=
      min_eq_right ((inv_le_one_of_one_le₀ h1a).trans h1a)
    have hA : A₀ ≤ ideleNorm F a := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hhigh
    obtain ⟨hint, hI⟩ := hD5 g hg
    have h1 := hΦle (diagOne a * g)
      (fun x => max Cst₄ 0 * (ideleNorm F a)⁻¹ ^ k * (‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M))
      (hint.const_mul _) (fun x => ?_)
    · refine h1.trans ?_
      rw [integral_const_mul, hmin]
      calc max Cst₄ 0 * (ideleNorm F a)⁻¹ ^ k * ∫ x, ‖B x‖ * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M ∂adelicAddHaar (𝓞 F) F
          ≤ max Cst₄ 0 * (ideleNorm F a)⁻¹ ^ k * max I 0 :=
            mul_le_mul_of_nonneg_left (hI.trans (le_max_left _ _)) (by positivity)
        _ = K₁ * (ideleNorm F a)⁻¹ ^ k := by rw [hK₁def]; ring
        _ ≤ (K₁ + K₂ + K₃) * (ideleNorm F a)⁻¹ ^ k := by gcongr; linarith
    · have h4 := hD4 a g x hg hA
      have h5 : ‖rightConv F φ f (diagOne a * g * unipotentGL2 x)‖
          ≤ max Cst₄ 0 * (ideleNorm F a)⁻¹ ^ k * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M :=
        h4.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pow_nonneg (inv_nonneg.mpr ha0.le) _)) (pow_nonneg (inv_nonneg.mpr (adelicHeight_pos _).le) _))
      calc ‖B x‖ * ‖rightConv F φ f (diagOne a * g * unipotentGL2 x)‖
          ≤ ‖B x‖ * (max Cst₄ 0 * (ideleNorm F a)⁻¹ ^ k * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M) :=
            mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
        _ = _ := by ring
  rcases le_or_gt (ideleNorm F a) A₁⁻¹ with hlow | hnotlow
  ·
    have hainv : A₁ ≤ ideleNorm F a⁻¹ := by
      rw [ideleNorm_inv]; exact (le_inv_comm₀ hA₁0 ha0).mpr hlow
    have ha1 : ideleNorm F a ≤ 1 := hlow.trans (inv_le_one_of_one_le₀ hA₁1)
    have hmin : min (ideleNorm F a) (ideleNorm F a)⁻¹ = ideleNorm F a :=
      min_eq_left (le_trans ha1 (one_le_inv₀ ha0 |>.mpr ha1))
    have hflip : Φ (diagOne a * g) = ((μ a : ℂˣ) : ℂ) * Φ (diagOne a⁻¹ * (globalPoints (𝓞 F) F (weylF F) * g)) := by
      rw [diagOne_eq_flip F a, mul_assoc, hΦcen, mul_assoc, hΦleft, mul_assoc]
    have hwg : globalPoints (𝓞 F) F (weylF F) * g ∈ wC := ⟨g, hg, rfl⟩
    obtain ⟨hint, hI⟩ := hD5' _ hwg
    have hA : A₀' ≤ ideleNorm F a⁻¹ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hainv
    have h1 := hΦle (diagOne a⁻¹ * (globalPoints (𝓞 F) F (weylF F) * g))
      (fun x => max Cst₄' 0 * (ideleNorm F a⁻¹)⁻¹ ^ (k + τ)
        * (‖B x‖ * (adelicHeight F (globalPoints (𝓞 F) F (weylF F) * g * unipotentGL2 x))⁻¹ ^ M'))
      (hint.const_mul _) (fun x => ?_)
    · rw [hflip, norm_mul, ht a, hmin]
      rw [integral_const_mul, ideleNorm_inv, inv_inv] at h1

      have h2 : ‖Φ (diagOne a⁻¹ * (globalPoints (𝓞 F) F (weylF F) * g))‖ ≤ K₂ * ideleNorm F a ^ (k + τ) := by
        refine h1.trans ?_
        calc max Cst₄' 0 * ideleNorm F a ^ (k + τ) *
              ∫ x, ‖B x‖ * (adelicHeight F (globalPoints (𝓞 F) F (weylF F) * g * unipotentGL2 x))⁻¹ ^ M' ∂adelicAddHaar (𝓞 F) F
            ≤ max Cst₄' 0 * ideleNorm F a ^ (k + τ) * max I' 0 :=
              mul_le_mul_of_nonneg_left (hI.trans (le_max_left _ _)) (by positivity)
          _ = K₂ * ideleNorm F a ^ (k + τ) := by rw [hK₂def]; ring
      have h3 : ideleNorm F a ^ t * ideleNorm F a ^ (k + τ) ≤ ideleNorm F a ^ k := by
        rw [← Real.rpow_natCast _ (k + τ), ← Real.rpow_add ha0, ← Real.rpow_natCast _ k]
        refine Real.rpow_le_rpow_of_exponent_ge ha0 ha1 ?_
        have : |t| ≤ (τ : ℝ) := Nat.le_ceil _
        push_cast
        linarith [neg_abs_le t]
      calc ideleNorm F a ^ t * ‖Φ (diagOne a⁻¹ * (globalPoints (𝓞 F) F (weylF F) * g))‖
          ≤ ideleNorm F a ^ t * (K₂ * ideleNorm F a ^ (k + τ)) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ha0.le _)
        _ = K₂ * (ideleNorm F a ^ t * ideleNorm F a ^ (k + τ)) := by ring
        _ ≤ K₂ * ideleNorm F a ^ k := mul_le_mul_of_nonneg_left h3 hK₂0
        _ ≤ (K₁ + K₂ + K₃) * ideleNorm F a ^ k := by gcongr; linarith
    · have h4 := hD4' a⁻¹ _ x hwg hA
      have h5 : ‖rightConv F φ f (diagOne a⁻¹ * (globalPoints (𝓞 F) F (weylF F) * g) * unipotentGL2 x)‖
          ≤ max Cst₄' 0 * (ideleNorm F a⁻¹)⁻¹ ^ (k + τ)
              * (adelicHeight F (globalPoints (𝓞 F) F (weylF F) * g * unipotentGL2 x))⁻¹ ^ M' :=
        h4.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (pow_nonneg (inv_nonneg.mpr (ideleNorm_pos _).le) _)) (pow_nonneg (inv_nonneg.mpr (adelicHeight_pos _).le) _))
      calc ‖B x‖ * ‖rightConv F φ f (diagOne a⁻¹ * (globalPoints (𝓞 F) F (weylF F) * g) * unipotentGL2 x)‖
          ≤ ‖B x‖ * (max Cst₄' 0 * (ideleNorm F a⁻¹)⁻¹ ^ (k + τ)
              * (adelicHeight F (globalPoints (𝓞 F) F (weylF F) * g * unipotentGL2 x))⁻¹ ^ M') :=
            mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
        _ = _ := by ring
  ·
    have hslab : ideleNorm F (Matrix.GeneralLinearGroup.det (diagOne a * g)) ∈ Set.Icc (α / A₁) (β * A₁) := by
      rw [det_diagOne_mul, ideleNorm_mul]
      constructor
      · calc α / A₁ = A₁⁻¹ * α := by ring
          _ ≤ ideleNorm F a * ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
            mul_le_mul hnotlow.le (show α ≤ ideleNorm F (Matrix.GeneralLinearGroup.det g) from hmin hg) hα.le ha0.le
      · calc ideleNorm F a * ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ A₁ * β :=
            mul_le_mul hnothigh.le (show ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ β from hmax hg)
              (ideleNorm_pos _).le hA₁0.le
          _ = β * A₁ := mul_comm _ _
    have h1 := hΦle (diagOne a * g) (fun x => max M₁ 0 * ‖B x‖) (hBint.const_mul _) (fun x => ?_)
    · rw [integral_const_mul] at h1

      have hmink : A₁⁻¹ ^ k ≤ min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k :=
        pow_le_pow_left₀ (inv_nonneg.mpr hA₁0.le) (le_min hnotlow.le ((inv_le_inv₀ hA₁0 ha0).mpr hnothigh.le)) k
      calc ‖Φ (diagOne a * g)‖ ≤ max M₁ 0 * IB := h1
        _ = K₃ * A₁⁻¹ ^ k := by rw [hK₃def, inv_pow]; field_simp
        _ ≤ K₃ * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k := mul_le_mul_of_nonneg_left hmink hK₃0
        _ ≤ (K₁ + K₂ + K₃) * min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k := by gcongr; linarith
    · have := hD1 (diagOne a * g * unipotentGL2 x) (by rwa [det_mul_unipotentGL2])
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (this.trans (le_max_left _ _)) (norm_nonneg _)

end

end S_AutomorphicForm_exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_unipotentAverage_rightConv_diagOne_mul_le_min_ideleNorm_pow (solution)
