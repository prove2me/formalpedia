-- Prove2me | solution 1 for AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8007119b-1215-525c-80dc-67e467593fce

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentAverage_diagOne
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_AutomorphicForm_continuous_unipotentAverage_rightConv
import Theorems.Thm_AutomorphicForm_unipotentAverage_globalPoints_mul
import Theorems.Thm_AutomorphicForm_isKfSmooth_unipotentAverage
import Theorems.Thm_AutomorphicForm_isCuspidalFn_unipotentAverage
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isCuspidalFn_rightConv
import Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker
open scoped Classical

noncomputable section

namespace Ws1
namespace K4W

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem globalPoints_unipotentGL2 (F : Type) [Field F] [NumberField F] (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  simp only [globalPoints, Matrix.GeneralLinearGroup.map, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, unipotentGL2_coe]

theorem globalPoints_diagOne (F : Type) [Field F] [NumberField F] (u : Fˣ) :
    globalPoints (𝓞 F) F (diagOne u) =
      diagOne (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) := by
  apply Units.ext
  ext i j
  simp only [globalPoints, Matrix.GeneralLinearGroup.map, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, diagOne_coe_apply, Matrix.diagonal]

theorem principalIdeles_equiv (F : Type) [Field F] [NumberField F] :
    ∃ e : {α : F // α ≠ 0} ≃ ↥(M4aHerbrand.principalIdeles (𝓞 F) F),
      ∀ a : {α : F // α ≠ 0}, ((e a : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) =
        Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) (Units.mk0 a.1 a.2) := by
  classical
  let fwd : {α : F // α ≠ 0} → ↥(M4aHerbrand.principalIdeles (𝓞 F) F) := fun a =>
    ⟨Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) (Units.mk0 a.1 a.2),
      ⟨Units.mk0 a.1 a.2, rfl⟩⟩
  have hinj : Function.Injective fwd := by
    intro a b hab
    have h1 : ((fwd a : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) = fwd b :=
      congrArg Subtype.val hab
    have h2 := congrArg (fun x : (AdeleRing (𝓞 F) F)ˣ => (x : AdeleRing (𝓞 F) F)) h1
    simp only [fwd, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0] at h2
    exact Subtype.ext (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F h2)
  have hsurj : Function.Surjective fwd := by
    rintro ⟨_, u, rfl⟩
    refine ⟨⟨(u : F), u.ne_zero⟩, Subtype.ext ?_⟩
    simp only [fwd, Units.mk0_val]
  exact ⟨Equiv.ofBijective fwd ⟨hinj, hsurj⟩, fun a => rfl⟩

end Ws1.K4W

end

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
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (a : (AdeleRing (𝓞 F) F)ˣ) :
    HasSum (fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F) =>
        whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 (diagOne ((γ : (AdeleRing (𝓞 F) F)ˣ) * a)))
      (Φ (diagOne a)) := by
  classical

  have hleftφ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g := by
    letI : MeasureTheory.MeasureSpace (AdelicGL2 (𝓞 F) F) := @MeasureTheory.MeasureSpace.mk _
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).mS
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).μ
    have hmem : LsXiMember (𝓞 F) F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z ξ
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).D φ := hφ.1
    exact hmem.left_invariant
  have hG1 : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ f (globalPoints (𝓞 F) F γ * g) = rightConv F φ f g := by
    intro γ g
    unfold rightConv
    congr 1
    funext x
    rw [mul_assoc, hleftφ]
  have hGc : Continuous (rightConv F φ f) :=
    (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).1
  have hGMG := AutomorphicForm.exists_norm_rightConv_le_mul_max_ideleNorm_det_pow F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf
  have hG3 : IsKfSmooth F (rightConv F φ f) := AutomorphicForm.isKfSmooth_rightConv F φ f hf

  have hΦc : Continuous Φ :=
    AutomorphicForm.continuous_unipotentAverage_rightConv F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf B hB Φ hΦ
  have hT1 : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      Φ (globalPoints (𝓞 F) F γ * g) = Φ g :=
    AutomorphicForm.unipotentAverage_globalPoints_mul F (rightConv F φ f) hG1 B Φ hΦ
  have hT3 : IsKfSmooth F Φ := AutomorphicForm.isKfSmooth_unipotentAverage F (rightConv F φ f) hG3 B hB Φ hΦ
  have hGleftN : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      rightConv F φ f (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = rightConv F φ f g := by
    intro β g
    rw [← Ws1.K4W.globalPoints_unipotentGL2 F β]
    exact hG1 _ g
  have hGarch := (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).2

  obtain ⟨-, hsummG⟩ :=
    AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
      F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
      ψ hψ (rightConv F φ f) hGleftN hG3 hGarch

  have hGcusp := AutomorphicForm.isCuspidalFn_rightConv F
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    φ hcont hφ.2 f hf
  have hT2 := AutomorphicForm.isCuspidalFn_unipotentAverage F
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (rightConv F φ f) hGc hGMG hGcusp B hB Φ hΦ
  have hcusp : ∀ g : AdelicGL2 (𝓞 F) F, whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 0 g = 0 := by
    intro g
    rw [AutomorphicForm.whittakerCoefficient_zero_eq_constantTerm]
    exact hT2 g

  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  have hW1 := fun α : F => AutomorphicForm.whittakerCoefficient_unipotentAverage_diagOne F
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    ψ hψ (rightConv F φ f) hGc hGMG hGleftN B hB Φ hΦ α a
  have hmult : ∀ α : F,
      ‖∫ x, B x * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * ((a : AdeleRing (𝓞 F) F) * x)) ∂(adelicAddHaar (𝓞 F) F)‖ ≤
        ∫ x, ‖B x‖ ∂(adelicAddHaar (𝓞 F) F) := by
    intro α
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖B x * ψ _‖ = ‖B x‖
    rw [norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ, mul_one]

  have hsummΦ : Summable fun α : F => whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ α (diagOne a) := by
    refine Summable.of_norm_bounded ((hsummG (diagOne a)).norm.mul_left
      (∫ x, ‖B x‖ ∂(adelicAddHaar (𝓞 F) F))) fun α => ?_
    rw [hW1 α, norm_mul]
    exact mul_le_mul_of_nonneg_right (hmult α) (norm_nonneg _)
  have hslice : Continuous (fun x : AdeleRing (𝓞 F) F => Φ (unipotentGL2 x * diagOne a)) :=
    hΦc.comp (AutomorphicForm.continuous_unipotentGL2.mul continuous_const)
  have hF : HasSum (fun α : F => whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ α (diagOne a)) (Φ (diagOne a)) :=
    AutomorphicForm.hasSum_whittakerCoefficient F _ _ _ ψ hψ Φ (diagOne a) hslice hsummΦ

  have hsupp : Function.support (fun α : F => whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ α (diagOne a)) ⊆ {α : F | α ≠ 0} := by
    intro α hα
    simp only [Function.mem_support, ne_eq] at hα
    intro h0
    exact hα (h0 ▸ hcusp (diagOne a))
  have hF' := (hasSum_subtype_iff_of_support_subset hsupp).mpr hF
  obtain ⟨e, he⟩ := Ws1.K4W.principalIdeles_equiv F
  suffices h : HasSum (fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F) =>
      whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 (diagOne (γ : (AdeleRing (𝓞 F) F)ˣ) * diagOne a)) (Φ (diagOne a)) by
    simpa only [← map_mul] using h
  refine (e.hasSum_iff).mp ?_
  have key : ∀ a' : {α : F // α ≠ 0},
      whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 (diagOne (((e a' : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ)) * diagOne a)
        = whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ (a' : F) (diagOne a) := by
    intro a'
    rw [he a', ← Ws1.K4W.globalPoints_diagOne F,
      AutomorphicForm.whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul F _ _ _ ψ hψ Φ
        hT1 (a' : F) a'.2 (diagOne a)]
  have hfun : ((fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F) =>
        whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 (diagOne (γ : (AdeleRing (𝓞 F) F)ˣ) * diagOne a)) ∘ ⇑e)
      = (fun α : F => whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ α (diagOne a)) ∘ Subtype.val := by
    funext a'
    exact key a'
  rw [hfun]
  exact hF'

end S_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage
end P2MW
export P2MW.S_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage (solution)
