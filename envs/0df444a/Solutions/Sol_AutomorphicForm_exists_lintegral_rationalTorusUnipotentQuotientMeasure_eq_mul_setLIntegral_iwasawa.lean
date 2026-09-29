-- Prove2me | solution 1 for AutomorphicForm.exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/af0af616-e61b-5f40-a401-92b8a254addc

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdelicHaar_exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel"
open scoped ENNReal

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar unipotentGL2 AdelicGL2 globalPoints centralScalar adelicMaximalCompact maximalCompactHaar continuous_unipotentGL2 isClosed_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
p2m_open "AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

variable (K : Type) [Field K] [NumberField K]

private noncomputable abbrev rationalScalarPoint (ζ : Kˣ) : AdelicGL2 (𝓞 K) K :=
  globalPoints (𝓞 K) K
    (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom ζ)

private noncomputable abbrev rationalDiagOnePoint (a : Kˣ) : AdelicGL2 (𝓞 K) K :=
  globalPoints (𝓞 K) K (diagOne a)

private theorem rationalScalarPoint_coe_apply (ζ : Kˣ) (i j : Fin 2) :
    ((rationalScalarPoint K ζ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
      = algebraMap K (AdeleRing (𝓞 K) K) (Matrix.scalar (Fin 2) (ζ : K) i j) := rfl

private theorem rationalDiagOnePoint_coe_apply (a : Kˣ) (i j : Fin 2) :
    ((rationalDiagOnePoint K a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
      = algebraMap K (AdeleRing (𝓞 K) K) (Matrix.diagonal ![(a : K), 1] i j) := rfl

private theorem coe_toAdelicUnipotent (x : AdeleRing (𝓞 K) K) :
    ((toAdelicUnipotent K x : adelicUnipotent K) : AdelicGL2 (𝓞 K) K) = unipotentGL2 x :=
  MonoidHom.coe_rangeRestrict _ _

private theorem measurable_toAdelicUnipotent : Measurable (toAdelicUnipotent K) :=
  continuous_unipotentGL2.measurable.subtype_mk

private theorem rationalScalarPoint_mul_rationalDiagOnePoint_mul_unipotentGL2 (ζ a : Kˣ)
    (x : AdeleRing (𝓞 K) K) :
    rationalScalarPoint K ζ * rationalDiagOnePoint K a * unipotentGL2 x
      = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) a * x)
          * (rationalScalarPoint K ζ * rationalDiagOnePoint K a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalScalarPoint_coe_apply, rationalDiagOnePoint_coe_apply, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm, mul_left_comm, mul_assoc]

variable {K}

private theorem lintegral_rationalTorusUnipotentHaar_mul (φ : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hφ : Measurable φ)
    (g₀ : AdelicGL2 (𝓞 K) K) :
    ∫⁻ h : rationalTorusUnipotent K, φ ((h : AdelicGL2 (𝓞 K) K) * g₀) ∂(rationalTorusUnipotentHaar K)
      = (adelicAddHaar (𝓞 K) K (adelicBox K))⁻¹ *
          ∑' za : Kˣ × Kˣ, ∫⁻ x, φ (rationalScalarPoint K za.1 * rationalDiagOnePoint K za.2
            * unipotentGL2 x * g₀) ∂(adelicAddHaar (𝓞 K) K) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  have hint : Measurable fun h : rationalTorusUnipotent K => φ ((h : AdelicGL2 (𝓞 K) K) * g₀) :=
    hφ.comp (measurable_subtype_coe.mul_const g₀)
  unfold rationalTorusUnipotentHaar
  rw [lintegral_sum_measure, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun za => ?_
  rw [lintegral_map _ ((measurable_const.fun_mul measurable_subtype_coe).subtype_mk)]
  swap
  · exact hint
  unfold unipotentHaar
  rw [lintegral_map _ (measurable_toAdelicUnipotent K)]
  swap
  · exact hint.comp ((measurable_const.mul measurable_subtype_coe).subtype_mk)
  rw [lintegral_smul_measure, smul_eq_mul]
  simp only [coe_toAdelicUnipotent, rationalScalarPoint, rationalDiagOnePoint]

private theorem lintegral_rationalTorus_mul_unipotentGL2_mul (φ : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hφ : Measurable φ) (ζ a : Kˣ) (g₀ : AdelicGL2 (𝓞 K) K) :
    ∫⁻ x, φ (rationalScalarPoint K ζ * rationalDiagOnePoint K a * unipotentGL2 x * g₀)
        ∂(adelicAddHaar (𝓞 K) K)
      = ∫⁻ x, φ (unipotentGL2 x * (rationalScalarPoint K ζ * rationalDiagOnePoint K a * g₀))
          ∂(adelicAddHaar (𝓞 K) K) := by
  have hmeas : Measurable fun y : AdeleRing (𝓞 K) K =>
      φ (unipotentGL2 y * (rationalScalarPoint K ζ * rationalDiagOnePoint K a * g₀)) :=
    hφ.comp (continuous_unipotentGL2.measurable.mul_const _)
  have hmp := NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar (F := K) (a : K)
    (Units.ne_zero a)
  rw [← hmp.lintegral_comp hmeas]
  refine lintegral_congr fun x => ?_
  rw [rationalScalarPoint_mul_rationalDiagOnePoint_mul_unipotentGL2]
  simp only [mul_assoc]

private theorem tsum_lintegral_unipotentGL2_mul_eq_adelicAddHaar_adelicBox (φ : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hφ : Measurable φ) (g₀ : AdelicGL2 (𝓞 K) K)
    (h1 : ∫⁻ h : rationalTorusUnipotent K, φ ((h : AdelicGL2 (𝓞 K) K) * g₀) ∂(rationalTorusUnipotentHaar K)
      = 1) :
    ∑' za : Kˣ × Kˣ, ∫⁻ x, φ (unipotentGL2 x * (rationalScalarPoint K za.1 * rationalDiagOnePoint K za.2 * g₀))
        ∂(adelicAddHaar (𝓞 K) K)
      = adelicAddHaar (𝓞 K) K (adelicBox K) := by
  have h2 := h1
  rw [lintegral_rationalTorusUnipotentHaar_mul φ hφ g₀] at h2
  simp only [lintegral_rationalTorus_mul_unipotentGL2_mul φ hφ] at h2
  have hbox0 : adelicAddHaar (𝓞 K) K (adelicBox K) ≠ 0 := (adelicAddHaar_adelicBox_pos (K := K)).ne'
  have hboxT : adelicAddHaar (𝓞 K) K (adelicBox K) ≠ ∞ := (adelicAddHaar_adelicBox_lt_top (K := K)).ne
  calc _ = 1 * ∑' za : Kˣ × Kˣ, ∫⁻ x,
            φ (unipotentGL2 x * (rationalScalarPoint K za.1 * rationalDiagOnePoint K za.2 * g₀))
              ∂(adelicAddHaar (𝓞 K) K) := (one_mul _).symm
    _ = adelicAddHaar (𝓞 K) K (adelicBox K) * (adelicAddHaar (𝓞 K) K (adelicBox K))⁻¹ * ∑' za : Kˣ × Kˣ, ∫⁻ x,
            φ (unipotentGL2 x * (rationalScalarPoint K za.1 * rationalDiagOnePoint K za.2 * g₀))
              ∂(adelicAddHaar (𝓞 K) K) := by
          rw [ENNReal.mul_inv_cancel hbox0 hboxT]
    _ = adelicAddHaar (𝓞 K) K (adelicBox K) * ((adelicAddHaar (𝓞 K) K (adelicBox K))⁻¹ * ∑' za : Kˣ × Kˣ, ∫⁻ x,
            φ (unipotentGL2 x * (rationalScalarPoint K za.1 * rationalDiagOnePoint K za.2 * g₀))
              ∂(adelicAddHaar (𝓞 K) K)) := mul_assoc _ _ _
    _ = adelicAddHaar (𝓞 K) K (adelicBox K) * 1 := congrArg (adelicAddHaar (𝓞 K) K (adelicBox K) * ·) h2
    _ = adelicAddHaar (𝓞 K) K (adelicBox K) := mul_one _

variable (K)

private theorem rationalScalarPoint_eq_centralScalar (ζ : Kˣ) :
    rationalScalarPoint K ζ
      = centralScalar (𝓞 K) K
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) ζ) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [rationalScalarPoint_coe_apply, centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map,
      Matrix.scalar_apply, Matrix.diagonal]

private theorem rationalDiagOnePoint_eq_diagOne (a : Kˣ) :
    rationalDiagOnePoint K a
      = diagOne (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [rationalDiagOnePoint_coe_apply, diagOne, Units.coe_map, Matrix.diagonal]

private theorem bijective_rangeRestrict_unitsMap_algebraMap :
    Function.Bijective
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).rangeRestrict :=
  ⟨fun x y hxy =>
      Units.map_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K) (congrArg Subtype.val hxy),
    MonoidHom.rangeRestrict_surjective _⟩

private noncomputable def principalIdelesEquiv : Kˣ ≃ M4aHerbrand.principalIdeles (𝓞 K) K :=
  Equiv.ofBijective _ (bijective_rangeRestrict_unitsMap_algebraMap K)

private theorem coe_principalIdelesEquiv_apply (ζ : Kˣ) :
    ((principalIdelesEquiv K ζ : M4aHerbrand.principalIdeles (𝓞 K) K) : (AdeleRing (𝓞 K) K)ˣ)
      = Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) ζ :=
  rfl

variable {K}

private theorem ideleNorm_coe_principalIdeles (ζ : M4aHerbrand.principalIdeles (𝓞 K) K) :
    NumberField.TateGlobal.ideleNorm K (ζ : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
  obtain ⟨ζ₀, hζ₀⟩ := ζ.2
  unfold NumberField.TateGlobal.ideleNorm
  rw [← hζ₀]
  have e : Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) ζ₀
      = Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom ζ₀ := rfl
  rw [e, NumberField.AdeleRing.distribHaarChar_algebraMap K ζ₀]
  simp

private theorem tsum_tsum_lintegral_unipotentGL2_mul_centralScalar_mul_diagOne_eq_adelicAddHaar_adelicBox
    (φ : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hφ : Measurable φ) (g₀ : AdelicGL2 (𝓞 K) K)
    (h1 : ∫⁻ h : rationalTorusUnipotent K, φ ((h : AdelicGL2 (𝓞 K) K) * g₀) ∂(rationalTorusUnipotentHaar K)
      = 1) :
    ∑' ζ : M4aHerbrand.principalIdeles (𝓞 K) K, ∑' ξ : M4aHerbrand.principalIdeles (𝓞 K) K, ∫⁻ x,
        φ (unipotentGL2 x * (centralScalar (𝓞 K) K (ζ : (AdeleRing (𝓞 K) K)ˣ)
          * diagOne (ξ : (AdeleRing (𝓞 K) K)ˣ) * g₀)) ∂(adelicAddHaar (𝓞 K) K)
      = adelicAddHaar (𝓞 K) K (adelicBox K) := by
  set I : M4aHerbrand.principalIdeles (𝓞 K) K × M4aHerbrand.principalIdeles (𝓞 K) K → ℝ≥0∞ := fun p =>
    ∫⁻ x, φ (unipotentGL2 x * (centralScalar (𝓞 K) K (p.1 : (AdeleRing (𝓞 K) K)ˣ)
      * diagOne (p.2 : (AdeleRing (𝓞 K) K)ˣ) * g₀)) ∂(adelicAddHaar (𝓞 K) K) with hI
  calc _ = ∑' p : M4aHerbrand.principalIdeles (𝓞 K) K × M4aHerbrand.principalIdeles (𝓞 K) K, I p :=
          (ENNReal.tsum_prod' (f := I)).symm
    _ = ∑' za : Kˣ × Kˣ, I ((principalIdelesEquiv K).prodCongr (principalIdelesEquiv K) za) :=
          (((principalIdelesEquiv K).prodCongr (principalIdelesEquiv K)).tsum_eq I).symm
    _ = ∑' za : Kˣ × Kˣ, ∫⁻ x,
          φ (unipotentGL2 x * (rationalScalarPoint K za.1 * rationalDiagOnePoint K za.2 * g₀))
            ∂(adelicAddHaar (𝓞 K) K) := by
          refine tsum_congr fun za => ?_
          simp only [hI, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, coe_principalIdelesEquiv_apply,
            rationalScalarPoint_eq_centralScalar, rationalDiagOnePoint_eq_diagOne]
    _ = adelicAddHaar (𝓞 K) K (adelicBox K) :=
          tsum_lintegral_unipotentGL2_mul_eq_adelicAddHaar_adelicBox φ hφ g₀ h1

variable (F : Type) [Field F] [NumberField F] in

private theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 F) F)).symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

variable (F : Type) [Field F] [NumberField F] in

private theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_idele F
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar F
  infer_instance

end AutomorphicForm

namespace NumberField
p2m_export "NumberField" "AdeleRing.algebraMap_injective AdeleRing AdelicHaar.adeleBorel AdelicHaar.borelSpace_adeleBorel AdelicHaar.isAddHaarMeasure_adelicAddHaar AdelicHaar.glBorel AdelicHaar.borelSpace_glBorel Idele.ideleBorel Idele.borelSpace_ideleBorel Idele.idelicHaar Idele.isHaarMeasure_idelicHaar TateGlobal.ideleNorm TateGlobal.ideleNorm_mul AdeleRing.secondCountableTopology_generalLinearGroup_finTwo AdeleRing.secondCountableTopology AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar AdeleRing.distribHaarChar_algebraMap"
namespace Idele
p2m_export "NumberField.Idele" "ideleBorel borelSpace_ideleBorel idelicHaar isHaarMeasure_idelicHaar"
p2m_open "NumberField.Idele NumberField"

open M4aHerbrand

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

variable (F : Type) [Field F] [NumberField F]

private theorem countable_principalIdeles : Countable (principalIdeles (𝓞 F) F) := by
  haveI : Countable Fˣ := (show Function.Injective (Units.val : Fˣ → F) from fun _ _ h => Units.ext h).countable
  exact (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).rangeRestrict_surjective.countable

private theorem lintegral_idelicHaar_eq_tsum_principalIdeles_mul {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hD : IsFundamentalDomain (principalIdeles (𝓞 F) F) D (idelicHaar F))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) :
    ∫⁻ u, f u ∂(idelicHaar F) =
      ∑' ζ : principalIdeles (𝓞 F) F,
        ∫⁻ u in D, f ((ζ : (AdeleRing (𝓞 F) F)ˣ) * u) ∂(idelicHaar F) := by
  haveI : (idelicHaar F).IsHaarMeasure := isHaarMeasure_idelicHaar F
  haveI : SMulInvariantMeasure (AdeleRing (𝓞 F) F)ˣ (AdeleRing (𝓞 F) F)ˣ (idelicHaar F) :=
    ⟨fun c s _ => measure_preimage_mul (idelicHaar F) c s⟩
  haveI : Countable (principalIdeles (𝓞 F) F) := countable_principalIdeles F
  haveI : MeasurableConstSMul (principalIdeles (𝓞 F) F) (AdeleRing (𝓞 F) F)ˣ :=
    ⟨fun ζ => measurable_const_mul (ζ : (AdeleRing (𝓞 F) F)ˣ)⟩
  exact (hD.lintegral_eq_tsum' f).trans
    ((Equiv.inv (principalIdeles (𝓞 F) F)).tsum_eq fun ζ : principalIdeles (𝓞 F) F =>
      ∫⁻ u in D, f ((ζ : (AdeleRing (𝓞 F) F)ˣ) * u) ∂(idelicHaar F))

private theorem lintegral_lintegral_idelicHaar_eq_tsum_tsum_principalIdeles_mul
    {D D' : Set (AdeleRing (𝓞 F) F)ˣ}
    (hD : IsFundamentalDomain (principalIdeles (𝓞 F) F) D (idelicHaar F))
    (hD' : IsFundamentalDomain (principalIdeles (𝓞 F) F) D' (idelicHaar F))
    (f : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) :
    ∫⁻ u, ∫⁻ t, f u t ∂(idelicHaar F) ∂(idelicHaar F) =
      ∑' ζ : principalIdeles (𝓞 F) F, ∫⁻ u in D,
        ∑' ξ : principalIdeles (𝓞 F) F, ∫⁻ t in D',
          f ((ζ : (AdeleRing (𝓞 F) F)ˣ) * u) ((ξ : (AdeleRing (𝓞 F) F)ˣ) * t) ∂(idelicHaar F)
        ∂(idelicHaar F) := by
  rw [lintegral_idelicHaar_eq_tsum_principalIdeles_mul F hD (fun u => ∫⁻ t, f u t ∂(idelicHaar F))]
  exact tsum_congr fun ζ => lintegral_congr fun u =>
    lintegral_idelicHaar_eq_tsum_principalIdeles_mul F hD' (f ((ζ : (AdeleRing (𝓞 F) F)ˣ) * u))

end NumberField.Idele

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar unipotentGL2 AdelicGL2 globalPoints centralScalar adelicMaximalCompact maximalCompactHaar continuous_unipotentGL2 isClosed_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
p2m_open "AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

section Coordinates

variable (F : Type) [Field F] [NumberField F]

private theorem measurable_out_of_forall_rationalTorusUnipotent_mul {X : Type*} [MeasurableSpace X]
    {G : AdelicGL2 (𝓞 F) F → X} (hG : Measurable G)
    (hinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g, G (x * g) = G g) :
    Measurable fun q : RationalTorusUnipotentQuotient F => G q.out := by
  refine measurable_from_quotient.2 ?_
  have hcomp : ((fun q : RationalTorusUnipotentQuotient F => G q.out) ∘ Quotient.mk'') = G := by
    funext g
    show G (Quotient.mk'' g : RationalTorusUnipotentQuotient F).out = G g
    have hobt1 := MulAction.orbitRel_apply.1
      (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' g : RationalTorusUnipotentQuotient F)))
    obtain ⟨x, hx⟩ := hobt1
    rw [← hx]
    exact hinv x x.2 g
  rw [hcomp]
  exact hG

private noncomputable def torusIwasawaMap
    (p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) : AdelicGL2 (𝓞 F) F :=
  centralScalar (𝓞 F) F p.1 * diagOne p.2.1 * (p.2.2 : AdelicGL2 (𝓞 F) F)

private theorem continuous_centralScalar : Continuous (centralScalar (𝓞 F) F) := by
  show Continuous (Units.map (Matrix.scalar (Fin 2) : AdeleRing (𝓞 F) F →+* Matrix (Fin 2) (Fin 2)
    (AdeleRing (𝓞 F) F)).toMonoidHom)
  refine Continuous.units_map _ ?_
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

private theorem continuous_diagOne :
    Continuous (fun t : (AdeleRing (𝓞 F) F)ˣ => (diagOne t : AdelicGL2 (𝓞 F) F)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => (t : AdeleRing (𝓞 F) F)
      exact Units.continuous_val
    · exact continuous_const
  · simp_rw [← map_inv]
    show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => ((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      exact Units.continuous_coe_inv
    · exact continuous_const

private theorem measurable_torusIwasawaMap : Measurable (torusIwasawaMap F) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  exact (((continuous_centralScalar F).measurable.comp measurable_fst).mul
      ((continuous_diagOne F).measurable.comp (measurable_fst.comp measurable_snd))).mul
    (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))

variable {F}

private theorem apply_out_mk_of_forall_rationalTorusUnipotent_mul {X : Type*} {G : AdelicGL2 (𝓞 F) F → X}
    (hinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, G (x * g) = G g)
    (g : AdelicGL2 (𝓞 F) F) :
    G (Quotient.mk'' g : RationalTorusUnipotentQuotient F).out = G g := by
  have hobt2 := MulAction.orbitRel_apply.1
    (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' g : RationalTorusUnipotentQuotient F)))
  obtain ⟨x, hx⟩ := hobt2
  rw [← hx]
  exact hinv x x.2 g

end Coordinates

end AutomorphicForm

namespace HaarQuotient
p2m_export "HaarQuotient" "weight density measure lintegral_density_mul_eq_one"
p2m_open "HaarQuotient"

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G]

omit [IsTopologicalGroup G] [SecondCountableTopology G] in

private theorem measurable_weight (H : Subgroup G) (μH : Measure H) : Measurable (weight H μH) := by
  unfold weight
  split_ifs with h
  · refine Measurable.tsum fun n => ?_
    exact (measurable_const.indicator isOpen_interior.measurableSet).const_mul _
  · exact measurable_const

private theorem measurable_lintegral_weight_mul (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable fun g : G => ∫⁻ x : H, weight H μH ((x : G) * g) ∂μH := by
  have hw := measurable_weight (G := G) H μH
  have hu : Measurable (Function.uncurry fun (g : G) (x : H) => weight H μH ((x : G) * g)) :=
    hw.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)
  exact hu.lintegral_prod_right

private theorem measurable_density (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable (density H μH) := by
  have h1 := measurable_weight (G := G) H μH
  have h2 := measurable_lintegral_weight_mul (G := G) H μH
  have hd : density H μH = fun g => weight H μH g * (∫⁻ x : H, weight H μH ((x : G) * g) ∂μH)⁻¹ := by
    funext g
    simp only [density, div_eq_mul_inv]
  rw [hd]
  exact h1.mul h2.inv

end HaarQuotient

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar unipotentGL2 AdelicGL2 globalPoints centralScalar adelicMaximalCompact maximalCompactHaar continuous_unipotentGL2 isClosed_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
p2m_open "AutomorphicForm"

p2m_open "NumberField P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.NumberField NumberField.TateGlobal"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

variable (K : Type) [Field K] [NumberField K]

private theorem measurable_ofReal_ideleNorm_inv :
    Measurable fun t : (AdeleRing (𝓞 K) K)ˣ => ENNReal.ofReal ((ideleNorm K t)⁻¹) :=
  ((continuous_ideleNorm K).measurable.inv).ennreal_ofReal

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem sigmaFinite_adelicAddHaar : SigmaFinite (adelicAddHaar (𝓞 K) K) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology K
  infer_instance

private theorem sFinite_unipotentHaar : SFinite (unipotentHaar K) := by
  haveI := sigmaFinite_adelicAddHaar K
  unfold unipotentHaar
  infer_instance

private theorem sFinite_rationalTorusUnipotentHaar : SFinite (rationalTorusUnipotentHaar K) := by
  haveI := sFinite_unipotentHaar K
  haveI : Countable Kˣ := Units.val_injective.countable
  unfold rationalTorusUnipotentHaar
  infer_instance

private theorem measurable_density_rationalTorusUnipotent :
    Measurable (HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI := sFinite_rationalTorusUnipotentHaar K
  exact HaarQuotient.measurable_density _ _

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar unipotentGL2 AdelicGL2 globalPoints centralScalar adelicMaximalCompact maximalCompactHaar continuous_unipotentGL2 isClosed_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
p2m_open "AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

section TorusIwasawaIntegrand

variable {K : Type} [Field K] [NumberField K]

private theorem unipotentGL2_mem_rationalTorusUnipotent (x : AdeleRing (𝓞 K) K) :
    (unipotentGL2 x : AdelicGL2 (𝓞 K) K) ∈ rationalTorusUnipotent K := by
  rw [← coe_toAdelicUnipotent K x]
  exact Subgroup.mem_sup_right (toAdelicUnipotent K x).2

private theorem centralScalar_mul_diagOne_mem_rationalTorusUnipotent
    (ζ ξ : M4aHerbrand.principalIdeles (𝓞 K) K) :
    centralScalar (𝓞 K) K (ζ : (AdeleRing (𝓞 K) K)ˣ) * diagOne (ξ : (AdeleRing (𝓞 K) K)ˣ)
      ∈ rationalTorusUnipotent K := by
  have hz := (principalIdelesEquiv K).surjective ζ
  have ha := (principalIdelesEquiv K).surjective ξ
  obtain ⟨z, rfl⟩ := hz
  obtain ⟨a, rfl⟩ := ha
  rw [coe_principalIdelesEquiv_apply, coe_principalIdelesEquiv_apply,
    ← rationalScalarPoint_eq_centralScalar, ← rationalDiagOnePoint_eq_diagOne]
  exact Subgroup.mem_sup_left (Subgroup.mul_mem_sup ⟨z, rfl⟩ ⟨a, rfl⟩)

private theorem centralScalar_mul_comm (u : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K u * g = g * centralScalar (𝓞 K) K u := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [centralScalar, Matrix.GeneralLinearGroup.scalar, Units.coe_map, Matrix.mul_apply,
      Matrix.scalar_apply, Matrix.diagonal, mul_comm]

private theorem centralScalar_mul_mul_diagOne_mul (ζ u ξ t : (AdeleRing (𝓞 K) K)ˣ) :
    centralScalar (𝓞 K) K (ζ * u) * diagOne (ξ * t)
      = centralScalar (𝓞 K) K ζ * diagOne ξ * (centralScalar (𝓞 K) K u * diagOne t) := by
  rw [map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (centralScalar (𝓞 K) K u),
    centralScalar_mul_comm u (diagOne ξ), mul_assoc]

private theorem lintegral_out_rationalTorusUnipotentQuotientMeasure_eq_lintegral_density_mul
    (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
      ∫⁻ g, HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K) g * f g
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  unfold rationalTorusUnipotentQuotientMeasure HaarQuotient.measure
  rw [lintegral_map (measurable_out_of_forall_rationalTorusUnipotent_mul K hf hinv)
    measurable_quotient_mk'']
  have hcongr : (fun g : AdelicGL2 (𝓞 K) K =>
      f (Quotient.mk'' g : RationalTorusUnipotentQuotient K).out) = f :=
    funext fun g => apply_out_mk_of_forall_rationalTorusUnipotent_mul hinv g
  rw [hcongr, lintegral_withDensity_eq_lintegral_mul _ (measurable_density_rationalTorusUnipotent K) hf]
  rfl

private noncomputable def torusIwasawaIntegrand (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (x : AdeleRing (𝓞 K) K)
    (u t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K) : ℝ≥0∞ :=
  HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
      (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
    (f (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
      ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))

private theorem measurable_torusIwasawaIntegrand (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ ×
        adelicMaximalCompact K => torusIwasawaIntegrand f p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  have hΘ : Measurable fun p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ ×
      adelicMaximalCompact K => torusIwasawaMap K p.2 :=
    (measurable_torusIwasawaMap K).comp measurable_snd
  have hn : Measurable fun p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ ×
      adelicMaximalCompact K => (unipotentGL2 p.1 : AdelicGL2 (𝓞 K) K) :=
    continuous_unipotentGL2.measurable.comp measurable_fst
  have hP : Measurable fun p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ ×
      adelicMaximalCompact K =>
        unipotentGL2 p.1 * centralScalar (𝓞 K) K p.2.1 * diagOne p.2.2.1
          * (p.2.2.2 : AdelicGL2 (𝓞 K) K) := by
    have e : (fun p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ ×
        adelicMaximalCompact K =>
          unipotentGL2 p.1 * centralScalar (𝓞 K) K p.2.1 * diagOne p.2.2.1
            * (p.2.2.2 : AdelicGL2 (𝓞 K) K))
        = fun p => unipotentGL2 p.1 * torusIwasawaMap K p.2 := by
      funext p
      simp only [torusIwasawaMap, mul_assoc]
    rw [e]
    exact hn.mul hΘ
  have hw : Measurable fun p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ ×
      adelicMaximalCompact K => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K p.2.2.1)⁻¹) :=
    (measurable_ofReal_ideleNorm_inv K).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hfΘ : Measurable fun p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ ×
      adelicMaximalCompact K => f (centralScalar (𝓞 K) K p.2.1 * diagOne p.2.2.1
        * (p.2.2.2 : AdelicGL2 (𝓞 K) K)) :=
    hf.comp hΘ
  unfold torusIwasawaIntegrand
  exact ((measurable_density_rationalTorusUnipotent K).comp hP).mul (hfΘ.mul hw)

end TorusIwasawaIntegrand

end AutomorphicForm

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar unipotentGL2 AdelicGL2 globalPoints centralScalar adelicMaximalCompact maximalCompactHaar continuous_unipotentGL2 isClosed_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant"
p2m_open "AutomorphicForm"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

section TorusComputation

variable {K : Type} [Field K] [NumberField K]

private theorem torusIwasawaIntegrand_coe_mul_coe_mul (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞)
    (hinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g)
    (ζ ξ : M4aHerbrand.principalIdeles (𝓞 K) K) (x : AdeleRing (𝓞 K) K)
    (u t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K) :
    torusIwasawaIntegrand f x ((ζ : (AdeleRing (𝓞 K) K)ˣ) * u) ((ξ : (AdeleRing (𝓞 K) K)ˣ) * t) k
      = HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
          (unipotentGL2 x * (centralScalar (𝓞 K) K (ζ : (AdeleRing (𝓞 K) K)ˣ)
            * diagOne (ξ : (AdeleRing (𝓞 K) K)ˣ)
            * (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)))) *
        (f (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)) := by
  unfold torusIwasawaIntegrand
  have e1 := centralScalar_mul_mul_diagOne_mul (K := K) (ζ : (AdeleRing (𝓞 K) K)ˣ) u
    (ξ : (AdeleRing (𝓞 K) K)ˣ) t
  have e2 : unipotentGL2 x * centralScalar (𝓞 K) K ((ζ : (AdeleRing (𝓞 K) K)ˣ) * u)
        * diagOne ((ξ : (AdeleRing (𝓞 K) K)ˣ) * t) * (k : AdelicGL2 (𝓞 K) K)
      = unipotentGL2 x * (centralScalar (𝓞 K) K (ζ : (AdeleRing (𝓞 K) K)ˣ)
          * diagOne (ξ : (AdeleRing (𝓞 K) K)ˣ)
          * (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K))) := by
    rw [mul_assoc (unipotentGL2 x : AdelicGL2 (𝓞 K) K), e1]
    simp only [mul_assoc]
  have e3 : f (centralScalar (𝓞 K) K ((ζ : (AdeleRing (𝓞 K) K)ˣ) * u)
        * diagOne ((ξ : (AdeleRing (𝓞 K) K)ˣ) * t) * (k : AdelicGL2 (𝓞 K) K))
      = f (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) := by
    rw [e1, mul_assoc]
    exact hinv _ (centralScalar_mul_diagOne_mem_rationalTorusUnipotent ζ ξ) _
  have e4 : NumberField.TateGlobal.ideleNorm K ((ξ : (AdeleRing (𝓞 K) K)ˣ) * t)
      = NumberField.TateGlobal.ideleNorm K t := by
    rw [NumberField.TateGlobal.ideleNorm_mul, ideleNorm_coe_principalIdeles, one_mul]
  rw [e2, e3, e4]

private theorem measurable_density_unipotentGL2_mul (g : AdelicGL2 (𝓞 K) K) :
    Measurable fun x : AdeleRing (𝓞 K) K =>
      HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
        (unipotentGL2 x * g) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  exact (measurable_density_rationalTorusUnipotent K).comp
    (continuous_unipotentGL2.measurable.mul_const g)

private theorem measurable_density_unipotentGL2_mul_mul_torusIwasawaMap (γ : AdelicGL2 (𝓞 K) K) :
    Measurable fun p : AdeleRing (𝓞 K) K × (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ ×
        adelicMaximalCompact K =>
      HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
        (unipotentGL2 p.1 * (γ * torusIwasawaMap K p.2)) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  exact (measurable_density_rationalTorusUnipotent K).comp
    ((continuous_unipotentGL2.measurable.comp measurable_fst).mul
      (((measurable_torusIwasawaMap K).comp measurable_snd).const_mul γ))

end TorusComputation

end AutomorphicForm

open MeasureTheory _root_.NumberField _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm in

open scoped ENNReal in

private theorem lintegral_lintegral_lintegral_lintegral_swap_innermost
    {W X Y : Type*} [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure W) (ν : Measure X) (κ : Measure Y) [SFinite μ] [SFinite ν] [SFinite κ]
    (F : W → X → X → Y → ℝ≥0∞) (hF : Measurable fun p : W × X × X × Y => F p.1 p.2.1 p.2.2.1 p.2.2.2) :
    ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k, F x u t k ∂κ ∂ν ∂ν ∂μ = ∫⁻ u, ∫⁻ t, ∫⁻ k, ∫⁻ x, F x u t k ∂μ ∂κ ∂ν ∂ν := by
  have hIk : Measurable fun r : W × X × X => ∫⁻ k, F r.1 r.2.1 r.2.2 k ∂κ := by
    have h : Measurable fun q : (W × X × X) × Y => F q.1.1 q.1.2.1 q.1.2.2 q.2 :=
      hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
        (measurable_fst.snd.snd.prodMk measurable_snd)))
    exact h.lintegral_prod_right' (ν := κ)
  have hItk : Measurable fun s : W × X => ∫⁻ t, ∫⁻ k, F s.1 s.2 t k ∂κ ∂ν :=
    (hIk.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right' (ν := ν)
  have h1 : AEMeasurable (Function.uncurry fun x u => ∫⁻ t, ∫⁻ k, F x u t k ∂κ ∂ν) (μ.prod ν) :=
    hItk.aemeasurable
  have h2 : ∀ u, AEMeasurable (Function.uncurry fun x t => ∫⁻ k, F x u t k ∂κ) (μ.prod ν) := fun u =>
    (hIk.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).aemeasurable
  have h3 : ∀ u t, AEMeasurable (Function.uncurry fun x k => F x u t k) (μ.prod κ) := fun u t =>
    (hF.comp (measurable_fst.prodMk (measurable_const.prodMk
      (measurable_const.prodMk measurable_snd)))).aemeasurable
  rw [lintegral_lintegral_swap h1]
  refine lintegral_congr fun u => ?_
  rw [lintegral_lintegral_swap (h2 u)]
  refine lintegral_congr fun t => ?_
  rw [lintegral_lintegral_swap (h3 u t)]

open MeasureTheory _root_.NumberField _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm in

open scoped ENNReal in

private theorem tsum_setLIntegral_tsum_setLIntegral_lintegral_mul_eq_const_mul
    {ι X Y : Type*} [Countable ι] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (κ : Measure Y) [SFinite ν] [SFinite κ] (D D' : Set X)
    (A : ι → ι → X → X → Y → ℝ≥0∞) (B : X → X → Y → ℝ≥0∞) (c : ℝ≥0∞) (hc' : c ≠ ∞)
    (hA : ∀ i j, Measurable fun y : X × X × Y => A i j y.1 y.2.1 y.2.2)
    (hB : Measurable fun y : X × X × Y => B y.1 y.2.1 y.2.2)
    (hc : ∀ u t k, ∑' i, ∑' j, A i j u t k = c) :
    ∑' i, ∫⁻ u in D, ∑' j, ∫⁻ t in D', ∫⁻ k, A i j u t k * B u t k ∂κ ∂ν ∂ν
      = c * ∫⁻ u in D, ∫⁻ t in D', ∫⁻ k, B u t k ∂κ ∂ν ∂ν := by
  have hre : Measurable fun q : (X × X) × Y => (q.1.1, q.1.2, q.2) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hAB : ∀ i j, Measurable fun y : X × X × Y => A i j y.1 y.2.1 y.2.2 * B y.1 y.2.1 y.2.2 :=
    fun i j => (hA i j).mul hB
  have hS : ∀ i, Measurable fun y : X × X × Y => ∑' j, A i j y.1 y.2.1 y.2.2 * B y.1 y.2.1 y.2.2 :=
    fun i => Measurable.tsum fun j => hAB i j

  have hin : ∀ i u, ∑' j, ∫⁻ t in D', ∫⁻ k, A i j u t k * B u t k ∂κ ∂ν
      = ∫⁻ t in D', ∫⁻ k, ∑' j, A i j u t k * B u t k ∂κ ∂ν := by
    intro i u
    have h1 : ∀ j, AEMeasurable (fun t => ∫⁻ k, A i j u t k * B u t k ∂κ) (ν.restrict D') := fun j =>
      (((hAB i j).comp (measurable_const.prodMk measurable_id)).lintegral_prod_right' (ν := κ)).aemeasurable
    have h2 : ∀ t j, AEMeasurable (fun k => A i j u t k * B u t k) κ := fun t j =>
      ((hAB i j).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aemeasurable
    rw [← lintegral_tsum h1]
    exact lintegral_congr fun t => (lintegral_tsum (h2 t)).symm
  simp_rw [hin]

  have h3 : ∀ i, AEMeasurable (fun u => ∫⁻ t in D', ∫⁻ k, ∑' j, A i j u t k * B u t k ∂κ ∂ν) (ν.restrict D) :=
    fun i => ((((hS i).comp hre).lintegral_prod_right' (ν := κ)).lintegral_prod_right'
      (ν := ν.restrict D')).aemeasurable
  have h4 : ∀ u i, AEMeasurable (fun t => ∫⁻ k, ∑' j, A i j u t k * B u t k ∂κ) (ν.restrict D') := fun u i =>
    (((hS i).comp (measurable_const.prodMk measurable_id)).lintegral_prod_right' (ν := κ)).aemeasurable
  have h5 : ∀ u t i, AEMeasurable (fun k => ∑' j, A i j u t k * B u t k) κ := fun u t i =>
    ((hS i).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aemeasurable
  rw [← lintegral_tsum h3]
  have hin2 : ∀ u, ∑' i, ∫⁻ t in D', ∫⁻ k, ∑' j, A i j u t k * B u t k ∂κ ∂ν
      = ∫⁻ t in D', ∫⁻ k, c * B u t k ∂κ ∂ν := by
    intro u
    rw [← lintegral_tsum (h4 u)]
    refine lintegral_congr fun t => ?_
    rw [← lintegral_tsum (h5 u t)]
    refine lintegral_congr fun k => ?_
    simp_rw [ENNReal.tsum_mul_right]
    rw [hc]
  simp_rw [hin2]
  simp only [lintegral_const_mul' c _ hc']

open MeasureTheory _root_.NumberField _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm in

open scoped ENNReal in
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in

private theorem lintegral_torusIwasawaIntegrand_eq_box_mul_setLIntegral (K : Type) [Field K] [NumberField K]
    {D D' : Set (AdeleRing (𝓞 K) K)ˣ}
    (hD : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (hD' : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D' (NumberField.Idele.idelicHaar K))
    (f : AdelicGL2 (𝓞 K) K → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) :
    ∫⁻ u, ∫⁻ t, ∫⁻ k, ∫⁻ x, torusIwasawaIntegrand f x u t k ∂(adelicAddHaar (𝓞 K) K)
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
      = adelicAddHaar (𝓞 K) K (adelicBox K) * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
          f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
        ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  classical
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : SigmaFinite (NumberField.Idele.idelicHaar K) := sigmaFinite_idelicHaar K
  haveI : SigmaFinite (adelicAddHaar (𝓞 K) K) := sigmaFinite_adelicAddHaar K
  haveI : Countable (M4aHerbrand.principalIdeles (𝓞 K) K) := NumberField.Idele.countable_principalIdeles K
  haveI := (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K).1
  haveI := (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant K).2
  have hρ : Measurable
      (HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)) :=
    measurable_density_rationalTorusUnipotent K
  have hbox_top : adelicAddHaar (𝓞 K) K (adelicBox K) ≠ ∞ := (adelicAddHaar_adelicBox_lt_top K).ne

  rw [NumberField.Idele.lintegral_lintegral_idelicHaar_eq_tsum_tsum_principalIdeles_mul K hD hD'
    (fun u t => ∫⁻ k, ∫⁻ x, torusIwasawaIntegrand f x u t k ∂(adelicAddHaar (𝓞 K) K)
      ∂(maximalCompactHaar K))]

  simp only [torusIwasawaIntegrand_coe_mul_coe_mul f hinv]
  have hpull : ∀ (γ g₀ : AdelicGL2 (𝓞 K) K) (C : ℝ≥0∞),
      ∫⁻ x, HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
          (unipotentGL2 x * (γ * g₀)) * C ∂(adelicAddHaar (𝓞 K) K)
        = (∫⁻ x, HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
            (unipotentGL2 x * (γ * g₀)) ∂(adelicAddHaar (𝓞 K) K)) * C :=
    fun γ g₀ C => lintegral_mul_const C (measurable_density_unipotentGL2_mul (γ * g₀))
  simp only [hpull]

  have hbr : ∀ g₀ : AdelicGL2 (𝓞 K) K,
      ∑' ζ : M4aHerbrand.principalIdeles (𝓞 K) K, ∑' ξ : M4aHerbrand.principalIdeles (𝓞 K) K,
        ∫⁻ x, HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
          (unipotentGL2 x * (centralScalar (𝓞 K) K (ζ : (AdeleRing (𝓞 K) K)ˣ)
            * diagOne (ξ : (AdeleRing (𝓞 K) K)ˣ) * g₀)) ∂(adelicAddHaar (𝓞 K) K)
      = adelicAddHaar (𝓞 K) K (adelicBox K) := fun g₀ =>
    tsum_tsum_lintegral_unipotentGL2_mul_centralScalar_mul_diagOne_eq_adelicAddHaar_adelicBox _ hρ g₀
      (HaarQuotient.lintegral_density_mul_eq_one (rationalTorusUnipotent K)
        (isClosed_rationalTorusUnipotent K) (rationalTorusUnipotentHaar K) g₀)

  have hA : ∀ ζ ξ : M4aHerbrand.principalIdeles (𝓞 K) K, Measurable
      fun y : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
        ∫⁻ x, HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
          (unipotentGL2 x * (centralScalar (𝓞 K) K (ζ : (AdeleRing (𝓞 K) K)ˣ)
            * diagOne (ξ : (AdeleRing (𝓞 K) K)ˣ)
            * (centralScalar (𝓞 K) K y.1 * diagOne y.2.1 * (y.2.2 : AdelicGL2 (𝓞 K) K))))
          ∂(adelicAddHaar (𝓞 K) K) := by
    intro ζ ξ
    simpa only [torusIwasawaMap] using
      (measurable_density_unipotentGL2_mul_mul_torusIwasawaMap
        (centralScalar (𝓞 K) K (ζ : (AdeleRing (𝓞 K) K)ˣ)
          * diagOne (ξ : (AdeleRing (𝓞 K) K)ˣ))).lintegral_prod_left' (μ := adelicAddHaar (𝓞 K) K)
  have hB : Measurable fun y : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ × adelicMaximalCompact K =>
      f (centralScalar (𝓞 K) K y.1 * diagOne y.2.1 * (y.2.2 : AdelicGL2 (𝓞 K) K)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K y.2.1)⁻¹) := by
    simpa only [Function.comp_def, torusIwasawaMap] using
      (hf.comp (measurable_torusIwasawaMap K)).fun_mul
        ((measurable_ofReal_ideleNorm_inv K).comp (measurable_fst.comp measurable_snd))

  exact tsum_setLIntegral_tsum_setLIntegral_lintegral_mul_eq_const_mul
    (NumberField.Idele.idelicHaar K) (maximalCompactHaar K) D D'
    (fun (ζ ξ : M4aHerbrand.principalIdeles (𝓞 K) K) (u t : (AdeleRing (𝓞 K) K)ˣ)
        (k : adelicMaximalCompact K) =>
      ∫⁻ x, HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
        (unipotentGL2 x * (centralScalar (𝓞 K) K (ζ : (AdeleRing (𝓞 K) K)ˣ)
          * diagOne (ξ : (AdeleRing (𝓞 K) K)ˣ)
          * (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)))) ∂(adelicAddHaar (𝓞 K) K))
    (fun (u t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K) =>
      f (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹))
    (adelicAddHaar (𝓞 K) K (adelicBox K)) hbox_top hA hB
    (fun u t k => hbr (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)))

open MeasureTheory _root_.NumberField _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm in

open scoped ENNReal in
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in
private theorem solution_core
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ (D D' : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D' (NumberField.Idele.idelicHaar K) →
      ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
          c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  classical
  have hIw := NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa K
  obtain ⟨c₀, hc₀, hc₀', hI⟩ := hIw
  have hbox_pos := adelicAddHaar_adelicBox_pos K
  have hbox_top : adelicAddHaar (𝓞 K) K (adelicBox K) ≠ ∞ := (adelicAddHaar_adelicBox_lt_top K).ne
  refine ⟨c₀ * adelicAddHaar (𝓞 K) K (adelicBox K), mul_ne_zero hc₀ hbox_pos.ne',
    ENNReal.mul_ne_top hc₀' hbox_top, ?_⟩
  intro D D' _ _ hD hD' f hf hinv
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : SigmaFinite (NumberField.Idele.idelicHaar K) := sigmaFinite_idelicHaar K
  haveI : SigmaFinite (adelicAddHaar (𝓞 K) K) := sigmaFinite_adelicAddHaar K
  have hρ : Measurable
      (HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)) :=
    measurable_density_rationalTorusUnipotent K

  rw [lintegral_out_rationalTorusUnipotentQuotientMeasure_eq_lintegral_density_mul f hf hinv,
    hI _ (hρ.fun_mul hf), mul_assoc c₀ (adelicAddHaar (𝓞 K) K (adelicBox K))]
  refine congrArg (fun y => c₀ * y) ?_

  have hF : ∀ (x : AdeleRing (𝓞 K) K) (u t : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
      HaarQuotient.density (rationalTorusUnipotent K) (rationalTorusUnipotentHaar K)
          (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
        f (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
      = torusIwasawaIntegrand f x u t k := by
    intro x u t k
    have hn : f (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K))
        = f (centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) := by
      rw [mul_assoc, mul_assoc, hinv _ (unipotentGL2_mem_rationalTorusUnipotent x), ← mul_assoc]
    rw [hn, torusIwasawaIntegrand, mul_assoc]
  simp only [hF]

  rw [lintegral_lintegral_lintegral_lintegral_swap_innermost (adelicAddHaar (𝓞 K) K)
    (NumberField.Idele.idelicHaar K) (maximalCompactHaar K) (torusIwasawaIntegrand f)
    (measurable_torusIwasawaIntegrand f hf)]
  exact lintegral_torusIwasawaIntegrand_eq_box_mul_setLIntegral K hD hD' f hf hinv

open MeasureTheory _root_.NumberField _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.AutomorphicForm in

open scoped ENNReal in
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ (D D' : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D' (NumberField.Idele.idelicHaar K) →
      ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
          c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by
  exact solution_core K

end S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
end P2MW
export P2MW.S_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa (solution)
