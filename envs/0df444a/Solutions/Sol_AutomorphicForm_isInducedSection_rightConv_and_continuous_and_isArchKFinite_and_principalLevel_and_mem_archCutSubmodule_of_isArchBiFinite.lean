-- Prove2me | solution 1 for AutomorphicForm.isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/987b316f-0527-5c31-9638-dede751e36a3

import Theorems.Thm_AutomorphicForm_isArchKFinite_rightConv_of_isInducedSection_of_comp_inv_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (_hφc : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (_hfF : IsFactorizableTestFn K f)
    (_hfbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (_hfty : IsArchBiFinite K tysK f) :
    letI := adeleBorel (𝓞 K) K
    IsInducedSection (𝓞 K) K χ₁ χ₂ (rightConv K φ f) ∧
    Continuous (rightConv K φ f) ∧
    IsArchKFinite K (rightConv K φ f) ∧
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, rightConv K φ f (g * u) = rightConv K φ f g) ∧
    rightConv K φ f ∈ archCutSubmodule K tysK := by
  classical
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  have hf0 : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro b hb g
    rw [rightConv_apply, rightConv_apply, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show φ (b * g * y) * f y = _
    rw [mul_assoc, _hφ b hb (g * y), mul_assoc]
  ·
    have hF : Continuous (Function.uncurry fun (g y : AdelicGL2 (𝓞 K) K) => φ (g * y) * f y) :=
      (_hφc.comp (continuous_fst.mul continuous_snd)).mul (_hf.comp continuous_snd)
    have h := continuous_parametric_integral_of_continuous (μ := adelicGLHaar (Fin 2) (𝓞 K) K) hF _hfc
    refine h.congr fun g => ?_
    rw [rightConv_apply]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hf0 y hy, mul_zero]
  · exact AutomorphicForm.isArchKFinite_rightConv_of_isInducedSection_of_comp_inv_mem_archCutSubmodule K χ₁ χ₂ φ
      _hφ _hφc f _hf _hfc tysK _hfty.1
  ·
    intro g u hu
    rw [rightConv_apply, rightConv_apply]
    have hu' : u⁻¹ ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := inv_mem hu
    calc (∫ y, φ (g * u * y) * f y ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
        = ∫ y, φ (g * (u * y)) * f (u⁻¹ * (u * y)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = ∫ y, φ (g * y) * f (u⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          integral_mul_left_eq_self (fun y => φ (g * y) * f (u⁻¹ * y)) u
      _ = ∫ y, φ (g * y) * f y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => by
            show φ (g * y) * f (u⁻¹ * y) = φ (g * y) * f y
            rw [(_hfbi u⁻¹ hu' y).1])
  · exact AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite K tysK φ _hφc f _hfF _hfty

end S_AutomorphicForm_isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite
end P2MW
export P2MW.S_AutomorphicForm_isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite (solution)
