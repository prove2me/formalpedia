-- Prove2me | solution 1 for AutomorphicForm.isSmoothCuspAutomorphicFnAt_of_continuous_of_principalLevel_of_ae_constantTerm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/acfee871-a5cd-5042-8d0e-20f3760ecf0f

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
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Mathlib
import Theorems.Thm_AutomorphicForm_isOpen_principalLevel
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_of_continuous_of_principalLevel_of_ae_constantTerm_eq_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

open AutomorphicForm FLT.SmoothVectors in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (_hf : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f)
    (_hfc : Continuous f)
    (_hflev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, f (g * u) = f g) :
    letI := adeleBorel (𝓞 K) K
    ∀ (_hct : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K),
        constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 f g = 0),
    IsSmoothCuspAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f := by
  intro hct
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 K) K

  set ν : Measure (AdeleRing (𝓞 K) K) := ((productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))).ν with hν
  have hνdef : ν = ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K) := rfl
  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset K
  have hcont : Continuous (fun g : AdelicGL2 (𝓞 K) K => constantTerm ν unipotentGL2 f g) := by
    have hF : Continuous (Function.uncurry fun (g : AdelicGL2 (𝓞 K) K) (a : AdeleRing (𝓞 K) K) => f (unipotentGL2 a * g)) :=
      _hfc.comp (((AutomorphicForm.CuspidalSpectrum.continuous_unipotentGL2_adele K).comp continuous_snd).mul continuous_fst)
    have hpar := continuous_parametric_integral_of_continuous
      (μ := (adelicAddHaar (𝓞 K) K).restrict (adelicBox K)) hF hCc
    have heq : (fun g : AdelicGL2 (𝓞 K) K => constantTerm ν unipotentGL2 f g) =
        fun g => ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹.toReal •
          ∫ a in C, f (unipotentGL2 a * g) ∂((adelicAddHaar (𝓞 K) K).restrict (adelicBox K)) := by
      funext g
      simp only [constantTerm, constantTermIntegrand, hνdef, ProbabilityTheory.cond, integral_smul_measure]
      congr 1
      rw [Measure.restrict_restrict hCc.isClosed.measurableSet, Set.inter_eq_right.mpr hBC]
    rw [heq]
    exact hpar.const_smul (((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹.toReal)
  have hzero : ∀ g : AdelicGL2 (𝓞 K) K, constantTerm ν unipotentGL2 f g = 0 := by
    have hae : (fun g : AdelicGL2 (𝓞 K) K => constantTerm ν unipotentGL2 f g) =ᵐ[adelicGLHaar (Fin 2) (𝓞 K) K] fun _ => (0 : ℂ) := hct
    have h := (Continuous.ae_eq_iff_eq (adelicGLHaar (Fin 2) (𝓞 K) K) hcont continuous_const).mp hae
    exact fun g => congrFun h g
  refine ⟨⟨_hf, hzero⟩, ?_⟩

  show IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup K)
    (RightTranslationFn.mk f : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ) :
      Subgroup (finiteAdelicGL2Subgroup K)) : Set (finiteAdelicGL2Subgroup K))
  have hVopen : IsOpen (((principalLevel (𝓞 K) K N).subgroupOf (finiteAdelicGL2Subgroup K) :
      Subgroup (finiteAdelicGL2Subgroup K)) : Set (finiteAdelicGL2Subgroup K)) :=
    (AutomorphicForm.isOpen_principalLevel K N hN).preimage continuous_subtype_val
  refine Subgroup.isOpen_mono ?_ hVopen
  intro k hk
  rw [MulAction.mem_stabilizer_iff]
  refine RightTranslationFn.ext fun x => ?_
  rw [Subgroup.smul_def, RightTranslationFn.toFun_smul]
  exact _hflev x k ⟨Subgroup.mem_subgroupOf.1 hk, k.2⟩

end

end S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_of_continuous_of_principalLevel_of_ae_constantTerm_eq_zero
end P2MW
export P2MW.S_AutomorphicForm_isSmoothCuspAutomorphicFnAt_of_continuous_of_principalLevel_of_ae_constantTerm_eq_zero (solution)
