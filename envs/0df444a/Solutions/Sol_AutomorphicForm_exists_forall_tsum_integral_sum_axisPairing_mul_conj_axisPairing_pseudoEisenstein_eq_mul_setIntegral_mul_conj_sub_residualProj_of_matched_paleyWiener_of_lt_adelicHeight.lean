-- Prove2me | solution 1 for AutomorphicForm.exists_forall_tsum_integral_sum_axisPairing_mul_conj_axisPairing_pseudoEisenstein_eq_mul_setIntegral_mul_conj_sub_residualProj_of_matched_paleyWiener_of_lt_adelicHeight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/734b84e4-b10f-55d1-86b0-a6ba0b351ffd

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
import Theorems.Thm_AutomorphicForm_exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener
import Theorems.Thm_AutomorphicForm_axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar
import Theorems.Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
import Theorems.Thm_AutomorphicForm_exists_isCompact_canonicalTruncationDomain_inter_setOf_adelicHeight_le_subset
import Theorems.Thm_AutomorphicForm_exists_forall_norm_axis_continuation_le_mul_pow_archParam_weight_of_isCompact_of_flat
import Theorems.Thm_AutomorphicForm_forall_isCompact_exists_forall_norm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_forall_exists_eLpNorm_axis_continuation_restrict_le_mul_pow_of_isCompact_of_ne_bot
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_sum_integral_sum_conj_inner_weylIntertwining_mul_setIntegral_mul_conj_axis_continuation_eq_of_isAutomorphicFnAt_of_lt_adelicHeight
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_tsum_integral_sum_axisPairing_mul_conj_axisPairing_pseudoEisenstein_eq_mul_setIntegral_mul_conj_sub_residualProj_of_matched_paleyWiener_of_lt_adelicHeight
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.iotaZsqrtdNegTwo_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply"
p2m_attr_erase "simp" "NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm
open scoped ENNReal

theorem tsum_integral_eq_sum_integral_comp_add_of_forall_not_mem_range
    {ιE ιP : Type} [Fintype ιP] (em : ιP → ιE) (hem : Function.Injective em) (τ : ιP → ℝ)
    (F : ιE → ℝ → ℂ) (hF : ∀ e : ιE, (∀ i : ιP, em i ≠ e) → ∀ t : ℝ, F e t = 0) :
    ∑' e : ιE, ∫ t : ℝ, F e t = ∑ i : ιP, ∫ t : ℝ, F (em i) (t + τ i) := by
  classical
  have hzero : ∀ e ∉ Finset.univ.image em, (∫ t : ℝ, F e t) = 0 := by
    intro e he
    have : ∀ i, em i ≠ e := fun i hi => he (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    simp only [hF e this, integral_zero]
  rw [tsum_eq_sum hzero, Finset.sum_image (fun i _ i' _ h => hem h)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (integral_add_right_eq_self (fun t => F (em i) t) (τ i)).symm

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ C : ℝ, 0 < C ∧
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
      (pψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hpψ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK pψ)
      (_hpψc : ∀ ε > (0:ℝ), ∃ r ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK r ∧ eLpNorm (pψ - r) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε)
      (_hpψo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (u : AdelicGL2 (𝓞 K) K → ℂ)
      (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
      (_hub : ∃ T : ℝ, ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
        T < NumberField.AdelicHeight.adelicHeight K g → u g = 0),
    (∀ (e : ιE) (j : Fin (nE e)), Integrable (fun t : ℝ => (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))) ∧
    Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))) ∧
    ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * conj (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      (C : ℂ) * ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        u g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  intro αm hαm
  classical
  obtain ⟨κ₁, hκ₁, hWP⟩ := AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
  obtain ⟨κ₂, hκ₂, hCP⟩ := AutomorphicForm.exists_forall_setIntegral_pseudoEisenstein_mul_conj_axis_continuation_eq_mul_integral_mul_conj_add_integral_mul_conj_weylIntertwining_of_matched_paleyWiener K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm
  refine ⟨2 * κ₂ / κ₁, by positivity, ?_⟩
  intro ι b cls hb hbn hbo hbs hbc ιE _iC μ ν hμE hνE hμicE hνicE hμcE hνcE hμνE hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP _iP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hr hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνcP hψdec ψ hψ hψrep em τ hem hψlev hψty pψ hpψ hpψc hpψo u hu hub
  have hW := hWP ι b cls hb hbn hbo hbs hbc ιE μ ν hμE hνE hμicE hνicE hμcE hνcE hμνE hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hr hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνcP hψdec ψ hψ hψrep em τ hem hψlev hψty pψ hpψ hpψc hpψo
  have hC := hCP ι b cls hb hbn hbo hbs hbc ιE μ ν hμE hνE hμicE hνicE hμcE hνcE hμνE hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hr hdistP ψf hψf hψjc hψhol hνcP hψdec ψ hψ hψrep em τ hem
  obtain ⟨hintY, hintX, hfold⟩ := AutomorphicForm.sum_integral_sum_conj_inner_weylIntertwining_mul_setIntegral_mul_conj_axis_continuation_eq_of_isAutomorphicFnAt_of_lt_adelicHeight K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν hμE hνE hμicE hνicE hμcE hνcE hμνE hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hr hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνcP hψdec ψ hψ hψrep em τ hem hψlev hψty u hu hub
  obtain ⟨hintX', hfub⟩ := AutomorphicForm.setIntegral_mul_conj_sum_integral_sum_inner_mul_axis_continuation_eq_sum_integral_sum_conj_inner_mul_setIntegral_of_isAutomorphicFnAt_of_lt_adelicHeight K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK hξu hαm ι b cls hb hbn hbo hbs hbc ιE μ ν hμE hνE hμicE hνicE hμcE hνcE hμνE hdistE nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan hpairs OE EE NE hEE ιP μP νP hμP hνP hμicP hνicP hμcP hμνP rP hr hdistP ψf hψf hψjc hψhol hψK hψsm hψKu hνcP hψdec ψ hψ hψrep em τ hem hψlev hψty u hu hub

  set TU : (e : ιE) → Fin (nE e) → ℝ → ℂ := fun e j t =>
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, u g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hTU
  set TP : (e : ιE) → Fin (nE e) → ℝ → ℂ := fun e j t =>
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, AutomorphicForm.pseudoEisenstein K ψ g * conj (EE e j ((t : ℂ) * Complex.I) g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hTP
  set c1 : (i : ιP) → Fin (nE (em i)) → ℝ → ℂ := fun i j t =>
    ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K) with hc1
  set c2 : (i : ιP) → Fin (nE (em i)) → ℝ → ℂ := fun i j t =>
    ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
              conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hc2

  have em_inj : Function.Injective em := by
    intro i i' h
    by_contra hne
    obtain ⟨x, hx, hsep⟩ := hdistP i i' hne
    have hx1 : NumberField.TateGlobal.ideleNorm K x = 1 := (NumberField.TateGlobal.mem_normOneIdeles_iff x).mp hx
    have h1 : NumberField.TateGlobal.normPowChar K (τ i) x = 1 :=
      NumberField.TateGlobal.normPowChar_eq_one_of_ideleNorm_eq_one (τ i) hx1
    have h2 : NumberField.TateGlobal.normPowChar K (τ i') x = 1 :=
      NumberField.TateGlobal.normPowChar_eq_one_of_ideleNorm_eq_one (τ i') hx1
    rcases hsep with hμ' | hν'
    · apply hμ'
      rw [(hem i).1, (hem i').1, MonoidHom.mul_apply, MonoidHom.mul_apply, h1, h2, h]
    · apply hν'
      rw [(hem i).2, (hem i').2, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
        MonoidHom.inv_apply, h1, h2, h]

  have hoff : ∀ e : ιE, (∀ i : ιP, em i ≠ e) → ∀ (j : Fin (nE e)) (t : ℝ), TP e j t = 0 :=
    fun e he j t => hC.1 e he j t
  have hon : ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
      TP (em i) j (t + τ i) = (κ₂ : ℂ) * (c1 i j t + c2 i j t) := fun i j t => hC.2 i j t

  have hshift : ∀ (i : ιP) (j : Fin (nE (em i))) (t : ℝ),
      TU (em i) j (t + τ i) * conj (TP (em i) j (t + τ i)) =
        (κ₂ : ℂ) * (conj (c1 i j t) * TU (em i) j (t + τ i)) + (κ₂ : ℂ) * (conj (c2 i j t) * TU (em i) j (t + τ i)) := by
    intro i j t
    rw [hon, map_mul, map_add, Complex.conj_ofReal]; ring

  have hint : ∀ (e : ιE) (j : Fin (nE e)), Integrable (fun t : ℝ => TU e j t * conj (TP e j t)) := by
    intro e j
    by_cases he : ∃ i, em i = e
    · obtain ⟨i, rfl⟩ := he
      have hs : Integrable (fun t : ℝ => TU (em i) j (t + τ i) * conj (TP (em i) j (t + τ i))) := by
        have h1 := ((hintX i j).const_mul (κ₂ : ℂ)).add ((hintY i j).const_mul (κ₂ : ℂ))
        refine h1.congr (Filter.Eventually.of_forall fun t => ?_)
        simp only [Pi.add_apply]
        rw [hshift]
      have := hs.comp_add_right (-τ i)
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp, neg_add_cancel_right, sub_eq_add_neg]
    · have hne : ∀ i, em i ≠ e := fun i hi => he ⟨i, hi⟩
      refine (integrable_zero ℝ ℂ volume).congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [hoff e hne, map_zero, mul_zero, Pi.zero_apply]

  have hsum : Summable (fun e : ιE => ∫ t : ℝ, ∑ j : Fin (nE e), TU e j t * conj (TP e j t)) := by
    apply summable_of_finite_support
    refine (Set.finite_range em).subset ?_
    intro e he
    by_contra hne
    apply he
    have hne' : ∀ i : ιP, em i ≠ e := fun i hi => hne ⟨i, hi⟩
    show ∫ t : ℝ, ∑ j : Fin (nE e), TU e j t * conj (TP e j t) = 0
    simp only [hoff e hne', map_zero, mul_zero, Finset.sum_const_zero, integral_zero]

  have X_def : ∀ i : ιP, Integrable (fun t : ℝ => ∑ j : Fin (nE (em i)), conj (c1 i j t) * TU (em i) j (t + τ i)) :=
    fun i => integrable_finset_sum _ fun j _ => hintX i j
  have Y_def : ∀ i : ιP, Integrable (fun t : ℝ => ∑ j : Fin (nE (em i)), conj (c2 i j t) * TU (em i) j (t + τ i)) :=
    fun i => integrable_finset_sum _ fun j _ => hintY i j
  have key : ∑' e : ιE, ∫ t : ℝ, ∑ j : Fin (nE e), TU e j t * conj (TP e j t) =
      ((2 * κ₂ / κ₁ : ℝ) : ℂ) * ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        u g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by

    rw [tsum_integral_eq_sum_integral_comp_add_of_forall_not_mem_range em em_inj τ
      (fun e t => ∑ j : Fin (nE e), TU e j t * conj (TP e j t))
      (fun e he t => by simp only [hoff e he, map_zero, mul_zero, Finset.sum_const_zero])]
    have hL : ∀ i : ιP, (∫ t : ℝ, ∑ j : Fin (nE (em i)), TU (em i) j (t + τ i) * conj (TP (em i) j (t + τ i))) =
        ((κ₂ : ℂ) * ∫ t : ℝ, ∑ j : Fin (nE (em i)), conj (c1 i j t) * TU (em i) j (t + τ i)) +
        ((κ₂ : ℂ) * ∫ t : ℝ, ∑ j : Fin (nE (em i)), conj (c2 i j t) * TU (em i) j (t + τ i)) := by
      intro i
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((X_def i).const_mul _) ((Y_def i).const_mul _)]
      congr 1; funext t
      simp only [hshift, Finset.sum_add_distrib, Finset.mul_sum]
    have hfold' : ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), conj (c2 i j t) * TU (em i) j (t + τ i) =
        ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), conj (c1 i j t) * TU (em i) j (t + τ i) := hfold
    simp only [hL, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hfold']

    have hR : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
        u g * conj (AutomorphicForm.pseudoEisenstein K ψ g - pψ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        (κ₁ : ℂ) * ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), conj (c1 i j t) * TU (em i) j (t + τ i) := by
      have hfub' : (∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          u g * conj (∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), c1 i j t * EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
          ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)), conj (c1 i j t) * TU (em i) j (t + τ i) := hfub
      rw [← hfub', ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hW] with g hg
      have hg' : AutomorphicForm.pseudoEisenstein K ψ g - pψ g = _ := hg
      rw [hg', map_mul, Complex.conj_ofReal]
      ring
    rw [hR]
    have hκ₁' : (κ₁ : ℂ) ≠ 0 := by exact_mod_cast hκ₁.ne'
    push_cast
    field_simp
    ring
  exact ⟨hint, hsum, key⟩

end S_AutomorphicForm_exists_forall_tsum_integral_sum_axisPairing_mul_conj_axisPairing_pseudoEisenstein_eq_mul_setIntegral_mul_conj_sub_residualProj_of_matched_paleyWiener_of_lt_adelicHeight
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_tsum_integral_sum_axisPairing_mul_conj_axisPairing_pseudoEisenstein_eq_mul_setIntegral_mul_conj_sub_residualProj_of_matched_paleyWiener_of_lt_adelicHeight (solution)
