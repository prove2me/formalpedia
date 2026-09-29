-- Prove2me | solution 1 for AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f98f04a9-4a8d-5449-b364-e50dd369d598

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

import Theorems.Thm_AutomorphicForm_exists_countable_orthonormal_flat_isInducedSection_family_complete_principalLevel_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation
import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat
import Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz
import Theorems.Thm_AutomorphicForm_exists_eisensteinTableOf_eq_table_of_isUnitaryChar_of_isUnramifiedCharAt
import Theorems.Thm_AutomorphicForm_isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
import Theorems.Thm_AutomorphicForm_exists_summable_dominant_rightConv_axis_family_maassSelberg_pairings_of_isUnitFactorization_sum_lipschitz
import Theorems.Thm_AutomorphicForm_exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn
import Theorems.Thm_AutomorphicForm_table_axis_mem_setOf_xiBox_of_isUnitaryChar_of_mul_mul_rpow_eq
import Theorems.Thm_AutomorphicForm_isInducedSection_mul_cpowChar_and_continuous_and_maximalCompactAway_of_isInducedSection_of_principalLevel
import Theorems.Thm_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt
import Theorems.Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_zero_eq_of_eq_of_flat
import Theorems.Thm_AutomorphicForm_exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial
import Theorems.Thm_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

namespace ContReduce

variable (K : Type) [Field K] [NumberField K]

theorem ideal_ne_bot_of_forall_dvd_mem (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) : N ≠ ⊥ := by
  classical
  intro hbot
  have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S := fun v => hN v (by rw [hbot]; exact dvd_zero _)
  have hMpos : 0 < ∏ v ∈ S, Ideal.absNorm v.asIdeal := by
    refine Finset.prod_pos fun v _ => Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (∏ v ∈ S, Ideal.absNorm v.asIdeal + 1)

  have hptop : Ideal.span {(p : 𝓞 K)} ≠ ⊤ := by
    intro htop
    have h1 : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = 1 := by rw [htop, Ideal.absNorm_top]
    rw [Ideal.absNorm_span_singleton] at h1
    have hn : Algebra.norm ℤ (p : 𝓞 K) = (p : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
      rw [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap]
    rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at h1
    have hr : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
    exact hp.one_lt.ne' (Nat.pow_eq_one.mp h1 |>.resolve_right hr.ne')
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hptop
  have h𝔪bot : 𝔪 ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hp.ne_zero (by exact_mod_cast hle)
  let v₀ : HeightOneSpectrum (𝓞 K) := ⟨𝔪, h𝔪.isPrime, h𝔪bot⟩

  have hpmem : (p : 𝓞 K) ∈ 𝔪 := hle (Ideal.mem_span_singleton_self _)
  have hdvd : (Ideal.absNorm 𝔪 : ℤ) ∣ (p : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
    have := Ideal.absNorm_dvd_norm_of_mem hpmem
    rwa [show (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap] at this
  have hdvd' : Ideal.absNorm 𝔪 ∣ p ^ Module.finrank ℤ (𝓞 K) := by
    rw [← Nat.cast_pow] at hdvd
    exact Int.natCast_dvd_natCast.mp hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp hdvd'
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk'
    exact h𝔪.ne_top hk'
  have hp_le : p ≤ Ideal.absNorm 𝔪 := by
    rw [hk']
    exact Nat.le_self_pow hk0 p

  have hdvM : Ideal.absNorm v₀.asIdeal ∣ ∏ v ∈ S, Ideal.absNorm v.asIdeal :=
    Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 K) => Ideal.absNorm v.asIdeal) (hall v₀)
  have hle' : Ideal.absNorm 𝔪 ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal := Nat.le_of_dvd hMpos hdvM
  omega

end ContReduce

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
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} ⊆ X)
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
        φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      ∃ (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            χ₂ z = 1) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          NumberField.TateGlobal.IsUnramifiedCharAt χ₁ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ v) ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          tabs n v = ((LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).a v,
            (LanglandsTunnell.Converse.eisensteinTableOf K M hM χ₁ χ₂).b v)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∃ Λ : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖Λ g‖ < ε) ∧
      ∃ s : C(X, ℂ) →L[ℂ] ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
        (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
        IsUnitFactorization K (SK ∪ T) f faK ff
          (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
            else fSK v) →
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
        IsArchBiFinite K tysK f →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).1 ^ ks v *
            ((HeckeEigensystem.cNorm v)⁻¹ *
              ((x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ) v).2) ^ js v) →
        (∀ᶠ R : ℝ in Filter.atTop, IntegrableOn (fun x =>
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y')) ∂νZK)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)))
            (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
        Filter.Tendsto (fun R : ℝ =>
          (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y')) ∂νZK)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x))
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
          (R : ℂ) * s g) Filter.atTop (nhds ((∑' n, cs n * g ⟨tabs n, htabs n⟩) + Λ g)) := by
  classical

  have hαm : ∀ x : (AdeleRing (𝓞 K) K)ˣ,
      0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ)) := by
    intro x
    exact NNReal.coe_pos.mpr distribHaarChar_pos

  obtain ⟨w, hξw⟩ := AutomorphicForm.exists_forall_norm_apply_eq_ideleNorm_rpow_of_continuous_of_trivial K ξK hξc hξt

  obtain ⟨ιE, _iC, μ, ν, _hμ, _hν, _hμic, _hνic, _hμc, _hνc, _hμν, _hdist, nE, φE, _hφE, _hφEK, _hφEf, _hφEjc, _hφEhol, _hφEKu, _hφEflat, _hφElev, _hφEty, _hφEon, _hφEspan, _hpairs, _hdiag, -⟩ :=
    AutomorphicForm.exists_countable_orthonormal_flat_isInducedSection_family_complete_principalLevel_archCutSubmodule K SK ξK hξc hξt N hN tysK w hξw hαm
  haveI := _iC

  choose OE EE NE hEE using fun (e : ιE) (j : Fin (nE e)) =>
    AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family K hαm
      (μ e) (ν e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e) (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j)
      (_hφEjc e j) (_hφEhol e j) (_hφEKu e j)

  obtain ⟨κ, hκ, HT⟩ := AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK w hξw hαm
  have HTW := HT ι b cls hb hbn hbo hbs hbc ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE hEE

  obtain ⟨c, hc, R₁, HC⟩ := AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat K α β hα hαβ ΦK hαm

  have hN0 : N ≠ ⊥ := ContReduce.ideal_ne_bot_of_forall_dvd_mem K N SK hN
  have HSA := AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_zero_eq_of_eq_of_flat K hαm

  have hX0 : X.Nonempty := by
    refine ⟨fun v => if v ∈ SK then 0 else ((0 : ℂ), HeckeEigensystem.cNorm v *
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)), hX ?_⟩
    refine ⟨fun v hv => by simp only [if_pos hv], fun v hv => ⟨?_, ?_, ?_⟩⟩
    · simp only [if_neg hv]
    · simp only [if_neg hv, norm_zero]; positivity
    · simp only [if_neg hv, map_zero, mul_zero]

  by_cases hTF : IsArchTestFactor K faK ∧ ∀ v ∈ SK, IsLocalTestFn K v (fSK v)
  swap
  · obtain ⟨x₀, hx₀⟩ := hX0
    refine ⟨fun _ => x₀, fun _ => hx₀, fun _ => 0, by simp, fun n hn => absurd rfl hn, ?_⟩
    intro T hTd hT2 ϖKs hirr hϖKs0 nKs rKs hcos zKs hzKs
    refine ⟨0, fun τ₀ ε hε => ⟨fun _ => Set.univ, fun v _ => ⟨isOpen_univ, Set.mem_univ _⟩,
      fun g _ _ => by simpa using hε⟩, 0, ?_⟩
    intro ks js f hf hfc ff hfact hbi harch g hg
    exfalso
    refine hTF ⟨hfact.1, fun v hv => ?_⟩
    have hvT : v ∉ T := fun hvT => Finset.disjoint_left.mp hTd hvT hv
    have h := hfact.2.2.1 v (Finset.mem_union_left T hv)
    simp only [if_neg hvT] at h
    exact h

  obtain ⟨f₀, ff₀, hf₀c, hf₀s, hf₀fact, hf₀T⟩ :=
    AutomorphicForm.exists_continuous_hasCompactSupport_isUnitFactorization_and_union_of_isArchTestFactor_of_isLocalTestFn
      K SK faK hTF.1 fSK hTF.2

  let μ' : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun e => μ e * cpowChar _ hαm (((w / 2 : ℝ) : ℂ))
  let ν' : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := fun e => ν e * cpowChar _ hαm (((w / 2 : ℝ) : ℂ))
  let A : ιE → HeightOneSpectrum (𝓞 K) → ℂ := fun e v => ((μ' e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)
  let B : ιE → HeightOneSpectrum (𝓞 K) → ℂ := fun e v => ((ν' e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)
  have hA : ∀ e v, A e v ≠ 0 := fun e v => Units.ne_zero _
  have hB : ∀ e v, B e v ≠ 0 := fun e v => Units.ne_zero _

  have hμ1 : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), ‖((μ e z : ℂˣ) : ℂ)‖ = 1 := fun e z => _hμ e z
  have hν1 : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), ‖((ν e z : ℂˣ) : ℂ)‖ = 1 := fun e z => _hν e z
  obtain ⟨M₀, hAM, hBM⟩ : ∃ M₀ : HeightOneSpectrum (𝓞 K) → ℝ, (∀ e v, ‖A e v‖ ≤ M₀ v) ∧ (∀ e v, ‖B e v‖ ≤ M₀ v) := by
    refine ⟨fun v => ‖((cpowChar _ hαm (((w / 2 : ℝ) : ℂ)) (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)‖,
      fun e v => ?_, fun e v => ?_⟩
    · simp only [A, μ', MonoidHom.mul_apply, Units.val_mul, norm_mul, hμ1, one_mul, le_refl]
    · simp only [B, ν', MonoidHom.mul_apply, Units.val_mul, norm_mul, hν1, one_mul, le_refl]
  let τ : ιE → ℝ → (HeightOneSpectrum (𝓞 K) → ℂ × ℂ) := fun e t v =>
    if v ∈ SK then 0 else
      ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
          (A e v * (HeckeEigensystem.cNorm v) ^ (-((t : ℂ) * Complex.I)) + B e v * (HeckeEigensystem.cNorm v) ^ ((t : ℂ) * Complex.I)),
        (HeckeEigensystem.cNorm v) * A e v * B e v)
  have hτ : ∀ (e : ιE) (t : ℝ) (v : HeightOneSpectrum (𝓞 K)), v ∉ SK →
      τ e t v = ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
          (A e v * (HeckeEigensystem.cNorm v) ^ (-((t : ℂ) * Complex.I)) + B e v * (HeckeEigensystem.cNorm v) ^ ((t : ℂ) * Complex.I)),
        (HeckeEigensystem.cNorm v) * A e v * B e v) := fun e t v hv => by simp only [τ, if_neg hv]
  have hτS : ∀ (e : ιE) (t : ℝ) (v : HeightOneSpectrum (𝓞 K)), v ∈ SK → τ e t v = 0 := fun e t v hv => by simp only [τ, if_pos hv]

  have hτX : ∀ e t, τ e t ∈ X := fun e t =>
    hX (AutomorphicForm.table_axis_mem_setOf_xiBox_of_isUnitaryChar_of_mul_mul_rpow_eq K SK ξK w hαm (μ e) (ν e) (_hμ e) (_hν e) (_hμν e) t)

  let vol : ℂ := (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)
  let P : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    ∫ k, φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
  let Q : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    ∫ k, (fun g => vol⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K) *
      conj ((fun g => vol⁻¹ * deriv (fun s : ℂ => NE e j s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
  let U : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    if μ e = ν e then
      ∫ k, φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
        conj ((fun g => vol⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
    else 0
  let V : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    if μ e = ν e then
      ∫ k, (fun g => vol⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K) *
        conj (φE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
    else 0

  have hPc : ∀ e i j t, P e i j t = P e i j 0 := by
    intro e i j t; simp only [P, _hφEflat]
  have hUV0 : ∀ e i j, U e i j 0 = V e i j 0 := by
    intro e i j
    have h0 : ((0:ℝ) : ℂ) * Complex.I = 0 := by simp
    by_cases h : μ e = ν e
    · simp only [U, V, if_pos h, h0]
      exact HSA (μ e) (ν e) h (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e)
        (φE e i) (_hφE e i) (_hφEK e i) (_hφEf e i) (_hφEjc e i) (_hφEhol e i) (_hφEKu e i) (_hφEflat e i)
        (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j) (_hφEflat e j)
        (OE e i) (EE e i) (NE e i) (hEE e i) (OE e j) (EE e j) (NE e j) (hEE e j)
    · simp only [U, V, if_neg h]

  let a : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
    ∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
      conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
  obtain ⟨hac, hQc, hUc, hVc, hai, haQ, haU, haV, L, hL, hL1, hL0, hLip⟩ :=
    AutomorphicForm.exists_summable_dominant_rightConv_axis_family_maassSelberg_pairings_of_isUnitFactorization_sum_lipschitz
      K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK faK fSK w hξw hαm
      ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat
      _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE hEE _hdiag f₀ hf₀c hf₀s ff₀ hf₀fact
  obtain ⟨tabs, htabs, cs, hsum, htabsat, HP⟩ :=
    AutomorphicForm.exists_atomic_forall_tendsto_tsum_integral_prod_pow_mul_affine_oscillatory_sub_mul_of_placewise_bound_of_sum_lipschitz K SK X hXc hX0 ιE nE A B hA hB M₀ hAM hBM τ hτ hτS hτX κ c P Q U V a hPc hQc hUc hVc hac hai haQ haU haV hUV0 L hL hL1 hL0 hLip
  refine ⟨tabs, htabs, cs, hsum, ?_, ?_⟩
  ·
    intro n hn
    obtain ⟨e, hne, htn⟩ := htabsat n hn
    have hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
        NumberField.TateGlobal.IsUnramifiedCharAt (μ e) v ∧ NumberField.TateGlobal.IsUnramifiedCharAt (ν e) v := by
      intro v hv
      have hvN : ¬ v.asIdeal ∣ N := fun h => hv (hN v h)
      have hφ0 : φE e ⟨0, hne⟩ 0 ≠ 0 := by
        intro h0
        have h1 := _hφEon e ⟨0, hne⟩ ⟨0, hne⟩
        rw [if_pos rfl, h0] at h1
        simp at h1
      exact AutomorphicForm.isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel K N hαm
        (μ e) (ν e) 0 (φE e ⟨0, hne⟩ 0) (_hφE e ⟨0, hne⟩ 0) hφ0 (_hφElev e ⟨0, hne⟩ 0) v hvN
    obtain ⟨M, hM, χ₁, χ₂, h1c, h1t, h2c, h2t, hur', htabM⟩ :=
      AutomorphicForm.exists_eisensteinTableOf_eq_table_of_isUnitaryChar_of_isUnramifiedCharAt K SK w hαm (μ e) (ν e)
        (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e) hur
    refine ⟨M, hM, χ₁, χ₂, h1c, h1t, h2c, h2t, hur', fun v hv => ?_⟩
    rw [htn, hτ e 0 v hv, ← htabM v hv]
    simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one]
    rfl
  intro T hTd hT2 ϖKs hirr hϖKs0 nKs rKs hcos zKs hzKs
  obtain ⟨Λ, hΛ, s, HPs⟩ := HP T hTd hT2
  refine ⟨Λ, hΛ, s, ?_⟩
  intro ks js f hf hfc ff hfact hbi harch g hg
  have HPg := HPs ks js g hg
  obtain ⟨R₀, HR⟩ := HTW f hf hfc ⟨faK, ff, hfact.1, hfact.2.1, hfact.2.2.2.2.2⟩ hbi harch
  refine ⟨Filter.eventually_atTop.2 ⟨R₀, fun R hR => (HR R hR).1⟩, ?_⟩
  have key := HPg (fun R : ℝ => ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y')) ∂νZK)
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' i : ι, convOp K f (b i) x * conj (b i y'))
                x) -
              (@AutomorphicForm.lambdaT _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
                (fun y' => ((νZK (ΩK ∩ {z | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Icc α β})).toReal : ℂ) / (((adelicGLHaar (Fin 2) (𝓞 K) K) (AutomorphicForm.canonicalTruncationDomain K α β)).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
                      SquaresToXi (𝓞 K) K ⊤ ξK χ ∧
                      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
                        z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                          χ z = 1) ∧
                      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    (∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) *
                      (chiDet (𝓞 K) K χ x * chiDet (𝓞 K) K χ⁻¹ y'))
                x)) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) (max R₀ R₁) (by

      intro R hR
      have hR₀ : R₀ ≤ R := le_trans (le_max_left _ _) hR
      have hR₁ : R₁ ≤ R := le_trans (le_max_right _ _) hR
      have hTSK : ∀ v ∈ T, v ∉ SK := fun v hv hvS => Finset.disjoint_left.mp hTd hv hvS
      obtain ⟨-, -, -, hEq⟩ := HR R hR₀
      beta_reduce
      rw [hEq]
      congr 1
      refine tsum_congr fun e => ?_
      refine integral_congr_ae ?_
      have hae : {t : ℝ | t ≠ 0} ∈ MeasureTheory.ae (volume : Measure ℝ) := by
        rw [MeasureTheory.mem_ae_iff]
        have hc0 : {t : ℝ | t ≠ 0}ᶜ = {0} := by
          ext t; simp
        rw [hc0]; exact measure_singleton 0
      filter_upwards [hae] with t ht
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_

      have hcj : Continuous (φE e j ((t : ℂ) * Complex.I)) :=
        (_hφEjc e j).comp (continuous_const.prodMk continuous_id)
      obtain ⟨hψ, hψc, hψsph⟩ :=
        AutomorphicForm.isInducedSection_mul_cpowChar_and_continuous_and_maximalCompactAway_of_isInducedSection_of_principalLevel
          K SK N hN w hαm (μ e) (ν e) ((t : ℂ) * Complex.I) (φE e j ((t : ℂ) * Complex.I)) (_hφE e j _) hcj (_hφElev e j _)

      have hunr : ∀ v ∈ T, NumberField.TateGlobal.IsUnramifiedCharAt (μ' e) v ∧ NumberField.TateGlobal.IsUnramifiedCharAt (ν' e) v := by
        intro v hv
        have hvN : ¬ v.asIdeal ∣ N := fun h => hTSK v hv (hN v h)
        have hφ0 : φE e i 0 ≠ 0 := by
          intro h0
          have h1 := _hφEon e i i
          rw [if_pos rfl, h0] at h1
          simp at h1
        have hu := AutomorphicForm.isUnramifiedCharAt_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel K N hαm
          (μ e) (ν e) 0 (φE e i 0) (_hφE e i 0) hφ0 (_hφElev e i 0) v hvN
        exact ⟨AutomorphicForm.isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt K hαm (μ e) _ v hu.1,
          AutomorphicForm.isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt K hαm (ν e) _ v hu.2⟩
      have h5 := AutomorphicForm.rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization
        K SK T hTd ϖKs hirr hϖKs0 nKs rKs hcos zKs hzKs faK fSK ks js f hf hfc ff hfact f₀ hf₀c hf₀s ff₀ (hf₀T T hTd)
        hαm (μ' e) (ν' e) hunr ((t : ℂ) * Complex.I) _ hψ hψc hψsph
      have hC := HC (μ e) (ν e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e)
        (φE e i) (_hφE e i) (_hφEK e i) (_hφEf e i) (_hφEjc e i) (_hφEhol e i) (_hφEKu e i) (_hφEflat e i)
        (φE e j) (_hφE e j) (_hφEK e j) (_hφEf e j) (_hφEjc e j) (_hφEhol e j) (_hφEKu e j) (_hφEflat e j)
        (OE e i) (EE e i) (NE e i) (hEE e i) (OE e j) (EE e j) (NE e j) (hEE e j) t ht R hR₁

      have hgτ : g ⟨τ e t, hτX e t⟩ = ∏ v ∈ T,
          ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
              (((μ' e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * (HeckeEigensystem.cNorm v) ^ (-((t : ℂ) * Complex.I)) +
                ((ν' e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * (HeckeEigensystem.cNorm v) ^ ((t : ℂ) * Complex.I))) ^ ks v *
            ((HeckeEigensystem.cNorm v)⁻¹ *
              ((HeckeEigensystem.cNorm v) * ((μ' e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
                ((ν' e (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ))) ^ js v := by
        rw [hg]
        refine Finset.prod_congr rfl fun v hv => ?_
        simp only [A, B, hτ e t v (hTSK v hv)]

      have hK : (∫ k, AutomorphicForm.rightConv K (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g *
                (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f (k : AdelicGL2 (𝓞 K) K) *
              conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
            = g ⟨τ e t, hτX e t⟩ * a e i j t := by
        rw [hgτ]
        simp only [a]
        rw [← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        beta_reduce
        rw [h5]
        ring
      rw [hK]
      rcases _hdiag e with hd | hd
      · rw [hC.2.1 hd]
        simp only [P, Q, U, V, vol, if_pos hd]
      · have hne : ¬ (μ e = ν e) := by
          rintro heq; obtain ⟨z, -, hz⟩ := hd; exact hz (by rw [heq])
        rw [hC.2.2 hd]
        simp only [P, Q, U, V, vol, if_neg hne]
        ring)
  exact key

end S_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul (solution)
