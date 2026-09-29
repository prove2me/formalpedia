-- Prove2me | solution 1 for AutomorphicForm.forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/72f00878-484b-50fb-b223-636ffe44c8c9

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Theorems.Thm_AutomorphicForm_exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact
import Theorems.Thm_AutomorphicForm_integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
import Theorems.Thm_AutomorphicForm_forall_mem_cuspClasses_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_le_of_isFundamentalDomain_of_pos
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one"
p2m_attr_erase "simp" "LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul"
p2m_attr_erase "simp" "RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ComplexConjugate ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace KerAssembly

variable {K : Type} [Field K] [NumberField K]

variable (K) in

abbrev slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

variable (K) in

abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

variable (K) in

abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

variable (K) in

abbrev pinsAt (D : Set (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K D (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

variable (K) in

abbrev Vcut (D : Set (AdelicGL2 (𝓞 K) K)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (tys : ArchTypeFamily K)
    (π : HeckeEigensystem K ℂ) : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
  isotypicCuspSubmodule K (pinsAt K D) ξ N S π ⊓ archCutSubmodule K tys

private scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
private scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

private theorem exists_heightOneSpectrum_comap_eq_span (p : ℕ) (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 K),
      Ideal.comap (algebraMap ℤ (𝓞 K)) P.asIdeal = Ideal.span {(p : ℤ)} := by
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp0).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, -, hQprime, hQcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K)) (Ideal.comap_bot_le_of_injective _ hinj)
  refine ⟨⟨Q, hQprime, fun hQ => ?_⟩, hQcomap⟩
  rw [hQ, Ideal.comap_bot_of_injective _ hinj] at hQcomap
  exact hp0 (Ideal.span_singleton_eq_bot.1 hQcomap.symm)

theorem ne_bot_of_forall_dvd_mem {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ N → p ∈ S) : N ≠ ⊥ := by
  rintro rfl
  have hall : ∀ p : HeightOneSpectrum (𝓞 K), p ∈ S := fun p =>
    hNS p (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
  choose P hP using fun q : {p : ℕ | Nat.Prime p} =>
    exists_heightOneSpectrum_comap_eq_span (K := K) q.1 q.2
  haveI : Infinite {p : ℕ | Nat.Prime p} := Set.infinite_coe_iff.2 Nat.infinite_setOf_prime
  refine not_injective_infinite_finite (fun q : {p : ℕ | Nat.Prime p} => (⟨P q, hall (P q)⟩ : S))
    fun q₁ q₂ h => ?_
  have h' : P q₁ = P q₂ := congrArg Subtype.val h
  have hspan : Ideal.span {((q₁ : ℕ) : ℤ)} = Ideal.span {((q₂ : ℕ) : ℤ)} := by
    rw [← hP q₁, ← hP q₂, h']
  have hq := Int.eq_of_associated_of_nonneg (Ideal.span_singleton_eq_span_singleton.1 hspan)
    (by positivity) (by positivity)
  exact Subtype.ext (by exact_mod_cast hq)

private theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

private theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

private theorem slab_measurable (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem slab_Γ_stable (α β : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K α β ↔ x ∈ slab K α β := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc α β ↔ x ∈ slab K α β
  rw [hγ₀, map_mul, ideleNorm_mul, ideleNorm_det_globalPoints, one_mul]
  exact Iff.rfl

private scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

private theorem smulInvariant_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K α β)) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ slab K α β =
      (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ slab K α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, slab_Γ_stable α β γ x]
  rw [hset, measure_preimage_mul]

private theorem countable_Γ : Countable (Γ K) := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Function.Injective.countable fun _ _ h => Units.ext h
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem setIntegral_eq_of_isFundamentalDomain_slab {α β : ℝ} {Φ Φ' : Set (AdelicGL2 (𝓞 K) K)}
    (hΦs : Φ ⊆ slab K α β) (hΦ's : Φ' ⊆ slab K α β)
    (hΦ : IsFundamentalDomain (Γ K) Φ ((μ K).restrict (slab K α β)))
    (hΦ' : IsFundamentalDomain (Γ K) Φ' ((μ K).restrict (slab K α β)))
    (F : AdelicGL2 (𝓞 K) K → ℂ)
    (hF : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K),
      F (globalPoints (𝓞 K) K γ * x) = F x) :
    ∫ x in Φ, F x ∂(μ K) = ∫ x in Φ', F x ∂(μ K) := by
  haveI : Countable (Γ K) := countable_Γ
  haveI := smulInvariant_restrict_slab (K := K) α β
  have hF' : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), F (γ • x) = F x := fun γ x => by
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Γ_smul, hγ₀, hF]
  calc ∫ x in Φ, F x ∂(μ K) = ∫ x in Φ, F x ∂((μ K).restrict (slab K α β)) := by
        rw [Measure.restrict_restrict_of_subset hΦs]
    _ = ∫ x in Φ', F x ∂((μ K).restrict (slab K α β)) := hΦ.setIntegral_eq hΦ' hF'
    _ = ∫ x in Φ', F x ∂(μ K) := by rw [Measure.restrict_restrict_of_subset hΦ's]

theorem eLpNorm_eq_of_isFundamentalDomain_slab {α β : ℝ} {Φ Φ' : Set (AdelicGL2 (𝓞 K) K)}
    (hΦs : Φ ⊆ slab K α β) (hΦ's : Φ' ⊆ slab K α β)
    (hΦ : IsFundamentalDomain (Γ K) Φ ((μ K).restrict (slab K α β)))
    (hΦ' : IsFundamentalDomain (Γ K) Φ' ((μ K).restrict (slab K α β)))
    (F : AdelicGL2 (𝓞 K) K → ℂ)
    (hF : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K),
      F (globalPoints (𝓞 K) K γ * x) = F x) :
    eLpNorm F 2 ((μ K).restrict Φ) = eLpNorm F 2 ((μ K).restrict Φ') := by
  haveI : Countable (Γ K) := countable_Γ
  haveI := smulInvariant_restrict_slab (K := K) α β
  have hF' : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), F (γ • x) = F x := fun γ x => by
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Γ_smul, hγ₀, hF]
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  calc ∫⁻ x in Φ, ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(μ K)
      = ∫⁻ x in Φ, ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂((μ K).restrict (slab K α β)) := by
        rw [Measure.restrict_restrict_of_subset hΦs]
    _ = ∫⁻ x in Φ', ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂((μ K).restrict (slab K α β)) :=
        hΦ.setLIntegral_eq hΦ' (fun x => ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal) (fun γ x => by rw [hF' γ x])
    _ = ∫⁻ x in Φ', ‖F x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(μ K) := by
        rw [Measure.restrict_restrict_of_subset hΦ's]

theorem memLp_of_isFundamentalDomain_slab {α β : ℝ} {Φ Φ' : Set (AdelicGL2 (𝓞 K) K)}
    (hΦs : Φ ⊆ slab K α β) (hΦ's : Φ' ⊆ slab K α β)
    (hΦ : IsFundamentalDomain (Γ K) Φ ((μ K).restrict (slab K α β)))
    (hΦ' : IsFundamentalDomain (Γ K) Φ' ((μ K).restrict (slab K α β)))
    (F : AdelicGL2 (𝓞 K) K → ℂ) (hc : Continuous F)
    (hF : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K),
      F (globalPoints (𝓞 K) K γ * x) = F x)
    (h : MemLp F 2 ((μ K).restrict Φ)) : MemLp F 2 ((μ K).restrict Φ') :=
  ⟨hc.aestronglyMeasurable, by
    rw [← eLpNorm_eq_of_isFundamentalDomain_slab hΦs hΦ's hΦ hΦ' F hF]; exact h.2⟩

section Members

variable {D : Set (AdelicGL2 (𝓞 K) K)} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
  {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))} {tys : ArchTypeFamily K}
  {π : HeckeEigensystem K ℂ}

private theorem lsXi_of_isIsotypicCuspFormAt {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : IsIsotypicCuspFormAt K (pinsAt K D) ξ N S π φ) :
    IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ MemLp φ 2 ((μ K).restrict D) := by
  have h1 : IsAutomorphicFnAt K (pinsAt K D) ξ φ := h.smoothCusp.1.1
  exact (lsXiMemberAt_iff (𝓞 K) K (μ K) ⊤ ξ D φ).1 h1

theorem continuous_of_mem_Vcut {b : AdelicGL2 (𝓞 K) K → ℂ} (hb : b ∈ Vcut K D ξ N S tys π) :
    Continuous b :=
  continuous_of_mem_isotypicCuspSubmodule hb.1

theorem isLsXiFunction_of_mem_Vcut {b : AdelicGL2 (𝓞 K) K → ℂ} (hb : b ∈ Vcut K D ξ N S tys π) :
    IsLsXiFunction (𝓞 K) K ⊤ ξ b := by
  refine Submodule.span_induction (p := fun φ _ => IsLsXiFunction (𝓞 K) K ⊤ ξ φ) ?_ ?_ ?_ ?_ hb.1
  · exact fun φ hφ => (lsXi_of_isIsotypicCuspFormAt hφ).1
  · exact isLsXiFunction_zero (𝓞 K) K ⊤ ξ
  · intro u w _ _ hu hw
    exact ⟨fun γ g => by simp only [Pi.add_apply, hu.left_invariant, hw.left_invariant],
      fun z g => by simp only [Pi.add_apply, hu.central_transform, hw.central_transform, mul_add]⟩
  · intro c u _ hu
    exact ⟨fun γ g => by simp only [Pi.smul_apply, hu.left_invariant],
      fun z g => by simp only [Pi.smul_apply, smul_eq_mul, hu.central_transform]; ring⟩

theorem memLp_two_of_mem_Vcut {b : AdelicGL2 (𝓞 K) K → ℂ} (hb : b ∈ Vcut K D ξ N S tys π) :
    MemLp b 2 ((μ K).restrict D) := by
  refine Submodule.span_induction (p := fun φ _ => MemLp φ 2 ((μ K).restrict D)) ?_ ?_ ?_ ?_ hb.1
  · exact fun φ hφ => (lsXi_of_isIsotypicCuspFormAt hφ).2
  · exact MemLp.zero'
  · exact fun u w _ _ hu hw => hu.add hw
  · exact fun c u _ hu => hu.const_smul c

theorem apply_globalPoints_mul_of_mem_Vcut {b : AdelicGL2 (𝓞 K) K → ℂ} (hb : b ∈ Vcut K D ξ N S tys π)
    (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K) :
    b (globalPoints (𝓞 K) K γ * g) = b g :=
  (isLsXiFunction_of_mem_Vcut hb).left_invariant γ g

theorem xi_continuous_and_trivial_of_exists_ne_zero {b : AdelicGL2 (𝓞 K) K → ℂ}
    (hb : b ∈ Vcut K D ξ N S tys π) (hb0 : b ≠ 0) :
    (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
    (∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1) := by
  have hne : ∃ g, b g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hb0 (funext h)
  obtain ⟨htriv, hcont⟩ :=
    AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous K ξ b
      (isLsXiFunction_of_mem_Vcut hb) (continuous_of_mem_Vcut hb) hne
  refine ⟨Units.continuous_val.comp hcont, fun z hz => ?_⟩
  obtain ⟨u, rfl⟩ := hz
  exact htriv u

end Members

theorem mul_conj_eq_cast_norm_sq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem mul_conj_eq_cast_norm_sq' (z : ℂ) : z * conj z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
  rw [mul_conj_eq_cast_norm_sq]; push_cast; rfl

section L2Facts

variable {ν : Measure (AdelicGL2 (𝓞 K) K)} {u v : AdelicGL2 (𝓞 K) K → ℂ}

theorem memLp_two_conj (hu : MemLp u 2 ν) : MemLp (fun g => conj (u g)) 2 ν :=
  hu.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => (RCLike.norm_conj (u x)).symm)

theorem integrable_mul_of_memLp_two (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) :
    Integrable (fun g => u g * v g) ν := by
  have ha' := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hb' := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  have hpt : ∀ x, ‖u x * v x‖ ≤ (‖u x‖ ^ 2 + ‖v x‖ ^ 2) / 2 := fun x => by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖u x‖ - ‖v x‖)]
  exact Integrable.mono' ((ha'.add hb').div_const 2) (hu.1.mul hv.1)
      (Filter.Eventually.of_forall fun x => hpt x)

theorem integral_norm_sq_eq_toReal_sq (hu : MemLp u 2 ν) :
    ∫ g, ‖u g‖ ^ 2 ∂ν = (eLpNorm u 2 ν).toReal ^ 2 := by
  have h := hu.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2] at h
  have hI : ∫ a, ‖u a‖ ^ (2:ℝ) ∂ν = ∫ g, ‖u g‖ ^ 2 ∂ν :=
    integral_congr_ae (Filter.Eventually.of_forall fun a => Real.rpow_two _)
  rw [hI] at h
  have hnn : 0 ≤ ∫ g, ‖u g‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  rw [h, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), ← Real.rpow_natCast,
    ← Real.rpow_mul hnn]
  norm_num

theorem toReal_eLpNorm_eq_sqrt (hu : MemLp u 2 ν) :
    (eLpNorm u 2 ν).toReal = Real.sqrt (∫ g, ‖u g‖ ^ 2 ∂ν) := by
  rw [integral_norm_sq_eq_toReal_sq hu, Real.sqrt_sq ENNReal.toReal_nonneg]

theorem integral_norm_mul_le (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) :
    ∫ g, ‖u g * v g‖ ∂ν ≤ (eLpNorm u 2 ν).toReal * (eLpNorm v 2 ν).toReal := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hu' : MemLp u (ENNReal.ofReal 2) ν := by rw [h2]; exact hu
  have hv' : MemLp v (ENNReal.ofReal 2) ν := by rw [h2]; exact hv
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := ν) Real.HolderConjugate.two_two hu' hv'
  simp_rw [norm_mul]
  refine h.trans (le_of_eq ?_)
  have e2 : ∀ w : AdelicGL2 (𝓞 K) K → ℂ, (∫ a, ‖w a‖ ^ (2:ℝ) ∂ν) = ∫ a, ‖w a‖ ^ 2 ∂ν := fun w =>
    integral_congr_ae (Filter.Eventually.of_forall fun a => Real.rpow_two _)
  rw [e2, e2, toReal_eLpNorm_eq_sqrt hu, toReal_eLpNorm_eq_sqrt hv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  try norm_num

end L2Facts

section Orthonormal

variable {ι : Type} (D : Set (AdelicGL2 (𝓞 K) K)) (b : ι → AdelicGL2 (𝓞 K) K → ℂ)

def IsOrthoOn : Prop :=
  (∀ i, ∫ g in D, b i g * conj (b i g) ∂(μ K) = 1) ∧
  (∀ i j, i ≠ j → ∫ g in D, b i g * conj (b j g) ∂(μ K) = 0)

variable {D b}

theorem norm_finsetSum_mul_le (s : Finset ι) (c : ι → ℂ) (x : AdelicGL2 (𝓞 K) K) :
    ‖∑ i ∈ s, c i * b i x‖ ≤ Real.sqrt (∑ i ∈ s, ‖c i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖b i x‖ ^ 2) :=
  calc ‖∑ i ∈ s, c i * b i x‖ ≤ ∑ i ∈ s, ‖c i‖ * ‖b i x‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_mul_le _ _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖c i‖) (fun i => ‖b i x‖)

theorem integral_normSq_finsetSum (hO : IsOrthoOn D b) (hL2 : ∀ i, MemLp (b i) 2 ((μ K).restrict D))
    (s : Finset ι) (c : ι → ℂ) :
    ∫ g in D, ‖∑ i ∈ s, c i * b i g‖ ^ 2 ∂(μ K) = ∑ i ∈ s, ‖c i‖ ^ 2 := by
  classical
  have hint : ∀ i j, Integrable (fun g => b i g * conj (b j g)) ((μ K).restrict D) := fun i j =>
    integrable_mul_of_memLp_two (hL2 i) (memLp_two_conj (hL2 j))
  have hC : (∫ g in D, (∑ i ∈ s, c i * b i g) * conj (∑ j ∈ s, c j * b j g) ∂(μ K)) =
      ∑ i ∈ s, c i * conj (c i) := by
    have hexp : ∀ g, (∑ i ∈ s, c i * b i g) * conj (∑ j ∈ s, c j * b j g)
        = ∑ i ∈ s, ∑ j ∈ s, (c i * conj (c j)) * (b i g * conj (b j g)) := fun g => by
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]; ring
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hint i j).const_mul _))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
    rw [Finset.sum_eq_single_of_mem i hi (fun j _ hji => ?_)]
    · rw [integral_const_mul, hO.1 i, mul_one]
    · rw [integral_const_mul, hO.2 i j (Ne.symm hji), mul_zero]
  have hpt : ∀ g, (((‖∑ i ∈ s, c i * b i g‖ ^ 2 : ℝ)) : ℂ) =
      (∑ i ∈ s, c i * b i g) * conj (∑ j ∈ s, c j * b j g) := fun g => (mul_conj_eq_cast_norm_sq _).symm
  have hR : ((∫ g in D, ‖∑ i ∈ s, c i * b i g‖ ^ 2 ∂(μ K) : ℝ) : ℂ) = ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hpt]
    rw [hC]; push_cast
    exact Finset.sum_congr rfl fun i _ => mul_conj_eq_cast_norm_sq' (c i)
  exact_mod_cast hR

theorem memLp_combo (hL2 : ∀ i, MemLp (b i) 2 ((μ K).restrict D)) (s : Finset ι) (c : ι → ℂ) :
    MemLp (fun g => ∑ i ∈ s, c i * b i g) 2 ((μ K).restrict D) :=
  memLp_finsetSum s (fun i _ => (hL2 i).const_mul (c i))

theorem eLpNorm_finsetSum_toReal (hO : IsOrthoOn D b) (hL2 : ∀ i, MemLp (b i) 2 ((μ K).restrict D))
    (s : Finset ι) (c : ι → ℂ) :
    (eLpNorm (fun g => ∑ i ∈ s, c i * b i g) 2 ((μ K).restrict D)).toReal = Real.sqrt (∑ i ∈ s, ‖c i‖ ^ 2) := by
  rw [toReal_eLpNorm_eq_sqrt (memLp_combo hL2 s c), integral_normSq_finsetSum hO hL2 s c]

theorem linearIndependent_of_isOrthoOn (hO : IsOrthoOn D b) (hL2 : ∀ i, MemLp (b i) 2 ((μ K).restrict D)) :
    LinearIndependent ℂ b := by
  classical
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h0 : ∑ j ∈ s, ‖c j‖ ^ 2 = 0 := by
    rw [← integral_normSq_finsetSum hO hL2 s c]
    have : ∀ g, ∑ j ∈ s, c j * b j g = 0 := fun g => by
      have := congrFun hs g
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    simp [this]
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h0 i hi
  exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this)

theorem injective_of_isOrthoOn (hO : IsOrthoOn D b) : Function.Injective b := fun i j hij => by
  by_contra hne
  have h0 := hO.2 i j hne
  rw [← hij, hO.1 i] at h0
  exact one_ne_zero h0

theorem exists_coeff_of_mem_span (s : Finset ι) {w : AdelicGL2 (𝓞 K) K → ℂ}
    (hw : w ∈ Submodule.span ℂ (b '' (↑s : Set ι))) :
    ∃ c : ι → ℂ, w = fun g => ∑ j ∈ s, c j * b j g := by
  classical
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun ℂ).1 hw
  refine ⟨fun j => if h : j ∈ s then c ⟨j, h⟩ else 0, ?_⟩
  ext g
  rw [← hc]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ι) ∈ s := by exact_mod_cast j.2
  rw [dif_pos hj]

theorem sqrt_sum_normSq_apply_le (hO : IsOrthoOn D b) (hL2 : ∀ i, MemLp (b i) 2 ((μ K).restrict D))
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) (s : Finset ι) (hbV : ∀ i ∈ s, b i ∈ V)
    (x : AdelicGL2 (𝓞 K) K) (B : ℝ) (hB : 0 ≤ B)
    (hsup : ∀ v ∈ V, ‖v x‖ ≤ B * (eLpNorm v 2 ((μ K).restrict D)).toReal) :
    Real.sqrt (∑ i ∈ s, ‖b i x‖ ^ 2) ≤ B := by
  set c : ι → ℂ := fun i => conj (b i x)
  set Kx : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ i ∈ s, c i * b i g
  have hKmem : Kx ∈ V := by
    have : Kx = ∑ i ∈ s, c i • b i := by
      ext g; simp only [Kx, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact V.sum_mem fun i hi => V.smul_mem _ (hbV i hi)
  have hc : ∀ i, ‖c i‖ ^ 2 = ‖b i x‖ ^ 2 := fun i => by simp [c]
  have hnorm : (eLpNorm Kx 2 ((μ K).restrict D)).toReal = Real.sqrt (∑ i ∈ s, ‖b i x‖ ^ 2) := by
    rw [show Kx = fun g => ∑ i ∈ s, c i * b i g from rfl, eLpNorm_finsetSum_toReal hO hL2 s c]
    simp_rw [hc]
  have hval : ‖Kx x‖ = ∑ i ∈ s, ‖b i x‖ ^ 2 := by
    have : Kx x = ((∑ i ∈ s, ‖b i x‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Kx, c]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; exact mul_conj_eq_cast_norm_sq' _
    rw [this, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
  have key := hsup Kx hKmem
  rw [hval, hnorm] at key

  set k := Real.sqrt (∑ i ∈ s, ‖b i x‖ ^ 2) with hk
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hsq : k ^ 2 = ∑ i ∈ s, ‖b i x‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  rw [← hsq] at key
  by_cases hk' : k = 0
  · rw [hk']; exact hB
  · have hkpos : 0 < k := lt_of_le_of_ne hk0 (Ne.symm hk')
    nlinarith

end Orthonormal

section PerClass

variable {ι : Type} {D : Set (AdelicGL2 (𝓞 K) K)} {b : ι → AdelicGL2 (𝓞 K) K → ℂ}

theorem sum_norm_apply_mul_le (hO : IsOrthoOn D b) (hL2 : ∀ i, MemLp (b i) 2 ((μ K).restrict D))
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) (s : Finset ι) (hbV : ∀ i ∈ s, b i ∈ V)
    (T : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hT : ∀ i ∈ s, T (b i) ∈ Submodule.span ℂ (b '' ↑s))
    (x y : AdelicGL2 (𝓞 K) K) (B : ℝ) (hB : 0 ≤ B)
    (hx : ∀ v ∈ V, ‖v x‖ ≤ B * (eLpNorm v 2 ((μ K).restrict D)).toReal)
    (hy : ∀ v ∈ V, ‖v y‖ ≤ B * (eLpNorm v 2 ((μ K).restrict D)).toReal) :
    ∑ i ∈ s, ‖T (b i) x * conj (b i y)‖ ≤
      B ^ 2 * Real.sqrt (∑ i ∈ s, (eLpNorm (T (b i)) 2 ((μ K).restrict D)).toReal ^ 2) := by
  classical

  have hc : ∀ i ∈ s, ∃ c : ι → ℂ, T (b i) = fun g => ∑ j ∈ s, c j * b j g :=
    fun i hi => exists_coeff_of_mem_span s (hT i hi)
  choose! c hc using hc
  set A : ι → ℝ := fun i => (eLpNorm (T (b i)) 2 ((μ K).restrict D)).toReal
  have hA : ∀ i ∈ s, A i = Real.sqrt (∑ j ∈ s, ‖c i j‖ ^ 2) := fun i hi => by
    simp only [A]; rw [hc i hi]; exact eLpNorm_finsetSum_toReal hO hL2 s (c i)
  have kx := sqrt_sum_normSq_apply_le hO hL2 V s hbV x B hB hx
  have ky := sqrt_sum_normSq_apply_le hO hL2 V s hbV y B hB hy

  have h1 : ∀ i ∈ s, ‖T (b i) x‖ ≤ A i * B := fun i hi => by
    rw [hA i hi, hc i hi]
    exact (norm_finsetSum_mul_le s (c i) x).trans
      (mul_le_mul_of_nonneg_left kx (Real.sqrt_nonneg _))
  calc ∑ i ∈ s, ‖T (b i) x * conj (b i y)‖ = ∑ i ∈ s, ‖T (b i) x‖ * ‖b i y‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_; rw [norm_mul, RCLike.norm_conj]
    _ ≤ ∑ i ∈ s, (A i * B) * ‖b i y‖ :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (h1 i hi) (norm_nonneg _)
    _ = B * ∑ i ∈ s, A i * ‖b i y‖ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ B * (Real.sqrt (∑ i ∈ s, A i ^ 2) * Real.sqrt (∑ i ∈ s, ‖b i y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt s A (fun i => ‖b i y‖)) hB
    _ ≤ B * (Real.sqrt (∑ i ∈ s, A i ^ 2) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ky (Real.sqrt_nonneg _)) hB
    _ = B ^ 2 * Real.sqrt (∑ i ∈ s, A i ^ 2) := by ring

theorem sum_integral_norm_mul_le (hO : IsOrthoOn D b) (hL2 : ∀ i, MemLp (b i) 2 ((μ K).restrict D))
    (s : Finset ι) (T : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hTL2 : ∀ i ∈ s, MemLp (T (b i)) 2 ((μ K).restrict D)) :
    ∑ i ∈ s, ∫ x in D, ‖T (b i) x * conj (b i x)‖ ∂(μ K) ≤
      Real.sqrt (s.card : ℝ) * Real.sqrt (∑ i ∈ s, (eLpNorm (T (b i)) 2 ((μ K).restrict D)).toReal ^ 2) := by
  set A : ι → ℝ := fun i => (eLpNorm (T (b i)) 2 ((μ K).restrict D)).toReal
  have hb1 : ∀ i, (eLpNorm (fun g => conj (b i g)) 2 ((μ K).restrict D)).toReal = 1 := fun i => by
    rw [toReal_eLpNorm_eq_sqrt (memLp_two_conj (hL2 i))]
    have : ∫ g, ‖conj (b i g)‖ ^ 2 ∂((μ K).restrict D) = 1 := by
      have h := integral_normSq_finsetSum hO hL2 {i} (fun _ => 1)
      simp only [Finset.sum_singleton, one_mul, norm_one, one_pow] at h
      simp_rw [RCLike.norm_conj]; exact h
    rw [this, Real.sqrt_one]
  have h1 : ∀ i ∈ s, ∫ x in D, ‖T (b i) x * conj (b i x)‖ ∂(μ K) ≤ A i := fun i hi => by
    have := integral_norm_mul_le (hTL2 i hi) (memLp_two_conj (hL2 i))
    rwa [hb1 i, mul_one] at this
  calc ∑ i ∈ s, ∫ x in D, ‖T (b i) x * conj (b i x)‖ ∂(μ K) ≤ ∑ i ∈ s, 1 * A i :=
        Finset.sum_le_sum fun i hi => by rw [one_mul]; exact h1 i hi
    _ ≤ Real.sqrt (∑ i ∈ s, (1:ℝ) ^ 2) * Real.sqrt (∑ i ∈ s, A i ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s (fun _ => (1:ℝ)) A
    _ = Real.sqrt (s.card : ℝ) * Real.sqrt (∑ i ∈ s, A i ^ 2) := by simp

end PerClass

theorem summable_and_tsum_le_of_sum_le {ι : Type} {g : ι → ℝ} {M : ℝ} (hg : ∀ i, 0 ≤ g i)
    (h : ∀ F : Finset ι, ∑ i ∈ F, g i ≤ M) : Summable g ∧ ∑' i, g i ≤ M :=
  ⟨summable_of_sum_le hg h, Real.tsum_le_of_sum_le hg h⟩

section Alias

variable {D : Set (AdelicGL2 (𝓞 K) K)} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
  {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))} {tys : ArchTypeFamily K}

open Classical in

def nrm (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ) :
    HeckeEigensystem K ℂ where
  level := N
  level_ne_bot := hN
  a := fun v => if v ∈ S then 0 else π.a v
  b := fun v => if v ∈ S then 0 else π.b v

theorem isIsotypicCuspFormAt_nrm_iff (hN : N ≠ ⊥) (π : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    IsIsotypicCuspFormAt K (pinsAt K D) ξ N S (nrm N hN S π) φ ↔ IsIsotypicCuspFormAt K (pinsAt K D) ξ N S π φ := by
  constructor
  · intro h
    refine ⟨h.smoothCusp, h.continuous, h.level_invariant, fun v hv => ?_, fun v hv g => ?_⟩
    · have := h.hecke_eigen v hv
      simpa only [nrm, if_neg hv] using this
    · have := h.central_eigen v hv g
      simpa only [HeckeEigensystem.toRawCentral_b, nrm, if_neg hv] using this
  · intro h
    refine ⟨h.smoothCusp, h.continuous, h.level_invariant, fun v hv => ?_, fun v hv g => ?_⟩
    · have := h.hecke_eigen v hv
      simpa only [nrm, if_neg hv] using this
    · have := h.central_eigen v hv g
      simpa only [HeckeEigensystem.toRawCentral_b, nrm, if_neg hv] using this

theorem Vcut_nrm (hN : N ≠ ⊥) (π : HeckeEigensystem K ℂ) :
    Vcut K D ξ N S tys (nrm N hN S π) = Vcut K D ξ N S tys π := by
  have : isotypicCuspSubmodule K (pinsAt K D) ξ N S (nrm N hN S π) = isotypicCuspSubmodule K (pinsAt K D) ξ N S π := by
    show Submodule.span ℂ _ = Submodule.span ℂ _
    congr 1
    ext φ
    exact isIsotypicCuspFormAt_nrm_iff hN π φ
  show isotypicCuspSubmodule K (pinsAt K D) ξ N S (nrm N hN S π) ⊓ _ = _
  rw [this]

theorem nrm_mem_cuspClasses (hN : N ≠ ⊥) (π : HeckeEigensystem K ℂ) (hne : Vcut K D ξ N S tys π ≠ ⊥) :
    nrm N hN S π ∈ cuspClasses K (pinsAt K D) ξ N S := by
  refine ⟨rfl, fun v hv => ⟨by simp [nrm, hv], by simp [nrm, hv]⟩, ?_⟩
  intro h0
  apply hne
  rw [← Vcut_nrm hN π]
  show isotypicCuspSubmodule K (pinsAt K D) ξ N S (nrm N hN S π) ⊓ archCutSubmodule K tys = ⊥
  rw [h0, bot_inf_eq]

end Alias

end KerAssembly
p2m_reactivate "P2MW.S_AutomorphicForm_forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.KerAssembly"

open KerAssembly in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (tys : ArchTypeFamily K)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S ∧
      b i ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S (cls i) ⊓ archCutSubmodule K tys)
    (hb₁ : ∀ i, ∫ g in Φ, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in Φ, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0)
    (hbs : ∀ π ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hff : IsFactorizableTestFn K f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (hft : IsArchBiFinite K tys f) :
    (∀ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ∀ y ∈ C,
        Summable (fun i => ‖convOp K f (b i) x * conj (b i y)‖) ∧
        ∑' i, ‖convOp K f (b i) x * conj (b i y)‖ ≤ M) ∧
    (∀ i, IntegrableOn (fun x => convOp K f (b i) x * conj (b i x)) Φ
        (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    Summable (fun π : HeckeEigensystem K ℂ =>
      ∫ x in Φ, ‖∑ᶠ i : {i // cls i = π}, convOp K f (b i) x * conj (b i x)‖
        ∂adelicGLHaar (Fin 2) (𝓞 K) K) := by
  classical

  have hD :=
    AutomorphicForm.integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
      K α β hα hαβ Φ hΦs hΦ ξ S N hN tys ι b cls hb hb₁ hb₀ hbs f hf hfc hff hfU hft

  have hN0 : N ≠ ⊥ := KerAssembly.ne_bot_of_forall_dvd_mem hN
  obtain ⟨-, -, -, hΦ₀s, hΦ₀⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  set Φ₀ : Set (AdelicGL2 (𝓞 K) K) := AutomorphicForm.canonicalTruncationDomain K α β with hΦ₀def
  set T : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) := convOp K f with hTdef
  set V : HeckeEigensystem K ℂ → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := fun π => Vcut K Φ ξ N S tys π
    with hVdef
  set V₀ : HeckeEigensystem K ℂ → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := fun π => Vcut K Φ₀ ξ N S tys π
    with hV₀def
  have hbV : ∀ i, b i ∈ V (cls i) := fun i => (hb i).2

  obtain ⟨Tw, cw, hcw, uw, hTcu⟩ :=
    AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  have hcov := hTcu 1 2 two_pos one_le_two
  have hVle : ∀ π, V π ≤ V₀ π := fun π =>
    (AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_le_of_isFundamentalDomain_of_pos
      K α β hα hαβ Φ hΦ ξ N hN0 S tys π cw uw 1 2 Tw hcw one_pos).trans
    (inf_le_inf_right _
      (AutomorphicForm.isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
        K cw uw 1 2 Tw one_lt_two hcov α β hα Φ₀ hΦ₀s hΦ₀ _ _ _ ξ N S π))
  have hbV₀ : ∀ i, b i ∈ V₀ (cls i) := fun i => hVle _ (hbV i)
  have hbne : ∀ i, b i ≠ 0 := fun i h => by
    have := hb₁ i
    rw [h] at this
    simp at this
  have hcls₀ : ∀ i, cls i ∈ cuspClasses K (pinsAt K Φ₀) ξ N S := fun i =>
    ⟨(hb i).1.1, (hb i).1.2.1, fun h0 => hbne i (by
      have := (Submodule.mem_inf.1 (hbV₀ i)).1
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).1 this)⟩

  have hTV : ∀ π, ∀ u ∈ V π, T u ∈ V π := fun π u hu =>
    AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
      K α β hα hαβ Φ hΦs hΦ ξ S N hN tys π f hf hfc hfU hft u hu

  have hcont : ∀ {π u}, u ∈ V π → Continuous u := fun hu => continuous_of_mem_Vcut hu
  have hinv : ∀ {π u}, u ∈ V π → ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) x,
      u (globalPoints (𝓞 K) K γ * x) = u x := fun hu => apply_globalPoints_mul_of_mem_Vcut hu
  have hL2Φ : ∀ {π u}, u ∈ V π → MemLp u 2 ((μ K).restrict Φ) := fun hu => memLp_two_of_mem_Vcut hu
  have hcont₀ : ∀ {π u}, u ∈ V₀ π → Continuous u := fun hu => continuous_of_mem_Vcut hu
  have hinv₀ : ∀ {π u}, u ∈ V₀ π → ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) x,
      u (globalPoints (𝓞 K) K γ * x) = u x := fun hu => apply_globalPoints_mul_of_mem_Vcut hu
  have hL2Φ₀ : ∀ {π u}, u ∈ V₀ π → MemLp u 2 ((μ K).restrict Φ₀) := fun hu => memLp_two_of_mem_Vcut hu

  have hnorm_eq : ∀ {π u}, u ∈ V₀ π →
      eLpNorm u 2 ((μ K).restrict Φ₀) = eLpNorm u 2 ((μ K).restrict Φ) := fun hu =>
    eLpNorm_eq_of_isFundamentalDomain_slab hΦ₀s hΦs hΦ₀ hΦ _ (hinv₀ hu)
  have hortho : IsOrthoOn Φ b := ⟨hb₁, hb₀⟩
  have hortho₀ : IsOrthoOn Φ₀ b := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [← hb₁ i]
      exact (setIntegral_eq_of_isFundamentalDomain_slab hΦs hΦ₀s hΦ hΦ₀ _ (fun γ x => by
        rw [hinv (hbV i)])).symm
    · rw [← hb₀ i j hij]
      exact (setIntegral_eq_of_isFundamentalDomain_slab hΦs hΦ₀s hΦ hΦ₀ _ (fun γ x => by
        rw [hinv (hbV i), hinv (hbV j)])).symm
  have hL2b : ∀ i, MemLp (b i) 2 ((μ K).restrict Φ) := fun i => hL2Φ (hbV i)
  have hL2b₀ : ∀ i, MemLp (b i) 2 ((μ K).restrict Φ₀) := fun i => hL2Φ₀ (hbV₀ i)

  have hfin : ∀ π : HeckeEigensystem K ℂ, {i | cls i = π}.Finite := fun π => by
    by_cases hπ : π ∈ cuspClasses K (pinsAt K Φ) ξ N S
    · exact (hbs π hπ).1
    · convert Set.finite_empty
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro rfl
      exact hπ (hb i).1
  set fib : HeckeEigensystem K ℂ → Finset ι := fun π => (hfin π).toFinset with hfibdef
  have mem_fib : ∀ {π i}, i ∈ fib π ↔ cls i = π := fun {π i} => by
    simp only [hfibdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have coe_fib : ∀ π, (↑(fib π) : Set ι) = {i | cls i = π} := fun π => (hfin π).coe_toFinset
  have hspan : ∀ π, (∃ i, cls i = π) → Submodule.span ℂ (b '' ↑(fib π)) = V π := fun π ⟨i, hi⟩ => by
    rw [coe_fib]
    exact (hbs π (hi ▸ (hb i).1)).2

  by_cases hι : IsEmpty ι
  · refine ⟨fun C hC => ⟨0, fun x _ y _ => ?_⟩, fun i => (IsEmpty.false i).elim, hD.2⟩
    exact KerAssembly.summable_and_tsum_le_of_sum_le (fun i => norm_nonneg _)
      (fun F => by rw [Finset.eq_empty_of_isEmpty F, Finset.sum_empty])
  rw [not_isEmpty_iff] at hι
  obtain ⟨i₀⟩ := hι

  obtain ⟨hξc, hξt⟩ := xi_continuous_and_trivial_of_exists_ne_zero (hbV i₀) (hbne i₀)

  have hE : ∀ π : HeckeEigensystem K ℂ,
      (∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ lam : ℂ,
          ∀ b' ∈ V₀ π, IsArchSmoothAt hw b' ∧ archCasimirAt hw b' = lam • b') ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), ∃ lam lam' : ℂ,
          ∀ b' ∈ V₀ π, IsArchSmoothAtComplex hw b' ∧ archCasimirAtComplex hw b' = lam • b' ∧
              archCasimirBarAtComplex hw b' = lam' • b') := by
    intro π
    by_cases hne : V₀ π = ⊥
    · refine ⟨fun w hw => ⟨0, fun b' hb' => ?_⟩, fun w hw => ⟨0, 0, fun b' hb' => ?_⟩⟩
      · rw [hne, Submodule.mem_bot] at hb'; subst hb'
        exact ⟨isArchSmoothAt_const hw 0, by rw [zero_smul]; exact archCasimirAt_const hw 0⟩
      · rw [hne, Submodule.mem_bot] at hb'; subst hb'
        exact ⟨isArchSmoothAtComplex_const hw 0, by rw [zero_smul]; exact archCasimirAtComplex_const hw 0,
          by rw [zero_smul]; exact archCasimirBarAtComplex_const hw 0⟩
    · have hmem := nrm_mem_cuspClasses (D := Φ₀) (ξ := ξ) (tys := tys) hN0 π hne
      have hE0 := AutomorphicForm.forall_mem_cuspClasses_exists_forall_isArchSmoothAt_and_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
        K α β hα hαβ ξ hξc hξt S N hN tys (nrm N hN0 S π) hmem
      have tr : ∀ {b'}, b' ∈ V₀ π → b' ∈ Vcut K Φ₀ ξ N S tys (nrm N hN0 S π) := fun hb' => by
        rw [Vcut_nrm hN0 π]; exact hb'
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · obtain ⟨lam, h⟩ := hE0.1 w hw
        exact ⟨lam, fun b' hb' => h b' (tr hb')⟩
      · obtain ⟨lam, lam', h⟩ := hE0.2 w hw
        exact ⟨lam, lam', fun b' hb' => h b' (tr hb')⟩
  choose lamR₀ hlamR₀ using fun π => (hE π).1
  choose lamC₀ lamC₀' hlamC₀ using fun π => (hE π).2
  set lamR : HeckeEigensystem K ℂ → InfinitePlace K → ℂ :=
    fun π w => if hw : w.IsReal then lamR₀ π w hw else 0 with hlamRdef
  set lamC : HeckeEigensystem K ℂ → InfinitePlace K → ℂ :=
    fun π w => if hw : w.IsComplex then lamC₀ π w hw else 0 with hlamCdef
  set lamC' : HeckeEigensystem K ℂ → InfinitePlace K → ℂ :=
    fun π w => if hw : w.IsComplex then lamC₀' π w hw else 0 with hlamC'def
  set Λ : HeckeEigensystem K ℂ → ℝ :=
    fun π => 1 + ∑ w : InfinitePlace K, (‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖) with hΛdef
  have hΛ1 : ∀ π, 1 ≤ Λ π := fun π =>
    le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => by positivity)
  have hΛpos : ∀ π, 0 < Λ π := fun π => lt_of_lt_of_le one_pos (hΛ1 π)
  have hlamR_le : ∀ π w, ‖lamR π w‖ ≤ Λ π := fun π w => by
    have h1 : ‖lamR π w‖ ≤ ‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖ := by
      have := norm_nonneg (lamC π w); have := norm_nonneg (lamC' π w); linarith
    have h2 : ‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖ ≤
        ∑ w : InfinitePlace K, (‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖) :=
      Finset.single_le_sum (f := fun w => ‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖)
        (fun w _ => by positivity) (Finset.mem_univ w)
    simp only [hΛdef]; linarith
  have hlamC_le : ∀ π w, ‖lamC π w‖ ≤ Λ π ∧ ‖lamC' π w‖ ≤ Λ π := fun π w => by
    have h2 : ‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖ ≤
        ∑ w : InfinitePlace K, (‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖) :=
      Finset.single_le_sum (f := fun w => ‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖)
        (fun w _ => by positivity) (Finset.mem_univ w)
    have := norm_nonneg (lamR π w); have := norm_nonneg (lamC π w); have := norm_nonneg (lamC' π w)
    simp only [hΛdef]; constructor <;> linarith

  have hRdata : ∀ π (w : InfinitePlace K) (hw : w.IsReal),
      ∀ b' ∈ V₀ π, IsArchSmoothAt hw b' ∧ archCasimirAt hw b' = lamR π w • b' := fun π w hw b' hb' => by
    have := hlamR₀ π w hw b' hb'
    simp only [hlamRdef, dif_pos hw]; exact this
  have hCdata : ∀ π (w : InfinitePlace K) (hw : w.IsComplex),
      ∀ b' ∈ V₀ π, IsArchSmoothAtComplex hw b' ∧ archCasimirAtComplex hw b' = lamC π w • b' ∧
        archCasimirBarAtComplex hw b' = lamC' π w • b' := fun π w hw b' hb' => by
    have := hlamC₀ π w hw b' hb'
    simp only [hlamCdef, hlamC'def, dif_pos hw]; exact this
  have hSUPhypR : ∀ π, ∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ lam : ℂ, ‖lam‖ ≤ Λ π ∧
      ∀ b' ∈ V₀ π, IsArchSmoothAt hw b' ∧ archCasimirAt hw b' = lam • b' :=
    fun π w hw => ⟨lamR π w, hlamR_le π w, hRdata π w hw⟩
  have hSUPhypC : ∀ π, ∀ (w : InfinitePlace K) (hw : w.IsComplex), ∃ lam lam' : ℂ,
      ‖lam‖ ≤ Λ π ∧ ‖lam'‖ ≤ Λ π ∧
      ∀ b' ∈ V₀ π, IsArchSmoothAtComplex hw b' ∧ archCasimirAtComplex hw b' = lam • b' ∧
        archCasimirBarAtComplex hw b' = lam' • b' :=
    fun π w hw => ⟨lamC π w, lamC' π w, (hlamC_le π w).1, (hlamC_le π w).2, hCdata π w hw⟩
  have hHShypR : ∀ (π : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsReal),
      lamC π w = 0 ∧ lamC' π w = 0 ∧
      ∀ b' ∈ V₀ π, IsArchSmoothAt hw b' ∧ archCasimirAt hw b' = lamR π w • b' := fun π w hw => by
    have hnc : ¬ w.IsComplex := InfinitePlace.not_isComplex_iff_isReal.2 hw
    exact ⟨by simp only [hlamCdef, dif_neg hnc], by simp only [hlamC'def, dif_neg hnc], hRdata π w hw⟩
  have hHShypC : ∀ (π : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsComplex),
      lamR π w = 0 ∧
      ∀ b' ∈ V₀ π, IsArchSmoothAtComplex hw b' ∧ archCasimirAtComplex hw b' = lamC π w • b' ∧
        archCasimirBarAtComplex hw b' = lamC' π w • b' := fun π w hw => by
    have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
    exact ⟨by simp only [hlamRdef, dif_neg hnr], hCdata π w hw⟩

  have hHS : ∀ s : ℝ, 0 ≤ s → ∃ M : ℝ, ∀ F : Finset ι,
      ∑ π ∈ F.image cls, Λ π ^ s *
        Real.sqrt (∑ i ∈ F.filter (fun i => cls i = π), (eLpNorm (T (b i)) 2 ((μ K).restrict Φ₀)).toReal ^ 2) ≤ M := by
    intro s hs
    obtain ⟨M, hM⟩ :=
      AutomorphicForm.exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
        K α β hα hαβ ξ hξc hξt S N hN tys f hf hfc hff hfU s hs
    refine ⟨M, fun F => ?_⟩
    have := hM ι b cls (fun i => ⟨hcls₀ i, hbV₀ i⟩) hortho₀.1 hortho₀.2 lamR lamC lamC' hHShypR hHShypC F
    simpa only [hΛdef, hTdef] using this

  have fib_sub : ∀ (F : Finset ι), F ⊆ (F.image cls).biUnion fib := fun F i hi =>
    Finset.mem_biUnion.2 ⟨cls i, Finset.mem_image_of_mem _ hi, mem_fib.2 rfl⟩
  have image_biUnion : ∀ (F : Finset ι), ((F.image cls).biUnion fib).image cls = F.image cls := fun F => by
    ext π
    simp only [Finset.mem_image, Finset.mem_biUnion]
    constructor
    · rintro ⟨i, ⟨π', ⟨j, hj, rfl⟩, hi⟩, rfl⟩
      exact ⟨j, hj, (mem_fib.1 hi).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, ⟨cls j, ⟨j, hj, rfl⟩, mem_fib.2 rfl⟩, rfl⟩
  have filter_biUnion : ∀ (F : Finset ι), ∀ π ∈ F.image cls,
      ((F.image cls).biUnion fib).filter (fun i => cls i = π) = fib π := fun F π hπ => by
    ext i
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨-, h⟩; exact mem_fib.2 h
    · intro hi; exact ⟨⟨π, hπ, hi⟩, mem_fib.1 hi⟩
  have fib_disj : ∀ (P : Finset (HeckeEigensystem K ℂ)),
      (↑P : Set (HeckeEigensystem K ℂ)).PairwiseDisjoint fib := fun P π _ π' _ hne => by
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    exact hne ((mem_fib.1 hi).symm.trans (mem_fib.1 hi'))

  have hS_eq : ∀ π, ∀ i ∈ fib π, (eLpNorm (T (b i)) 2 ((μ K).restrict Φ)).toReal =
      (eLpNorm (T (b i)) 2 ((μ K).restrict Φ₀)).toReal := fun π i hi => by
    rw [hnorm_eq (hVle _ (hTV _ _ (hbV i)))]
  have hHS' : ∀ s : ℝ, 0 ≤ s → ∃ M : ℝ, ∀ F : Finset ι,
      ∑ π ∈ F.image cls, Λ π ^ s *
        Real.sqrt (∑ i ∈ fib π, (eLpNorm (T (b i)) 2 ((μ K).restrict Φ)).toReal ^ 2) ≤ M := by
    intro s hs
    obtain ⟨M, hM⟩ := hHS s hs
    refine ⟨M, fun F => ?_⟩
    have := hM ((F.image cls).biUnion fib)
    rw [image_biUnion F] at this
    refine le_of_eq_of_le (Finset.sum_congr rfl fun π hπ => ?_) this
    rw [filter_biUnion F π hπ]
    congr 2
    exact Finset.sum_congr rfl fun i hi => by rw [hS_eq π i hi]

  refine ⟨fun C hC => ?h1, fun i => ?h2, ?h3⟩
  case h2 =>
    exact integrable_mul_of_memLp_two (hL2Φ (hTV _ _ (hbV i))) (memLp_two_conj (hL2b i))
  case h1 =>
    obtain ⟨Cst, A, hCst, hA, hSUP⟩ :=
      AutomorphicForm.exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact
        K α β hα hαβ ξ hξc hξt S N hN tys C hC
    obtain ⟨M, hM⟩ := hHS' (2 * A) (by positivity)
    refine ⟨Cst ^ 2 * M, fun x hx y hy => ?_⟩
    have key : ∀ F : Finset ι, ∑ i ∈ F, ‖T (b i) x * conj (b i y)‖ ≤ Cst ^ 2 * M := by
      intro F
      set P := F.image cls with hP

      have hpt : ∀ π, ∀ z ∈ C, ∀ v ∈ V₀ π, ‖v z‖ ≤ (Cst * Λ π ^ A) * (eLpNorm v 2 ((μ K).restrict Φ)).toReal :=
        fun π z hz v hv => by
          rw [← hnorm_eq hv]
          exact hSUP π (Λ π) (hΛ1 π) (hSUPhypR π) (hSUPhypC π) v hv z hz
      have hBnn : ∀ π, 0 ≤ Cst * Λ π ^ A := fun π => mul_nonneg hCst (Real.rpow_nonneg (hΛpos π).le _)
      have hclass : ∀ π ∈ P, ∑ i ∈ fib π, ‖T (b i) x * conj (b i y)‖ ≤
          (Cst * Λ π ^ A) ^ 2 * Real.sqrt (∑ i ∈ fib π, (eLpNorm (T (b i)) 2 ((μ K).restrict Φ)).toReal ^ 2) :=
        fun π hπ => by
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hπ
          refine sum_norm_apply_mul_le hortho hL2b (V₀ (cls j)) (fib (cls j)) (fun i hi => ?_) T
            (fun i hi => ?_) x y _ (hBnn _) (hpt _ x hx) (hpt _ y hy)
          · have := hbV₀ i; rwa [mem_fib.1 hi] at this
          · rw [hspan (cls j) ⟨j, rfl⟩]
            have := hTV _ _ (hbV i); rwa [mem_fib.1 hi] at this
      calc ∑ i ∈ F, ‖T (b i) x * conj (b i y)‖
          ≤ ∑ i ∈ P.biUnion fib, ‖T (b i) x * conj (b i y)‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg (fib_sub F) (fun i _ _ => norm_nonneg _)
        _ = ∑ π ∈ P, ∑ i ∈ fib π, ‖T (b i) x * conj (b i y)‖ := Finset.sum_biUnion (fib_disj P)
        _ ≤ ∑ π ∈ P, (Cst * Λ π ^ A) ^ 2 *
              Real.sqrt (∑ i ∈ fib π, (eLpNorm (T (b i)) 2 ((μ K).restrict Φ)).toReal ^ 2) :=
            Finset.sum_le_sum hclass
        _ = Cst ^ 2 * ∑ π ∈ P, Λ π ^ (2 * A) *
              Real.sqrt (∑ i ∈ fib π, (eLpNorm (T (b i)) 2 ((μ K).restrict Φ)).toReal ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun π _ => ?_
            have e : (Λ π ^ A) ^ 2 = Λ π ^ (2 * A) := by
              rw [← Real.rpow_two (Λ π ^ A), ← Real.rpow_mul (hΛpos π).le, mul_comm A 2]
            rw [mul_pow, e]
            ring
        _ ≤ Cst ^ 2 * M := mul_le_mul_of_nonneg_left (hM F) (sq_nonneg _)
    exact KerAssembly.summable_and_tsum_le_of_sum_le (fun i => norm_nonneg _) key
  case h3 => exact hD.2

#print axioms solution

end
end S_AutomorphicForm_forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab (solution)
