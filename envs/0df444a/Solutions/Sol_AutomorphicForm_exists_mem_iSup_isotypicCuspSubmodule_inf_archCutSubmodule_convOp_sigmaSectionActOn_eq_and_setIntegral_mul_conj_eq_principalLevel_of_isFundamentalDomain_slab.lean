-- Prove2me | solution 1 for AutomorphicForm.exists_mem_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_convOp_sigmaSectionActOn_eq_and_setIntegral_mul_conj_eq_principalLevel_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2156c9ec-abc1-5b8e-a590-5d6375e03847

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_convOp_sigmaSectionActOn_eq_and_setIntegral_mul_conj_eq_principalLevel_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq"
p2m_attr_erase "simp" "SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.TateLocal.conductorExponentAt_one HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul"
p2m_attr_erase "simp" "RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4ProjSigma

variable {L : Type} [Field L] [NumberField L]

section Members

variable {ΦL : Set (AdelicGL2 (𝓞 L) L)} {U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L)}
  {gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L} {B : Set (AdeleRing (𝓞 L) L)}
  {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} {N : Ideal (𝓞 L)}
  {SL : Finset (HeightOneSpectrum (𝓞 L))} {π : HeckeEigensystem L ℂ}

theorem lsXiMemberAt_of_isIsotypicCuspFormAt {u : AdelicGL2 (𝓞 L) L → ℂ}
    (h : IsIsotypicCuspFormAt L (productionPinsOf L ΦL U gen B) ξL N SL π u) :
    IsLsXiFunction (𝓞 L) L ⊤ ξL u ∧ MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) := by
  have h1 : LsXiMemberAt (𝓞 L) L (adelicGLHaar (Fin 2) (𝓞 L) L) ⊤ ξL ΦL u := h.smoothCusp.1.1
  exact (lsXiMemberAt_iff (𝓞 L) L _ ⊤ ξL ΦL u).1 h1

theorem isLsXiFunction_and_memLp_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π) :
    IsLsXiFunction (𝓞 L) L ⊤ ξL u ∧ MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) := by
  refine Submodule.span_induction (p := fun u _ =>
    IsLsXiFunction (𝓞 L) L ⊤ ξL u ∧ MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL))
    ?_ ?_ ?_ ?_ hu
  · exact fun u h => lsXiMemberAt_of_isIsotypicCuspFormAt h
  · exact ⟨⟨fun _ _ => rfl, fun _ _ => by simp⟩, MemLp.zero'⟩
  · rintro u w - - ⟨⟨hul, huc⟩, hu2⟩ ⟨⟨hwl, hwc⟩, hw2⟩
    refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hu2.add hw2⟩
    · simp only [Pi.add_apply, hul, hwl]
    · simp only [Pi.add_apply, huc, hwc, mul_add]
  · rintro c u - ⟨⟨hul, huc⟩, hu2⟩
    refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hu2.const_smul c⟩
    · simp only [Pi.smul_apply, hul]
    · simp only [Pi.smul_apply, huc, smul_eq_mul]
      ring

end Members

section Twist

variable (K : Type) [Field K] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) a) := by
  refine Units.ext ?_
  change ((Matrix.scalar (Fin 2) (a : R)).map f : Matrix (Fin 2) (Fin 2) S) =
    Matrix.scalar (Fin 2) (f (a : R))
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f)]

theorem sigmaAdelicAct_centralScalar (τ : L ≃ₐ[K] L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D τ (centralScalar (𝓞 L) L w) =
      centralScalar (𝓞 L) L
        (Units.map ((D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) w) :=
  map_scalar (D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom w

variable {K D}

theorem isLsXiFunction_sigmaSectionActOn (σ : L ≃ₐ[K] L)
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξ ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ =
        ξ ⟨z, Subgroup.mem_top z⟩)
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : IsLsXiFunction (𝓞 L) L ⊤ ξ u) :
    IsLsXiFunction (𝓞 L) L ⊤ ξ (sigmaSectionActOn K L D σ u) := by
  refine ⟨fun γ x => ?_, fun z x => ?_⟩
  · show u (sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L γ * x)) = u (sigmaAdelicAct K L D σ x)
    rw [map_mul, show sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L γ) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) from
        sigmaAdelicAct_globalPoints K L D σ γ, hu.left_invariant]
  · obtain ⟨z, hz⟩ := z
    show u (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x)) =
      ((ξ ⟨z, hz⟩ : ℂˣ) : ℂ) * u (sigmaAdelicAct K L D σ x)
    rw [map_mul, sigmaAdelicAct_centralScalar, hu.central_transform ⟨_, Subgroup.mem_top _⟩, hξσ z]

end Twist

end R4ProjSigma

end

open R4ProjSigma in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξ ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ =
        ξ ⟨z, Subgroup.mem_top z⟩)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : Ψ ∈ cuspClasses L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL)
    (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : u ∈ isotypicCuspSubmodule L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL Ψ ⊓ archCutSubmodule L tysL) :
    ∃ u₁ ∈ ⨆ (π : HeckeEigensystem L ℂ) (_ : π ∈ cuspClasses L
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL),
        isotypicCuspSubmodule L
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL π ⊓ archCutSubmodule L tysL,
      (∀ (f : AdelicGL2 (𝓞 L) L → ℂ), Continuous f → HasCompactSupport f →
          IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f →
          IsArchBiFinite L tysL f →
        convOp L f (sigmaSectionActOn K L D σ u) = convOp L f u₁) ∧
      ∀ π ∈ cuspClasses L
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL,
      ∀ b ∈ isotypicCuspSubmodule L
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL π ⊓ archCutSubmodule L tysL,
        ∫ x in Φ, sigmaSectionActOn K L D σ u x * conj (b x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
          ∫ x in Φ, u₁ x * conj (b x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  classical
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  set P := productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun v => heckeGen (𝓞 L) L v) (adelicBox L) with hP
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ

  have huV : u ∈ isotypicCuspSubmodule L P ξ N SL Ψ := (Submodule.mem_inf.mp hu).1
  have huc : Continuous u := continuous_of_mem_isotypicCuspSubmodule huV
  obtain ⟨hul, hu2⟩ := isLsXiFunction_and_memLp_of_mem huV
  have hσc : Continuous (sigmaSectionActOn K L D σ u) := continuous_sigmaSectionActOn K L D σ huc
  have hσl : IsLsXiFunction (𝓞 L) L ⊤ ξ (sigmaSectionActOn K L D σ u) :=
    isLsXiFunction_sigmaSectionActOn σ hξσ hul
  have hσ2 : MemLp (sigmaSectionActOn K L D σ u) 2 (μ.restrict Φ) := by
    have hsq : IntegrableOn (fun x => ‖u x‖ ^ 2) Φ μ := (memLp_two_iff_integrable_sq_norm hu2.1).1 hu2
    have hul' : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L),
        u (globalPoints (𝓞 L) L γ * x) = u x := fun γ x => hul.left_invariant γ x
    obtain ⟨-, -, -, h4, -⟩ :=
      AutomorphicForm.integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab
        K L D σ α β Φ Φ hΦs hΦ hΦs hΦ ℝ (fun x => ‖u x‖ ^ 2)
        (fun γ x => by simp only [hul' γ x])
        (fun x _ => ‖u x‖ ^ 2) (fun γ x _ => by simp only [hul' γ x]) (fun _ _ _ => rfl)
    have hsq' : IntegrableOn (fun x => ‖sigmaSectionActOn K L D σ u x‖ ^ 2) Φ μ := h4.1 hsq
    exact (memLp_two_iff_integrable_sq_norm hσc.aestronglyMeasurable).2 hsq'

  obtain ⟨Ψ', hΨ'N, hΨ'S, hT⟩ :=
    AutomorphicForm.exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
      K L D σ α β hα hαβ Φ hΦs hΦ ξ hξσ SL hSL N hN tysL Ψ hΨ.1
  have hR : ∀ (f : AdelicGL2 (𝓞 L) L → ℂ), Continuous f → HasCompactSupport f →
      IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f →
      IsArchBiFinite L tysL f →
      convOp L f (sigmaSectionActOn K L D σ u) ∈
        isotypicCuspSubmodule L P ξ N SL Ψ' ⊓ archCutSubmodule L tysL :=
    fun f hf hfc hfU hft => hT f hf hfc hfU hft u hu

  obtain ⟨u₁, hu₁W, h1, h2⟩ :=
    AutomorphicForm.exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab
      L α β hα hαβ Φ hΦs hΦ ξ SL N hN tysL Ψ' hΨ'N hΨ'S (sigmaSectionActOn K L D σ u) hσl hσc hσ2 hR
  refine ⟨u₁, ?_, h1, h2⟩

  by_cases hu₁0 : u₁ = 0
  · rw [hu₁0]
    exact Submodule.zero_mem _
  · have hne : isotypicCuspSubmodule L P ξ N SL Ψ' ≠ ⊥ := by
      intro hbot
      apply hu₁0
      have : u₁ ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)) := hbot ▸ (Submodule.mem_inf.mp hu₁W).1
      exact (Submodule.mem_bot ℂ).mp this
    have hΨ'cls : Ψ' ∈ cuspClasses L P ξ N SL := ⟨hΨ'N, hΨ'S, hne⟩
    exact Submodule.mem_iSup_of_mem Ψ' (Submodule.mem_iSup_of_mem hΨ'cls hu₁W)

end S_AutomorphicForm_exists_mem_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_convOp_sigmaSectionActOn_eq_and_setIntegral_mul_conj_eq_principalLevel_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_convOp_sigmaSectionActOn_eq_and_setIntegral_mul_conj_eq_principalLevel_of_isFundamentalDomain_slab (solution)
