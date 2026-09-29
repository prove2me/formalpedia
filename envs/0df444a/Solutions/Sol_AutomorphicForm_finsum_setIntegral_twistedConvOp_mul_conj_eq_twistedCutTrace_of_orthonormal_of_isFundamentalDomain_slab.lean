-- Prove2me | solution 1 for AutomorphicForm.finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/555d0078-cd6d-5197-90c2-74e60f00298f

import Theorems.Thm_AutomorphicForm_exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace R4CuspSigma

variable {L : Type} [Field L] [NumberField L]

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

attribute [local instance] isHaar

theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_gl2 : Countable (GL (Fin 2) L) := by
  haveI := countable_numberField (L := L)
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

scoped instance countable_range : Countable (globalPoints (𝓞 L) L).range := by
  haveI := countable_gl2 (L := L)
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 L) L))

def slab (L : Type) [Field L] [NumberField L] (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem globalPoints_mul_mem_slab_iff {α β : ℝ} (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L γ * x ∈ slab L α β ↔ x ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

scoped instance smulInvariantMeasure_slab (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨g, γ₀, rfl⟩ := γ
  have hslab : MeasurableSet (slab L α β) :=
    measurableSet_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable
  have hpre : (fun x : AdelicGL2 (𝓞 L) L =>
      (⟨globalPoints (𝓞 L) L γ₀, γ₀, rfl⟩ : (globalPoints (𝓞 L) L).range) • x) ⁻¹' s =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s := rfl
  rw [hpre, Measure.restrict_apply ((measurable_const_mul _) hs), Measure.restrict_apply hs]
  have hset : (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s ∩ slab L α β =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' (s ∩ slab L α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset, measure_preimage_mul]

theorem setIntegral_eq_of_isFundamentalDomain {α β : ℝ} {Φ₀ ΦL : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ₀s : Φ₀ ⊆ slab L α β)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (hΦs : ΦL ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (F : AdelicGL2 (𝓞 L) L → ℂ) (hF : ∀ (γ : GL (Fin 2) L) (x), F (globalPoints (𝓞 L) L γ * x) = F x) :
    ∫ x in Φ₀, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = ∫ x in ΦL, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  have h := hΦ₀.setIntegral_eq hΦ (f := F) (fun γ x => by
    obtain ⟨g, γ₀, rfl⟩ := γ
    exact hF γ₀ x)
  rwa [Measure.restrict_restrict_of_subset hΦ₀s, Measure.restrict_restrict_of_subset hΦs] at h

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

theorem isLsXiFunction_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π) :
    IsLsXiFunction (𝓞 L) L ⊤ ξL u :=
  (isLsXiFunction_and_memLp_of_mem hu).1

theorem memLp_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) :=
  (isLsXiFunction_and_memLp_of_mem hu).2

theorem apply_globalPoints_mul_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π)
    (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L) : u (globalPoints (𝓞 L) L γ * g) = u g :=
  (isLsXiFunction_of_mem hu).left_invariant γ g

theorem apply_centralScalar_mul_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π)
    (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    u (centralScalar (𝓞 L) L z * g) = ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u g :=
  (isLsXiFunction_of_mem hu).central_transform ⟨z, Subgroup.mem_top z⟩ g

end Members

section Pairing

variable (Φ : Set (AdelicGL2 (𝓞 L) L))

def ip (u v : AdelicGL2 (𝓞 L) L → ℂ) : ℂ :=
  ∫ x in Φ, u x * conj (v x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)

variable {Φ}

theorem integrable_mul_conj {u v : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hv : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ)) :
    Integrable (fun x => u x * conj (v x)) ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ) := by
  have hv' : MemLp (star v) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ) := hv.star
  exact hu.integrable_mul hv'

theorem ip_add_left {u w v : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hw : MemLp w 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hv : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ)) :
    ip Φ (u + w) v = ip Φ u v + ip Φ w v := by
  unfold ip
  simp only [Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_conj hu hv) (integrable_mul_conj hw hv)

theorem ip_smul_left (c : ℂ) (u v : AdelicGL2 (𝓞 L) L → ℂ) :
    ip Φ (c • u) v = c * ip Φ u v := by
  unfold ip
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem ip_zero_left (v : AdelicGL2 (𝓞 L) L → ℂ) : ip Φ 0 v = 0 := by
  simp [ip]

theorem ip_sum_smul_left {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → AdelicGL2 (𝓞 L) L → ℂ)
    (v : AdelicGL2 (𝓞 L) L → ℂ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hv : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ)) :
    ip Φ (∑ i ∈ s, c i • f i) v = ∑ i ∈ s, c i * ip Φ (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ip_add_left ((hf a (Finset.mem_insert_self a s)).const_smul (c a))
        (memLp_finsetSum' s fun i hi => (hf i (Finset.mem_insert_of_mem hi)).const_smul (c i)) hv,
      ip_smul_left, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end Pairing

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

theorem twistedConvOp_centralScalar_mul (σ : L ≃ₐ[K] L)
    {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} (φ u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsLsXiFunction (𝓞 L) L ⊤ ξL u) (z : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L) :
    twistedConvOp K L D σ φ u (centralScalar (𝓞 L) L z * x) =
      ((ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
        twistedConvOp K L D σ φ u x := by
  rw [twistedConvOp_apply, rightConv_apply, rightConv_apply]
  simp only [sigmaSectionActOn, Function.comp_apply, map_mul, sigmaAdelicAct_centralScalar K D σ z,
    mul_assoc]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [hu.central_transform ⟨_, Subgroup.mem_top _⟩, mul_assoc]

theorem twistedConvOp_globalPoints_mul (σ : L ≃ₐ[K] L)
    {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} (φ u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsLsXiFunction (𝓞 L) L ⊤ ξL u) (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) :
    twistedConvOp K L D σ φ u (globalPoints (𝓞 L) L γ * x) = twistedConvOp K L D σ φ u x := by
  rw [twistedConvOp_apply, rightConv_apply, rightConv_apply]
  simp only [sigmaSectionActOn, Function.comp_apply, map_mul, mul_assoc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [show sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L γ) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) from
    sigmaAdelicAct_globalPoints K L D σ γ, hu.left_invariant]

end Twist

end R4CuspSigma
p2m_reactivate "P2MW.S_AutomorphicForm_finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab.R4CuspSigma"

end
p2m_reactivate "P2MW.S_AutomorphicForm_finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab.R4CuspSigma"

open R4CuspSigma in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (hφt : IsArchBiFinite L tysL φ)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : Ψ ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL) :
    ∑ᶠ i : {i // cls i = Ψ},
        ∫ x in Φ₀, twistedConvOp K L D σ φ (b i) x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      twistedCutTrace K L D σ
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc := by
  classical
  haveI := isHaar (L := L)

  set W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := isotypicCuspSubmodule L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ ⊓ archCutSubmodule L tysL with hW
  set A : (AdelicGL2 (𝓞 L) L → ℂ) → (AdelicGL2 (𝓞 L) L → ℂ) := twistedConvOp K L D σ φ with hA

  obtain ⟨hfin, hspan⟩ := hbs Ψ hΨ
  haveI : Finite {i // cls i = Ψ} := hfin.to_subtype
  letI : Fintype {i // cls i = Ψ} := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]

  have hbW : ∀ i : {i // cls i = Ψ}, b i ∈ W := by
    intro i
    have h := (hb i.1).2
    rwa [i.2] at h
  have hV : ∀ u ∈ W, u ∈ isotypicCuspSubmodule L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ :=
    fun u hu => (Submodule.mem_inf.mp hu).1
  have hbV : ∀ i : ι, b i ∈ isotypicCuspSubmodule L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) :=
    fun i => (Submodule.mem_inf.mp (hb i).2).1
  have hb2 : ∀ i : ι, MemLp (b i) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) :=
    fun i => memLp_of_mem (hbV i)
  have hip₁ : ∀ i : ι, ip ΦL (b i) (b i) = 1 := fun i => hb₁ i
  have hip₀ : ∀ i j : ι, i ≠ j → ip ΦL (b i) (b j) = 0 := fun i j h => hb₀ i j h

  have hFD : ∀ {u v : AdelicGL2 (𝓞 L) L → ℂ} {π π' : HeckeEigensystem L ℂ},
      u ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π →
      v ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π' →
      ∫ x in Φ₀, u x * conj (v x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = ip ΦL u v := by
    intro u v π π' hu hv
    exact setIntegral_eq_of_isFundamentalDomain (α := α) (β := β) hΦ₀s hΦ₀ hΦs hΦ
      (fun x => u x * conj (v x)) fun γ x => by
        simp only [apply_globalPoints_mul_of_mem hu, apply_globalPoints_mul_of_mem hv]
  by_cases hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩
  swap
  ·
    push Not at hξσ
    have hL : ∀ i : {i // cls i = Ψ},
        ∫ x in Φ₀, A (b i) x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := fun i =>
      AutomorphicForm.setIntegral_twistedConvOp_mul_conj_eq_zero_of_exists_apply_act_ne_of_isFundamentalDomain_slab
        K L D σ α β ΦL hΦ Φ₀ hΦ₀s hΦ₀ ξL hξσ (b i) (b i) (isLsXiFunction_of_mem (hbV i))
        (isLsXiFunction_of_mem (hbV i)) (hb2 i) φ
    rw [Finset.sum_eq_zero fun i _ => hL i, twistedCutTrace_eq]
    by_cases hmaps : ∀ u ∈ W, A u ∈ W
    · rw [twistedConvTraceOn_eq_traceOn K L D σ _ hφ hφc hmaps, traceOn_eq]
      obtain ⟨z₀, hz₀⟩ := hξσ
      have hzero : ∀ u ∈ W, A u = 0 := by
        intro u hu
        funext x
        have h1 := twistedConvOp_centralScalar_mul (D := D) σ φ u (isLsXiFunction_of_mem (hV u hu)) z₀ x
        have h2 := apply_centralScalar_mul_of_mem (hV _ (hmaps u hu)) z₀ x
        have h3 : (((ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
              AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z₀, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) -
            ((ξL ⟨z₀, Subgroup.mem_top z₀⟩ : ℂˣ) : ℂ)) * A u x = 0 := by
          rw [sub_mul, ← h1, hA, ← h2, sub_self]
        rcases mul_eq_zero.mp h3 with h | h
        · exact absurd (Units.val_injective (sub_eq_zero.mp h)) hz₀
        · exact h
      have hEnd : (isStableLinearOn_twistedConvOp K L D σ
          (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ hφc hmaps).toEnd = 0 :=
        LinearMap.ext fun u => Subtype.ext (hzero u u.2)
      rw [hEnd, map_zero]
    · rw [twistedConvTraceOn_eq_zero K L D σ _ hφ hφc hmaps]
  by_cases hmaps : ∀ u ∈ W, A u ∈ W
  ·
    have hL2 : ∀ u ∈ W, MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) :=
      fun u hu => memLp_of_mem (hV u hu)
    rw [twistedCutTrace_eq, twistedConvTraceOn_eq_traceOn K L D σ _ hφ hφc hmaps, traceOn_eq]
    set hst := isStableLinearOn_twistedConvOp K L D σ
      (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ hφc hmaps with hhst

    let e : {i // cls i = Ψ} → W := fun i => ⟨b i, hbW i⟩
    have hip_e : ∀ i j : {i // cls i = Ψ}, ip ΦL (b j) (b i) = if j = i then 1 else 0 := by
      intro i j
      split_ifs with h
      · rw [h]; exact hip₁ i
      · exact hip₀ j i fun h' => h (Subtype.ext h')
    have hli : LinearIndependent ℂ e := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hg' : ∑ j, g j • b (j : ι) = 0 := by
        have := congrArg (Subtype.val : W → AdelicGL2 (𝓞 L) L → ℂ) hg
        simpa [e, Submodule.coe_sum, Submodule.coe_smul] using this
      have h := congrArg (fun u => ip ΦL u (b i)) hg'
      rw [ip_sum_smul_left Finset.univ g (fun j : {i // cls i = Ψ} => b (j : ι)) (b i)
        (fun j _ => hb2 j) (hb2 i), ip_zero_left] at h
      simp only [hip_e i, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true] at h
      exact h
    have hsp : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
      rintro w -
      have hw : (w : AdelicGL2 (𝓞 L) L → ℂ) ∈ Submodule.span ℂ (b '' {i | cls i = Ψ}) := by
        rw [hspan]; exact w.2
      have hrange : W.subtype '' Set.range e = b '' {i | cls i = Ψ} := by
        ext u
        simp only [Set.mem_image, Set.mem_range, Set.mem_setOf_eq, Submodule.coe_subtype]
        constructor
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, i.2, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          exact ⟨e ⟨i, hi⟩, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
      rw [← Submodule.apply_mem_span_image_iff_mem_span (Submodule.injective_subtype W), hrange]
      exact hw
    let B : Module.Basis {i // cls i = Ψ} ℂ W := Module.Basis.mk hli hsp
    have hB : ∀ i, B i = e i := fun i => Module.Basis.mk_apply hli hsp i

    have hcoord : ∀ (i : {i // cls i = Ψ}) (w : W), B.repr w i = ip ΦL w (b i) := by
      intro i
      let f : W →ₗ[ℂ] ℂ :=
        { toFun := fun w => ip ΦL (w : AdelicGL2 (𝓞 L) L → ℂ) (b i)
          map_add' := fun w w' => by
            simp only [Submodule.coe_add]
            exact ip_add_left (hL2 _ w.2) (hL2 _ w'.2) (hb2 i)
          map_smul' := fun c w => by
            simp only [Submodule.coe_smul, RingHom.id_apply]
            exact ip_smul_left c _ _ }
      have key : B.coord i = f := by
        refine B.ext fun j => ?_
        show (Module.Basis.mk hli hsp).coord i ((Module.Basis.mk hli hsp) j) =
          ip ΦL ((Module.Basis.mk hli hsp j : W) : AdelicGL2 (𝓞 L) L → ℂ) (b i)
        rw [Module.Basis.mk_apply, Module.Basis.mk_coord_apply]
        exact (hip_e i j).symm
      intro w
      have := congrArg (fun g : W →ₗ[ℂ] ℂ => g w) key
      simp [Module.Basis.coord_apply] at this
      exact this
    rw [LinearMap.trace_eq_matrix_trace ℂ B, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hcoord, hB]
    show ∫ x in Φ₀, A (b i) x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ip ΦL (A (b i)) (b i)
    exact hFD (hV _ (hmaps _ (hbW i))) (hV _ (hbW i))
  ·
    obtain ⟨Ψ', hΨ'N, hΨ'S, hmap⟩ :=
      AutomorphicForm.exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isBiInvariantUnder_of_isFundamentalDomain_slab
        K L D σ α β hα hαβ ΦL hΦs hΦ ξL hξσ SL hSL N hN tysL Ψ hΨ.1
    have hmapφ := hmap φ hφ hφc hφU hφt
    set W' : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ' ⊓ archCutSubmodule L tysL with hW'
    have hV' : ∀ u ∈ W', u ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ' :=
      fun u hu => (Submodule.mem_inf.mp hu).1
    have hne : Ψ' ≠ Ψ := by
      rintro rfl
      exact hmaps hmapφ
    have hW'ne : W' ≠ ⊥ := by
      intro hbot
      apply hmaps
      intro u hu
      have h := hmapφ u hu
      rw [hbot, Submodule.mem_bot] at h
      show twistedConvOp K L D σ φ u ∈ W
      rw [h]
      exact W.zero_mem
    have hV'ne : isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ' ≠ ⊥ := by
      intro h
      apply hW'ne
      rw [hW', h, bot_inf_eq]
    have hΨ'c : Ψ' ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL := ⟨hΨ'N, hΨ'S, hV'ne⟩
    obtain ⟨-, hspan'⟩ := hbs Ψ' hΨ'c
    have hL2' : ∀ u ∈ Submodule.span ℂ (b '' {j | cls j = Ψ'}),
        MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) := by
      intro u hu
      rw [hspan'] at hu
      exact memLp_of_mem (hV' u hu)
    have hL : ∀ i : {i // cls i = Ψ},
        ∫ x in Φ₀, A (b i) x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by
      intro i
      have hAi : A (b i) ∈ W' := hmapφ _ (hbW i)
      rw [hFD (hV' _ hAi) (hbV i)]
      have hAi' : A (b i) ∈ Submodule.span ℂ (b '' {j | cls j = Ψ'}) := by
        rw [hspan']; exact hAi
      refine Submodule.span_induction (p := fun u _ => ip ΦL u (b i) = 0) ?_ ?_ ?_ ?_ hAi'
      · rintro _ ⟨j, hj, rfl⟩
        have hji : j ≠ i.1 := by
          intro h
          apply hne
          rw [Set.mem_setOf_eq] at hj
          rw [← hj, h, i.2]
        exact hip₀ j i.1 hji
      · exact ip_zero_left _
      · intro u w hu hw hu0 hw0
        rw [ip_add_left (hL2' u hu) (hL2' w hw) (hb2 i), hu0, hw0, add_zero]
      · intro c u hu hu0
        rw [ip_smul_left, hu0, mul_zero]
    rw [Finset.sum_eq_zero fun i _ => hL i, twistedCutTrace_eq,
      twistedConvTraceOn_eq_zero K L D σ _ hφ hφc hmaps]

end S_AutomorphicForm_finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_finsum_setIntegral_twistedConvOp_mul_conj_eq_twistedCutTrace_of_orthonormal_of_isFundamentalDomain_slab (solution)
