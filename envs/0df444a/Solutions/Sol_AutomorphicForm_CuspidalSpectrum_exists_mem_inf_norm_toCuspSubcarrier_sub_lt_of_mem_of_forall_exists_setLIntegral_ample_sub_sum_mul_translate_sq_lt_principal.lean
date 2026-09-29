-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/33987073-1247-5f2d-ae7d-915447810d7f

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import Theorems.Thm_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep
import Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_cuspKFiniteSubmodule_le_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul"
p2m_attr_erase "simp" "M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace C2ppPrincipalAssembly

variable {F : Type} [Field F] [NumberField F]

private abbrev levelFam (F : Type) [Field F] [NumberField F] : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F) :=
  fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F

private abbrev pinsOn (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (levelFam F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private abbrev pinsOnOne (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

private theorem cuspKFiniteSubmodule_pinsOn_eq (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    cuspKFiniteSubmodule F (pinsOn F D) ξ = cuspKFiniteSubmodule F (pinsOnOne F D) ξ := by
  unfold cuspKFiniteSubmodule IsSmoothCuspAutomorphicFnAt IsCuspAutomorphicFnAt
  rfl

section FinPrincipal

variable (F)

private def weylFin : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) := glFin (𝓞 F) F (weyl (𝓞 F) F)

private def finPrincipalSet (N : Ideal (𝓞 F)) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  {k | k ∈ finiteLevelOne (𝓞 F) F N ∧ (weylFin F)⁻¹ * k * weylFin F ∈ finiteLevelOne (𝓞 F) F N}

private theorem mem_principalLevel_iff_glFin (N : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) :
    g ∈ principalLevel (𝓞 F) F N ↔ glFin (𝓞 F) F g ∈ finPrincipalSet F N := by
  rw [mem_principalLevel_iff, mem_levelOne_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_levelOne_iff,
    map_mul, map_mul, map_inv]
  rfl

private theorem finPrincipalSet_eq (N : Ideal (𝓞 F)) :
    finPrincipalSet F N = (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) ∩
      (fun k => (weylFin F)⁻¹ * k * weylFin F) ⁻¹'
        (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := rfl

private theorem continuous_weylConj : Continuous (fun k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
    (weylFin F)⁻¹ * k * weylFin F) :=
  (continuous_const.mul continuous_id).mul continuous_const

private theorem isCompact_finPrincipalSet (N : Ideal (𝓞 F)) : IsCompact (finPrincipalSet F N) := by
  rw [finPrincipalSet_eq]
  exact (isCompact_finiteLevelOne (𝓞 F) F N).inter_right
    ((isClosed_finiteLevelOne (𝓞 F) F N).preimage (continuous_weylConj F))

private theorem isOpen_finPrincipalSet {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsOpen (finPrincipalSet F N) := by
  rw [finPrincipalSet_eq]
  exact (isOpen_finiteLevelOne (𝓞 F) F hN).inter
    ((isOpen_finiteLevelOne (𝓞 F) F hN).preimage (continuous_weylConj F))

private theorem finPrincipalSet_subset_finiteIntegralGL2 (N : Ideal (𝓞 F)) :
    finPrincipalSet F N ⊆ (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
  fun _ hk => mem_finiteIntegralGL2_iff.mpr ⟨hk.1.1.integral, hk.1.2.integral⟩

private theorem finEmbed_mem_of_mem_finPrincipalSet {N : Ideal (𝓞 F)} {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ finPrincipalSet F N) :
    AdelicDock.finEmbed (𝓞 F) F k ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show AdelicDock.finEmbed (𝓞 F) F k ∈ principalLevel (𝓞 F) F N
    rw [mem_principalLevel_iff_glFin, AdelicDock.glFin_finEmbed]; exact hk
  · show AdelicDock.finEmbed (𝓞 F) F k ∈ finiteAdelicGL2Subgroup F
    rw [mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]

private theorem glFin_image_principalLevel_inf (N : Ideal (𝓞 F)) :
    (glFin (𝓞 F) F) '' ((principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
      Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) = finPrincipalSet F N := by
  ext k
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_principalLevel_iff_glFin F N g).mp hg.1
  · intro hk
    exact ⟨AdelicDock.finEmbed (𝓞 F) F k, finEmbed_mem_of_mem_finPrincipalSet F hk,
      AdelicDock.glFin_finEmbed (𝓞 F) F k⟩

theorem isOpen_glFin_image_principalLevel_inf {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsOpen ((glFin (𝓞 F) F) '' ((principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
      Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [glFin_image_principalLevel_inf]; exact isOpen_finPrincipalSet F hN

theorem isCompact_glFin_image_principalLevel_inf (N : Ideal (𝓞 F)) :
    IsCompact ((glFin (𝓞 F) F) '' ((principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
      Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F))) := by
  rw [glFin_image_principalLevel_inf]; exact isCompact_finPrincipalSet F N

theorem glFin_image_principalLevel_inf_subset_finiteIntegralGL2 (N : Ideal (𝓞 F)) :
    (glFin (𝓞 F) F) '' ((principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :
      Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) ⊆
      (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  rw [glFin_image_principalLevel_inf]; exact finPrincipalSet_subset_finiteIntegralGL2 F N

end FinPrincipal

private theorem eLpNorm_two_pow_two {α : Type*} [MeasurableSpace α] (ν : Measure α) (φ : α → ℂ) :
    eLpNorm φ 2 ν ^ 2 = ∫⁻ a, ‖φ a‖ₑ ^ 2 ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem norm_toCarrier {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (a : AdelicGL2 (𝓞 F) F → ℂ) (ha : a ∈ memberSubmodule F Φ₀ ξ) :
    ‖toCarrier F hΦ₀ σ ξ ⟨a, ha⟩‖ = (eLpNorm a 2 (weightedMeasure F Φ₀ σ)).toReal :=
  Lp.norm_toLp a (memLp_weightedMeasure_of_mem F hΦ₀ σ ha)

private theorem weightedMeasure_le {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) :
    weightedMeasure F Φ₀ σ ≤ ENNReal.ofReal (max (α ^ (-σ)) (β ^ (-σ))) • (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀ := by
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have hres : μ.restrict Φ₀ = (μ.restrict (detNormSlab F α β)).restrict Φ₀ := by
    rw [Measure.restrict_restrict₀ hΦ₀.isFundamentalDomain.nullMeasurableSet, Set.inter_eq_left.mpr hΦ₀.subset]
  have hae : ∀ᵐ x ∂(μ.restrict Φ₀), x ∈ Φ₀ := by
    rw [hres]; exact ae_restrict_mem₀ hΦ₀.isFundamentalDomain.nullMeasurableSet
  have hbound : ∀ x ∈ Φ₀, weight F σ x ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hΦ₀.subset hx
    unfold weight
    rcases le_or_gt 0 (-σ) with hs | hs
    · exact (Real.rpow_le_rpow (hΦ₀.pos.le.trans h1) h2 hs).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hΦ₀.pos h1 hs.le).trans (le_max_left _ _)
  unfold weightedMeasure
  rw [← withDensity_const]
  exact withDensity_mono (hae.mono fun x hx => ENNReal.ofReal_le_ofReal (hbound x hx))

private theorem isSmoothCuspAutomorphicFnAt_fdPins_of {D Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsSmoothCuspAutomorphicFnAt F (pinsOn F D) ξ ψ)
    (hL2 : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀)) :
    IsSmoothCuspAutomorphicFnAt F (fdPins F Φ₀) ξ ψ := by
  refine ⟨⟨(isAutomorphicFnAt_fdPins_iff F Φ₀ ξ ψ).mpr ⟨?_, hL2⟩, h.1.2⟩, h.2⟩
  exact ((lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ D ψ).mp h.1.1).1

private theorem isLsXiFunction_of_isSmoothCuspAutomorphicFnAt {D : Set (AdelicGL2 (𝓞 F) F)}
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsSmoothCuspAutomorphicFnAt F (pinsOn F D) ξ ψ) : IsLsXiFunction (𝓞 F) F ⊤ ξ ψ :=
  ((lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ D ψ).mp h.1.1).1

private theorem memLp_of_isSmoothCuspAutomorphicFnAt {D : Set (AdelicGL2 (𝓞 F) F)}
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsSmoothCuspAutomorphicFnAt F (pinsOn F D) ξ ψ) : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) :=
  ((lsXiMemberAt_iff (𝓞 F) F (adelicGLHaar (Fin 2) (𝓞 F) F) ⊤ ξ D ψ).mp h.1.1).2

private def lsXiSubmodule (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {ψ | IsLsXiFunction (𝓞 F) F ⊤ ξ ψ}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => by simp⟩
  add_mem' := fun {a b} ha hb =>
    ⟨fun γ g => by rw [Pi.add_apply, Pi.add_apply, ha.1, hb.1],
      fun z g => by rw [Pi.add_apply, Pi.add_apply, ha.2, hb.2, mul_add]⟩
  smul_mem' := fun c {a} ha =>
    ⟨fun γ g => by rw [Pi.smul_apply, Pi.smul_apply, ha.1],
      fun z g => by rw [Pi.smul_apply, Pi.smul_apply, ha.2, smul_eq_mul, smul_eq_mul, mul_left_comm]⟩

private theorem rightTranslate_mem_lsXiSubmodule {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {ψ : AdelicGL2 (𝓞 F) F → ℂ} (h : ψ ∈ lsXiSubmodule ξ) (y : AdelicGL2 (𝓞 F) F) :
    rightTranslate F y ψ ∈ lsXiSubmodule ξ :=
  ⟨fun γ g => by rw [rightTranslate_apply, rightTranslate_apply, mul_assoc, h.1],
    fun z g => by rw [rightTranslate_apply, rightTranslate_apply, mul_assoc, h.2]⟩

private theorem continuous_and_lsXi_of_mem_cuspKFiniteSubmodule {D : Set (AdelicGL2 (𝓞 F) F)}
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ} {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : ψ ∈ cuspKFiniteSubmodule F (pinsOn F D) ξ) : Continuous ψ ∧ ψ ∈ lsXiSubmodule ξ := by
  refine Submodule.span_induction (p := fun ψ _ => Continuous ψ ∧ ψ ∈ lsXiSubmodule ξ) ?_ ?_ ?_ ?_ h
  · rintro ψ ⟨hsat, hcont, -⟩
    refine ⟨hcont, ?_⟩
    have h1 := isLsXiFunction_of_isSmoothCuspAutomorphicFnAt (hsat 1)
    have : rightTranslate F 1 ψ = ψ := funext fun x => by rw [rightTranslate_apply, mul_one]
    rw [this] at h1
    exact h1
  · exact ⟨continuous_const, (lsXiSubmodule ξ).zero_mem⟩
  · exact fun _ _ _ _ hu hw => ⟨hu.1.add hw.1, (lsXiSubmodule ξ).add_mem hu.2 hw.2⟩
  · exact fun c _ _ hu => ⟨hu.1.const_smul c, (lsXiSubmodule ξ).smul_mem c hu.2⟩

private theorem rightConv_mem_levelInvariantSubmodule {D : Set (AdelicGL2 (𝓞 F) F)} (N : Ideal (𝓞 F))
    (tys : ArchTypeFamily F) {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsLevelSphericalOfType F tys (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) f)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F ψ f ∈ levelInvariantSubmodule F (pinsOn F D) N := by
  obtain ⟨fa, -, -, -, hfeq⟩ := hf
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  intro y u hu
  have hu' : u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := hu
  have huarch : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp hu'.2
  have hfl : ∀ z, f (u⁻¹ * z) = f z := by
    intro z
    rw [hfeq, hfeq, map_mul, map_inv, huarch, inv_one, one_mul]
    congr 1
    rw [map_mul, map_inv]
    by_cases hz : glFin (𝓞 F) F z ∈
        glFin (𝓞 F) F '' ((principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
          Set (AdelicGL2 (𝓞 F) F))
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem]
      obtain ⟨k, hk, hkz⟩ := hz
      exact ⟨u⁻¹ * k, Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hk, by rw [map_mul, map_inv, hkz]⟩
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem]
      rintro ⟨k, hk, hkz⟩
      exact hz ⟨u * k, Subgroup.mul_mem _ hu' hk, by rw [map_mul, hkz, mul_inv_cancel_left]⟩
  show rightConv F ψ f (y * u) = rightConv F ψ f y
  simp only [rightConv_apply]
  rw [← integral_mul_left_eq_self (fun x => ψ (y * u * x) * f x) u⁻¹]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show ψ (y * u * (u⁻¹ * x)) * f (u⁻¹ * x) = ψ (y * x) * f x
  rw [hfl, mul_assoc, mul_inv_cancel_left]

private theorem rightConv_sum_smul_rightTranslate {f : AdelicGL2 (𝓞 F) F → ℂ} (hfc : Continuous f) (hfK : HasCompactSupport f)
    {φ₁ : AdelicGL2 (𝓞 F) F → ℂ} (hφ₁ : Continuous φ₁) (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (fun y => ∑ h ∈ s, l h * φ₁ (y * h)) f = ∑ h ∈ s, l h • rightConv F (rightTranslate F h φ₁) f := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext y
  simp only [rightConv_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rightTranslate_apply, Finset.sum_mul]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun h _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring
  · intro h _
    exact ((continuous_const.mul (hφ₁.comp ((continuous_const.mul continuous_id).mul continuous_const))).mul hfc).integrable_of_hasCompactSupport
      hfK.mul_left

private theorem memLp_restrict_of_lintegral_lt_top {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (h : ∫⁻ x in Φ₀, (‖ψ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤) :
    MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
  refine ⟨hψ.aestronglyMeasurable, ?_⟩
  have hsq : eLpNorm ψ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) ^ 2 < ⊤ := by
    rw [eLpNorm_two_pow_two]
    simpa only [enorm_eq_nnnorm] using h
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop] at hsq
  exact absurd hsq (by simp)

private theorem eLpNorm_weightedMeasure_sq_le {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) :
    eLpNorm ψ 2 (weightedMeasure F Φ₀ σ) ^ 2 ≤
      ENNReal.ofReal (max (α ^ (-σ)) (β ^ (-σ))) * ∫⁻ x in Φ₀, (‖ψ x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have hle := weightedMeasure_le hΦ₀ σ
  calc eLpNorm ψ 2 (weightedMeasure F Φ₀ σ) ^ 2 = ∫⁻ x, ‖ψ x‖ₑ ^ 2 ∂(weightedMeasure F Φ₀ σ) := eLpNorm_two_pow_two _ _
    _ ≤ ∫⁻ x, ‖ψ x‖ₑ ^ 2 ∂(ENNReal.ofReal (max (α ^ (-σ)) (β ^ (-σ))) • (adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
        lintegral_mono' hle le_rfl
    _ = ENNReal.ofReal (max (α ^ (-σ)) (β ^ (-σ))) * ∫⁻ x in Φ₀, ‖ψ x‖ₑ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        simp only [lintegral_smul_measure, smul_eq_mul]
    _ = _ := by simp only [enorm_eq_nnnorm]

end C2ppPrincipalAssembly

end

open C2ppPrincipalAssembly in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (φ₁ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₁ : φ₁ ∈ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hφc : Continuous φ)
    (hφN : φ ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N)
    (hφt : φ ∈ archCutSubmodule F tys)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ,
            (‖φ y - ∑ h ∈ s, l h * φ₁ (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ,
    ∃ x ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys,
    ∃ hxm : x ∈ cuspMemberSubmodule F Φ₀ ξ,
      ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩‖ < δ := by

  set Pp : CarrierPins F := productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F) with hPp
  have hsub : (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ) ⊆ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ :=
    Set.iUnion₂_mono fun x _ => Set.image_mono (centreCutSiegelSetAmple_subset c u d₁ d₂ κ)
  have hcovP : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) :=
    fun g => by obtain ⟨γ, z, hz⟩ := hcov g; exact ⟨γ, z, hsub hz⟩
  have hS3one := AutomorphicForm.CuspidalSpectrum.cuspKFiniteSubmodule_le_cuspMemberSubmodule F c u d₁ d₂ T hc hd₁ hd hcovP ξ hΦ₀
  have hS3 : cuspKFiniteSubmodule F Pp ξ ≤ cuspMemberSubmodule F Φ₀ ξ :=
    (C2ppPrincipalAssembly.cuspKFiniteSubmodule_pinsOn_eq (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ξ).trans_le
      hS3one
  obtain ⟨C, hC⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample
      F c u d₁ d₂ κ T hd hκ hcov ξ hΦ₀

  have hφx : IsLsXiFunction (𝓞 F) F ⊤ ξ φ := C2ppPrincipalAssembly.isLsXiFunction_of_isSmoothCuspAutomorphicFnAt hφ
  have hφL2a := C2ppPrincipalAssembly.memLp_of_isSmoothCuspAutomorphicFnAt hφ
  have hφfin : ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ, (‖φ x‖₊ : ℝ≥0∞) ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ := by
    have h2 := ENNReal.pow_lt_top hφL2a.eLpNorm_lt_top (n := 2)
    rw [C2ppPrincipalAssembly.eLpNorm_two_pow_two] at h2
    simpa only [enorm_eq_nnnorm] using h2
  have hφL2 : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
    C2ppPrincipalAssembly.memLp_restrict_of_lintegral_lt_top hφc
      (lt_of_le_of_lt (hC φ hφx hφc) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφfin))
  have hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ := ⟨C2ppPrincipalAssembly.isSmoothCuspAutomorphicFnAt_fdPins_of hφ hφL2, hφc⟩

  have hφU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, φ (g * k) = φ g :=
    fun g k hk => hφN g k hk
  obtain ⟨f, hft, hfsph, -, hφf, hφfδ⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
      F hΦ₀ σ ξ hσ (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) inf_le_right
      (C2ppPrincipalAssembly.isOpen_glFin_image_principalLevel_inf F hN)
      (C2ppPrincipalAssembly.isCompact_glFin_image_principalLevel_inf F N)
      (C2ppPrincipalAssembly.glFin_image_principalLevel_inf_subset_finiteIntegralGL2 F N)
      tys φ hφm hφU hφt (δ / 2) (half_pos hδ)
  have hfsph' := hfsph
  obtain ⟨fa, hfa_t, hfa_bf, hfa_c, hfa_eq⟩ := hfsph
  have hfbf : IsArchBiFinite F tys f := IsArchBiFinite.of_factorization F hfa_eq hfa_bf
  obtain ⟨hfc, hfK⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hft

  obtain ⟨Tf, -, hTf, -, -⟩ := AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfK

  set M : ℝ := ‖Tf‖ with hM
  set Cw : ℝ≥0∞ := ENNReal.ofReal (max (α ^ (-σ)) (β ^ (-σ))) with hCw
  set r : ℝ := δ / (2 * (M + 1)) with hr
  have hM0 : 0 ≤ M := norm_nonneg _
  have hrpos : 0 < r := div_pos hδ (by positivity)
  set K : ℝ≥0∞ := Cw * ENNReal.ofReal C with hK
  have hKtop : K + 1 ≠ ⊤ := by
    simp only [hK, hCw, ne_eq, ENNReal.add_eq_top, ENNReal.one_ne_top, or_false]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  set ε : ℝ≥0∞ := ENNReal.ofReal (r ^ 2) / (K + 1) with hεdef
  have hεpos : 0 < ε := ENNReal.div_pos (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity) hKtop
  obtain ⟨s, l, hsl⟩ := happrox ε hεpos
  set g : AdelicGL2 (𝓞 F) F → ℂ := fun y => ∑ h ∈ s, l h * φ₁ (y * h) with hgdef

  obtain ⟨hφ₁c, hφ₁x⟩ := C2ppPrincipalAssembly.continuous_and_lsXi_of_mem_cuspKFiniteSubmodule (hV.le hφ₁)
  have hgeq : g = ∑ h ∈ s, l h • rightTranslate F h φ₁ := by
    funext y
    simp only [hgdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rightTranslate_apply]
  have hgc : Continuous g :=
    continuous_finsetSum s fun h _ => continuous_const.mul (hφ₁c.comp (continuous_id.mul continuous_const))
  have hgx : IsLsXiFunction (𝓞 F) F ⊤ ξ g := by
    have : g ∈ C2ppPrincipalAssembly.lsXiSubmodule ξ := by
      rw [hgeq]
      exact Submodule.sum_mem _ fun h _ =>
        Submodule.smul_mem _ _ (C2ppPrincipalAssembly.rightTranslate_mem_lsXiSubmodule hφ₁x h)
    exact this

  have hdx : IsLsXiFunction (𝓞 F) F ⊤ ξ (φ - g) :=
    ((C2ppPrincipalAssembly.lsXiSubmodule ξ).sub_mem (show φ ∈ C2ppPrincipalAssembly.lsXiSubmodule ξ from hφx) hgx)
  have hdc : Continuous (φ - g) := hφc.sub hgc
  have hdW : ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ, (‖(φ - g) x‖₊ : ℝ≥0∞) ^ 2
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε := by
    simpa only [Pi.sub_apply, hgdef] using hsl
  have hdΦ₀ : ∫⁻ x in Φ₀, (‖(φ - g) x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤ ENNReal.ofReal C * ε :=
    (hC (φ - g) hdx hdc).trans (mul_le_mul_right hdW.le _)
  have hεtop : ε < ⊤ := by
    refine ENNReal.div_lt_top ENNReal.ofReal_ne_top ?_
    simp
  have hdL2 : MemLp (φ - g) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) :=
    C2ppPrincipalAssembly.memLp_restrict_of_lintegral_lt_top hdc
      (lt_of_le_of_lt hdΦ₀ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hεtop))
  have hgL2 : MemLp g 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ₀) := by
    have := hφL2.sub hdL2
    simpa only [sub_sub_cancel] using this
  have hφmem : φ ∈ memberSubmodule F Φ₀ ξ := hφm.1.1.1
  have hgmem : g ∈ memberSubmodule F Φ₀ ξ := (mem_memberSubmodule_iff' F Φ₀ ξ g).mpr ⟨hgx, hgL2⟩

  set x : AdelicGL2 (𝓞 F) F → ℂ := ∑ h ∈ s, l h • rightConv F (rightTranslate F h φ₁) f with hxdef
  have hxV : x ∈ V :=
    Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _
      (AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep F Pp ξ tys V hV φ₁ hφ₁ h f hft hfbf)
  have hxU : x ∈ levelInvariantSubmodule F Pp N :=
    Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _
      (C2ppPrincipalAssembly.rightConv_mem_levelInvariantSubmodule N tys hfsph' _)
  have hxt : x ∈ archCutSubmodule F tys :=
    Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _
      (AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite F tys (rightTranslate F h φ₁)
        (continuous_rightTranslate F hφ₁c h) f hft hfbf)
  have hxm : x ∈ cuspMemberSubmodule F Φ₀ ξ := hS3 (hV.le hxV)
  have hxg : x = rightConv F g f := by
    rw [hxdef, hgdef, C2ppPrincipalAssembly.rightConv_sum_smul_rightTranslate hfc hfK hφ₁c s l]

  refine ⟨hφm, x, Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hxV, hxU⟩, hxt⟩, hxm, ?_⟩

  have hTφ := hTf.comm φ ⟨hφmem, hφc⟩
  have hTg := hTf.comm g ⟨hgmem, hgc⟩
  have hgfmem : rightConv F g f ∈ memberSubmodule F Φ₀ ξ := (hTf.mapsTo g ⟨hgmem, hgc⟩).1

  have h2 : ‖(toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφf⟩ : Carrier F Φ₀ σ) -
      (toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩ : Carrier F Φ₀ σ)‖ ≤ M * ‖toCarrier F hΦ₀ σ ξ ⟨φ - g, (memberSubmodule F Φ₀ ξ).sub_mem hφmem hgmem⟩‖ := by
    rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    have hx' : (⟨x, hxm.1.1.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ⟨rightConv F g f, hgfmem⟩ := Subtype.ext hxg
    have hφ' : (⟨rightConv F φ f, hφf.1.1.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) =
        ⟨rightConv F φ f, (hTf.mapsTo φ ⟨hφmem, hφc⟩).1⟩ := rfl
    rw [hx', hφ', ← hTφ, ← hTg, ← map_sub, ← map_sub]
    exact Tf.le_opNorm _

  have h3 : ‖toCarrier F hΦ₀ σ ξ ⟨φ - g, (memberSubmodule F Φ₀ ξ).sub_mem hφmem hgmem⟩‖ ≤ r := by
    rw [C2ppPrincipalAssembly.norm_toCarrier hΦ₀ σ ξ]
    have hsq : eLpNorm (φ - g) 2 (weightedMeasure F Φ₀ σ) ^ 2 ≤ ENNReal.ofReal r ^ 2 := by
      calc eLpNorm (φ - g) 2 (weightedMeasure F Φ₀ σ) ^ 2
          ≤ Cw * ∫⁻ x in Φ₀, (‖(φ - g) x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
            C2ppPrincipalAssembly.eLpNorm_weightedMeasure_sq_le hΦ₀ σ (φ - g)
        _ ≤ Cw * (ENNReal.ofReal C * ε) := mul_le_mul_right hdΦ₀ _
        _ = K * ε := by rw [hK, mul_assoc]
        _ ≤ ENNReal.ofReal (r ^ 2) := by
            rw [hεdef, ENNReal.div_eq_inv_mul, ← mul_assoc, mul_comm K, mul_assoc, ← ENNReal.div_eq_inv_mul,
              ENNReal.div_le_iff (by simp) hKtop]
            calc K * ENNReal.ofReal (r ^ 2) ≤ (K + 1) * ENNReal.ofReal (r ^ 2) := mul_le_mul_left le_self_add _
              _ = ENNReal.ofReal (r ^ 2) * (K + 1) := mul_comm _ _
        _ = ENNReal.ofReal r ^ 2 := ENNReal.ofReal_pow hrpos.le 2
    have hle : eLpNorm (φ - g) 2 (weightedMeasure F Φ₀ σ) ≤ ENNReal.ofReal r :=
      (ENNReal.pow_le_pow_left_iff two_ne_zero).mp hsq
    exact ENNReal.toReal_le_of_le_ofReal hrpos.le hle

  have h4 : M * ‖toCarrier F hΦ₀ σ ξ ⟨φ - g, (memberSubmodule F Φ₀ ξ).sub_mem hφmem hgmem⟩‖ < δ / 2 := by
    calc M * ‖toCarrier F hΦ₀ σ ξ ⟨φ - g, (memberSubmodule F Φ₀ ξ).sub_mem hφmem hgmem⟩‖ ≤ M * r :=
          mul_le_mul_of_nonneg_left h3 hM0
      _ < δ / 2 := by
          rw [hr]
          have hM1 : 0 < M + 1 := by positivity
          rw [show M * (δ / (2 * (M + 1))) = (δ / 2) * (M / (M + 1)) by field_simp]
          exact mul_lt_of_lt_one_right (half_pos hδ) ((div_lt_one hM1).mpr (lt_add_one M))
  calc ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩‖
      ≤ ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφf⟩‖ +
        ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφf⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ / 2 + δ / 2 := by
        exact add_lt_add hφfδ (lt_of_le_of_lt h2 h4)
    _ = δ := add_halves δ

end S_AutomorphicForm_CuspidalSpectrum_exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt_principal (solution)
