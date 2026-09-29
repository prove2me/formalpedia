-- Prove2me | solution 1 for AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/109472c1-ff78-5d97-b9e2-49131cd079fc

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample
import Theorems.Thm_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_AutomorphicForm_exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le
import Theorems.Thm_AutomorphicForm_norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply"
p2m_attr_erase "simp" "ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.AdelicVolume"
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsGenuineCuspRealizationAt CarrierPins productionPinsOf AdelicGL2 centralScalar IsLsXiFunction finiteAdelicGL2Subgroup LsXiMemberAt lsXiMemberAt_iff SmoothCuspRealizationAt HeckeEigensystem isotypicCuspSubmodule exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule memLp_iUnion_centreCutSiegelSet_of_detWindow_le norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre"
namespace WindowMultiplicityOne
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K]

private def plainW (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂

private def pinsW (K : Type) [Field K] [NumberField K] (D : Set (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K)

private theorem plainW_mono {c u u' d₁ d₂ : ℝ} (T : Finset (AdelicGL2 (𝓞 K) K)) (h : u ^ 2 ≤ u' ^ 2) :
    plainW K c u d₁ d₂ T ⊆ plainW K c u' d₁ d₂ T := by
  refine Set.iUnion₂_mono fun x _ => Set.image_mono fun g hg => ?_
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (mem_centreCutSiegelSet_iff (F := K)).mp hg
  exact (mem_centreCutSiegelSet_iff (F := K)).mpr ⟨h₁, h₂, fun w => le_trans (h₃ w) h, h₄⟩

section Transport

variable {D D' : Set (AdelicGL2 (𝓞 K) K)} {Φ : HeckeEigensystem K ℂ}

private def transport (R : SmoothCuspRealizationAt K (pinsW K D) Φ)
    (hL2 : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D')) :
    SmoothCuspRealizationAt K (pinsW K D') Φ where
  toFun := R.toFun
  exists_ne_zero := R.exists_ne_zero
  centralChar := R.centralChar
  smoothCusp := by
    refine ⟨⟨?_, R.smoothCusp.1.2⟩, R.smoothCusp.2⟩
    have h : LsXiMemberAt (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)
        R.centralChar D R.toFun := R.smoothCusp.1.1
    have h' : LsXiMemberAt (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)
        R.centralChar D' R.toFun :=
      (lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mpr ⟨((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mp h).1, hL2⟩
    exact h'
  level_invariant := R.level_invariant
  exceptionalSet := R.exceptionalSet
  hecke_eigen := R.hecke_eigen
  central_eigen := R.central_eigen

private theorem transport_toFun (R : SmoothCuspRealizationAt K (pinsW K D) Φ)
    (hL2 : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D')) :
    (transport R hL2).toFun = R.toFun := rfl

private theorem isGenuine_transport (R : SmoothCuspRealizationAt K (pinsW K D) Φ)
    (hR : IsGenuineCuspRealizationAt K (pinsW K D) Φ R)
    (hL2 : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D')) :
    IsGenuineCuspRealizationAt K (pinsW K D') Φ (transport R hL2) := hR

end Transport

section MassAdapter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem eLpNorm_two_pow_two (f : α → ℂ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, one_div,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat, inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one]
  congr 1; funext x
  rw [← ENNReal.rpow_natCast, enorm_eq_nnnorm]; norm_num

private theorem memLp_of_lintegral_ne_top [TopologicalSpace α] [OpensMeasurableSpace α] {f : α → ℂ}
    (hf : Continuous f) {D : Set α} (hD : (∫⁻ x in D, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≠ ⊤) :
    MemLp f 2 (μ.restrict D) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [lt_top_iff_ne_top]
  intro htop
  apply hD
  rw [← eLpNorm_two_pow_two, htop, ENNReal.top_pow two_ne_zero]

private theorem lintegral_ne_top_of_memLp {f : α → ℂ} {D : Set α} (hf : MemLp f 2 (μ.restrict D)) :
    (∫⁻ x in D, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) ≠ ⊤ := by
  rw [← eLpNorm_two_pow_two]
  exact ENNReal.pow_ne_top hf.eLpNorm_ne_top

end MassAdapter

section Members

private theorem continuous_and_memLp_of_mem {D : Set (AdelicGL2 (𝓞 K) K)} {ξ : (pinsW K D).Z →* ℂˣ}
    {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : f ∈ isotypicCuspSubmodule K (pinsW K D) ξ N S Φ) :
    Continuous f ∧ MemLp f 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D) := by
  induction hf using Submodule.span_induction with
  | mem φ hφ =>
    refine ⟨hφ.continuous, ?_⟩
    have h : LsXiMemberAt (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)
        ξ D φ := hφ.smoothCusp.1.1
    exact ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mp h).2
  | zero => exact ⟨continuous_const, MemLp.zero⟩
  | add φ ψ _ _ hφ hψ => exact ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  | smul a φ _ hφ => exact ⟨hφ.1.const_smul a, hφ.2.const_smul a⟩

end Members

section Transfer

private theorem lintegral_plainW_ne_top (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c)
    (hd : d₁ < d₂) (hcov : CoversModCentre K (plainW K c u d₁ d₂ T)) (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ.toRawCentral R)
    (u' d d' : ℝ) (hd0 : 0 < d) :
    (∫⁻ x in plainW K c u' d d' T, (‖R.toFun x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ≠ ⊤ := by
  have hRc : Continuous R.toFun := hR
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
  have hmem := R.toFun_mem_isotypicCuspSubmodule hRc
  have hmem₀ :
      R.toFun ∈ isotypicCuspSubmodule K (pinsW K Φ₀) R.centralChar Θ.level R.exceptionalSet Θ :=
    isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab K c u d₁ d₂ T hd hcov 1 2
      one_pos
      Φ₀ hΦ₀s hΦ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (adelicBox K) R.centralChar Θ.level R.exceptionalSet Θ hmem
  obtain ⟨φ, hφmem, hφK, hφt, hφM⟩ :=
    exists_isArchKFinite_tendsto_and_setLIntegral_le_of_mem_isotypicCuspSubmodule K 1 2 Φ₀ hΦ₀ hΦ₀s
      R.centralChar Θ.level R.exceptionalSet Θ R.toFun hmem₀
  obtain ⟨C, hCtop, hC⟩ :=
    exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule K c u' d d' T
      hc hd0 1 2 two_pos one_lt_two Φ₀ hΦ₀ R.centralChar Θ.level Θ.level_ne_bot R.exceptionalSet Θ

  have hM : (∫⁻ x in Φ₀, (‖R.toFun x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ≠ ⊤ :=
    lintegral_ne_top_of_memLp (continuous_and_memLp_of_mem hmem₀).2

  have hφc : ∀ n, Continuous (φ n) := fun n => (continuous_and_memLp_of_mem (hφmem n)).1
  have hmeas : ∀ n, Measurable fun x => (‖φ n x‖₊ : ℝ≥0∞) ^ 2 := fun n =>
    ((hφc n).measurable.nnnorm.coe_nnreal_ennreal).pow_const 2

  have hpt : ∀ x, Filter.Tendsto (fun n => (‖φ n x‖₊ : ℝ≥0∞) ^ 2) Filter.atTop
      (nhds ((‖R.toFun x‖₊ : ℝ≥0∞) ^ 2)) := fun x =>
    ((ENNReal.continuous_pow 2).tendsto _).comp
      ((ENNReal.continuous_coe.tendsto _).comp ((continuous_nnnorm.tendsto _).comp (hφt x)))

  have hF : (∫⁻ x in plainW K c u' d d' T, (‖R.toFun x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
      ≤ C * ∫⁻ x in Φ₀, (‖R.toFun x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    calc (∫⁻ x in plainW K c u' d d' T, (‖R.toFun x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
        = ∫⁻ x in plainW K c u' d d' T, Filter.liminf (fun n => (‖φ n x‖₊ : ℝ≥0∞) ^ 2) Filter.atTop
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
          lintegral_congr fun x => ((hpt x).liminf_eq).symm
      _ ≤ Filter.liminf (fun n => ∫⁻ x in plainW K c u' d d' T, (‖φ n x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) Filter.atTop :=
          lintegral_liminf_le fun n => hmeas n
      _ ≤ C * ∫⁻ x in Φ₀, (‖R.toFun x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
          refine Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun n => ?_)
          exact (hC (φ n) (hφmem n) (hφK n)).trans (mul_le_mul' le_rfl (hφM n))
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hCtop hM) hF

end Transfer

section CoveringSlice

private theorem exists_setLIntegral_sub_sum_translate_sq_lt_of_pos_of_coveringRadius
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂) (hc : 0 < c)
    (hu : ∀ x : (w : InfinitePlace K) → w.Completion, ∃ ξ : 𝓞 K, ∀ w : InfinitePlace K,
        ‖x w - algebraMap K w.Completion (ξ : K)‖ ≤ u)
    (hcov : CoversModCentre K (plainW K c u d₁ d₂ T))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ'.toRawCentral R') :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        ∫⁻ y in plainW K c u d₁ d₂ T,
            (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε := by
  obtain ⟨u', d₁', κ, hd₁', hlt, hκ, hamp, ⟨Rκ, hRκ, hRκf⟩, ⟨R'κ, hR'κ, hR'κf⟩, himp⟩ :=
    exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre
      K c u d₁ d₂ T hd hc hu hcov Θ Θ' hΘ R hR R' hR'
  refine himp fun δ hδ => ?_
  have h := exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample
    K c u' d₁' d₂ κ T hlt hκ hc hd₁' hamp Θ Θ' hΘ Rκ hRκ R'κ hR'κ δ hδ
  rwa [hRκf, hR'κf] at h

end CoveringSlice

section OwnedBricks

section CoveringRadius

open NumberField.InfinitePlace NumberField.mixedEmbedding

private noncomputable def mixedOfCompletions (K : Type) [Field K] [NumberField K]
    (x : (w : InfinitePlace K) → w.Completion) : mixedSpace K :=
  (fun w => Completion.extensionEmbeddingOfIsReal w.prop (x w.val),
    fun w => Completion.extensionEmbedding w.val (x w.val))

private theorem normAtPlace_mixedOfCompletions_sub (K : Type) [Field K] [NumberField K]
    (x : (w : InfinitePlace K) → w.Completion) (a : K) (w : InfinitePlace K) :
    normAtPlace w (mixedOfCompletions K x - mixedEmbedding K a) = ‖x w - algebraMap K w.Completion a‖ := by
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, Prod.fst_sub, Pi.sub_apply, mixedEmbedding_apply_isReal]
    have hcoe : embedding_of_isReal hw a
        = Completion.extensionEmbeddingOfIsReal hw (algebraMap K w.Completion a) := by
      rw [show algebraMap K w.Completion a = ((WithAbs.equiv w.1).symm a : w.Completion) from rfl,
        Completion.extensionEmbeddingOfIsReal_coe, RingEquiv.apply_symm_apply]
    rw [hcoe]
    show ‖Completion.extensionEmbeddingOfIsReal hw (x w) - Completion.extensionEmbeddingOfIsReal hw _‖ = _
    rw [← map_sub, (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)]
  · rw [normAtPlace_apply_of_isComplex hw, Prod.snd_sub, Pi.sub_apply, mixedEmbedding_apply_isComplex]
    have hcoe : w.embedding a = Completion.extensionEmbedding w (algebraMap K w.Completion a) := by
      rw [show algebraMap K w.Completion a = ((WithAbs.equiv w.1).symm a : w.Completion) from rfl,
        Completion.extensionEmbedding_coe, RingEquiv.apply_symm_apply]
    rw [hcoe]
    show ‖Completion.extensionEmbedding w (x w) - Completion.extensionEmbedding w _‖ = _
    rw [← map_sub, (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]

open scoped Classical in

private theorem exists_integer_norm_sub_le (K : Type) [Field K] [NumberField K] :
    ∃ R : ℝ, ∀ v : mixedSpace K, ∃ ξ : 𝓞 K, ‖v - mixedEmbedding K (ξ : K)‖ ≤ R := by
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded (latticeBasis K)).exists_norm_le
  refine ⟨R, fun v => ?_⟩
  have hfloor := (ZSpan.floor (latticeBasis K) v).property
  rw [mem_span_latticeBasis] at hfloor
  obtain ⟨ξ, hξ⟩ := hfloor
  refine ⟨ξ, ?_⟩
  have hfract : v - mixedEmbedding K (ξ : K) = ZSpan.fract (latticeBasis K) v := by
    rw [ZSpan.fract_apply, ← hξ]
    rfl
  rw [hfract]
  exact hR _ (ZSpan.fract_mem_fundamentalDomain _ v)

private theorem exists_coveringRadius (K : Type) [Field K] [NumberField K] :
    ∃ u₀ : ℝ, ∀ x : (w : InfinitePlace K) → w.Completion, ∃ ξ : 𝓞 K, ∀ w : InfinitePlace K,
      ‖x w - algebraMap K w.Completion (ξ : K)‖ ≤ u₀ := by
  classical
  obtain ⟨R, hR⟩ := exists_integer_norm_sub_le K
  refine ⟨R, fun x => ?_⟩
  obtain ⟨ξ, hξ⟩ := hR (mixedOfCompletions K x)
  refine ⟨ξ, fun w => ?_⟩
  rw [← normAtPlace_mixedOfCompletions_sub K x (ξ : K) w]
  refine le_trans ?_ hξ
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => normAtPlace w (mixedOfCompletions K x - mixedEmbedding K (ξ : K)))
    (Finset.mem_univ w)

end CoveringRadius

private theorem memLp_plainW_of_memLp_quarter (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂) (hcov : CoversModCentre K (plainW K c u d₁ d₂ T)) (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ.toRawCentral R) (u' : ℝ)
    (hq : MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW K c u' (d₂ / 4) d₂ T))) :
    MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW K c u' d₁ d₂ T)) := by
  have hRfun : IsLsXiFunction (𝓞 K) K ⊤ R.centralChar R.toFun :=
    ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mp R.smoothCusp.1.1).1
  have hRL2 : MemLp R.toFun 2
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) :=
    ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _).mp R.smoothCusp.1.1).2
  have hRc : Continuous R.toFun := hR
  let χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ :=
    { toFun := fun z => R.centralChar ⟨z, Subgroup.mem_top z⟩
      map_one' := R.centralChar.map_one
      map_mul' := fun a b => R.centralChar.map_mul ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩ }
  have hχ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      R.toFun (centralScalar (𝓞 K) K z * g) = ((χ z : ℂˣ) : ℂ) * R.toFun g :=
    fun z g => hRfun.central_transform ⟨z, Subgroup.mem_top z⟩ g
  unfold plainW at hcov hq ⊢
  exact memLp_iUnion_centreCutSiegelSet_of_detWindow_le K c u' d₁ d₂ (d₂ / 4) T (by positivity) (by linarith)
    (by linarith) R.toFun hRc.measurable.aestronglyMeasurable χ hχ
    (fun _ w a ha => norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre K c u d₁ d₂ T hd₁ hd₂ hcov
      R.toFun hRc R.exists_ne_zero hRfun.left_invariant χ hχ hRL2 w a ha)
    hq

end OwnedBricks

section ThinSlice

private theorem memLp_plainW_of_realization (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd : d₁ < d₂) (hd₂ : 0 < d₂) (hcov : CoversModCentre K (plainW K c u d₁ d₂ T))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K (pinsW K (plainW K c u d₁ d₂ T)) Θ.toRawCentral R) (u' : ℝ) :
    MemLp R.toFun 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (plainW K c u' d₁ d₂ T)) := by
  have hRc : Continuous R.toFun := hR
  refine memLp_of_lintegral_ne_top hRc ?_
  by_cases hd₁ : 0 < d₁
  · exact lintegral_plainW_ne_top c u d₁ d₂ T hc hd hcov Θ R hR u' d₁ d₂ hd₁
  · have hq := lintegral_plainW_ne_top c u d₁ d₂ T hc hd hcov Θ R hR u' (d₂ / 4) d₂ (by positivity)
    exact lintegral_ne_top_of_memLp (memLp_plainW_of_memLp_quarter c u d₁ d₂ T (not_lt.mp hd₁) hd₂ hcov Θ R hR
      u' (memLp_of_lintegral_ne_top hRc hq))

end ThinSlice

end AutomorphicForm.WindowMultiplicityOne

end

open AutomorphicForm.WindowMultiplicityOne in

theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
            (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε := by
  by_cases hc : 0 < c
  ·
    obtain ⟨u₀, hu₀⟩ := exists_coveringRadius K
    set uf : ℝ := max |u| |u₀| with huf
    have hu : ∀ x : (w : InfinitePlace K) → w.Completion, ∃ ξ : 𝓞 K, ∀ w : InfinitePlace K,
        ‖x w - algebraMap K w.Completion (ξ : K)‖ ≤ uf := fun x => by
      obtain ⟨ξ, hξ⟩ := hu₀ x
      exact ⟨ξ, fun w => (hξ w).trans ((le_abs_self u₀).trans (le_max_right _ _))⟩
    have husq : u ^ 2 ≤ uf ^ 2 := by
      rw [← sq_abs u]
      exact pow_le_pow_left₀ (abs_nonneg u) (le_max_left _ _) 2
    have hsub : plainW K c u d₁ d₂ T ⊆ plainW K c uf d₁ d₂ T := plainW_mono T husq
    have hcovf : CoversModCentre K (plainW K c uf d₁ d₂ T) := CoversModCentre.mono hsub hcov

    have hd₂ : 0 < d₂ := by
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
      obtain ⟨γ, z, hmem⟩ := hcov 1
      obtain ⟨x, -, g, hg, -⟩ := Set.mem_iUnion₂.mp hmem
      exact lt_of_lt_of_le (archDetNorm_pos w g) (((mem_centreCutSiegelSet_iff (F := K)).mp hg).2.2.2 w).2
    have hL2 := memLp_plainW_of_realization c u d₁ d₂ T hc hd hd₂ hcov Θ R hR uf
    have hL2' := memLp_plainW_of_realization c u d₁ d₂ T hc hd hd₂ hcov Θ' R' hR' uf

    have h := exists_setLIntegral_sub_sum_translate_sq_lt_of_pos_of_coveringRadius c uf d₁ d₂ T hd hc hu
      hcovf Θ Θ' hΘ (transport R hL2) (isGenuine_transport R hR hL2) (transport R' hL2')
      (isGenuine_transport R' hR' hL2')
    intro ε hε
    obtain ⟨s, l, hsl⟩ := h ε hε
    exact ⟨s, l, (lintegral_mono_set hsub).trans_lt hsl⟩
  · exact absurd ⟨R, hR⟩ (not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre K c u d₁ d₂ T
      (not_lt.mp hc) hd hcov Θ)

end S_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre (solution)
