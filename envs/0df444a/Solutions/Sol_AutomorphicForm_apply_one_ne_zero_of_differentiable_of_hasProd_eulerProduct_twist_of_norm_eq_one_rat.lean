-- Prove2me | solution 1 for AutomorphicForm.apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/28401d2d-69d8-5913-a369-d0cc408fbe85

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one
import Theorems.Thm_NumberField_exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow
import Theorems.Thm_AutomorphicForm_exists_finset_neg_analyticAt_ofReal_hasProd_rsEulerPoly_self_div_sub_one_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.instT2SpaceAdeleRing IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension FLT.SpectralSide.instCompactSpaceMatrix IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero"
p2m_attr_erase "simp" "LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.deltaLiftSystem_level LanglandsTunnell.deltaLiftSystem_toRawCentral AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.preimage_mulLeft_smul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq AutomorphicForm.WhittakerModel.archFnAt_zero AutomorphicForm.WhittakerModel.localFnAt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul"
p2m_attr_erase "simp" "RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal Polynomial
open LanglandsTunnell.RankinSelberg

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsArithGenuineCuspRealizable WindowedSiegel.mem_centreCutSiegelSet_iff productionPinsOf AdelicGL2 IsIdeleClassChar finiteAdelicGL2Subgroup HeckeEigensystem SiegelCovering.not_coversModCentre_empty uniformizerIdele not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one exists_finset_neg_analyticAt_ofReal_hasProd_rsEulerPoly_self_div_sub_one_rat"
namespace R1Assembly
p2m_open "AutomorphicForm"

open scoped Classical

theorem rsEulerPoly_twist (u a b : ℂ) (hu : u ≠ 0) (hb : b ≠ 0) :
    rsEulerPoly ((u * a) / (u ^ 2 * b)) (u ^ 2 * b)⁻¹ (u * a) (u ^ 2 * b) 0
      = rsEulerPoly (a / b) b⁻¹ a b 0 := by
  simp only [rsEulerPoly]
  ext n
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, mul_ite, mul_one, mul_zero]
  rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> simp <;> field_simp

theorem conj_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ :=
  (Complex.inv_eq_conj hz).symm

theorem conj_natCast_cpow (n : ℕ) (s : ℂ) : (starRingEnd ℂ) ((n : ℂ) ^ s) = (n : ℂ) ^ ((starRingEnd ℂ) s) := by
  have h := Complex.cpow_conj (n : ℂ) s (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne)
  rw [Complex.conj_natCast] at h
  exact h.symm

theorem hasProd_cexp_of_hasSum {ι : Type} {f : ι → ℂ} {a : ℂ} (h : HasSum f a) :
    HasProd (fun i => Complex.exp (f i)) (Complex.exp a) := h.cexp

theorem exists_differentiable_eq_sub_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z₀ : ℂ) (h0 : f z₀ = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z : ℂ, f z = (z - z₀) * g z := by
  refine ⟨dslope f z₀, ?_, ?_⟩
  · intro z
    by_cases hz : z = z₀
    · subst hz
      obtain ⟨p, hp⟩ := hf.analyticAt z
      exact (hp.has_fpower_series_dslope_fslope).analyticAt.differentiableAt
    · exact (differentiableAt_dslope_of_ne hz).mpr (hf z)
  · intro z
    by_cases hz : z = z₀
    · subst hz; simp [h0]
    · have := sub_smul_dslope f z₀ z
      rw [smul_eq_mul, h0, sub_zero] at this
      exact this.symm

theorem peel {ι : Type} {f : ι → ℂ} {S S' : Finset ι} (hSS' : S ⊆ S') {a : ℂ}
    (h : HasProd (fun i : {i : ι // i ∉ S} => f i.1) a) (hne : ∀ i ∈ S', i ∉ S → f i ≠ 0) :
    HasProd (fun i : {i : ι // i ∉ S'} => f i.1) (a / ∏ i ∈ S' \ S, f i) := by
  have h1 : HasProd (((↑S : Set ι)ᶜ).mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := (↑S : Set ι)ᶜ) (f := f)).mp h
  refine (hasProd_subtype_iff_mulIndicator (s := (↑S' : Set ι)ᶜ) (f := f)).mpr ?_
  set g : ι → ℂ := (↑(S' \ S) : Set ι).mulIndicator (fun i => (f i)⁻¹) with hg
  have hfin : HasProd g (∏ i ∈ S' \ S, g i) :=
    hasProd_prod_of_ne_finset_one (fun i hi => Set.mulIndicator_of_notMem (by simpa using hi) _)
  have hgprod : ∏ i ∈ S' \ S, g i = ∏ i ∈ S' \ S, (f i)⁻¹ :=
    Finset.prod_congr rfl (fun i hi => Set.mulIndicator_of_mem (by simpa using hi) _)
  rw [hgprod] at hfin
  have h2 := h1.mul hfin
  convert h2 using 1
  · funext i
    simp only [hg, Set.mulIndicator_apply, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff]
    by_cases hiS : i ∈ S
    · simp [hiS, hSS' hiS]
    · by_cases hiS' : i ∈ S'
      · simp [hiS, hiS', mul_inv_cancel₀ (hne i hiS' hiS)]
      · simp [hiS, hiS']
  · rw [div_eq_mul_inv, Finset.prod_inv_distrib]

theorem peel_inv {ι : Type} {g : ι → ℂ} {S S' : Finset ι} (hSS' : S ⊆ S') {a : ℂ}
    (h : HasProd (fun i : {i : ι // i ∉ S} => (g i.1)⁻¹) a) (hne : ∀ i ∈ S', i ∉ S → g i ≠ 0) :
    HasProd (fun i : {i : ι // i ∉ S'} => (g i.1)⁻¹) (a * ∏ i ∈ S' \ S, g i) := by
  have := peel (f := fun i => (g i)⁻¹) hSS' h (fun i hi hi' => inv_ne_zero (hne i hi hi'))
  rwa [Finset.prod_inv_distrib, div_inv_eq_mul] at this

theorem peel_inv₀ {ι : Type} {g : ι → ℂ} (S' : Finset ι) {a : ℂ}
    (h : HasProd (fun i => (g i)⁻¹) a) (hne : ∀ i ∈ S', g i ≠ 0) :
    HasProd (fun i : {i : ι // i ∉ S'} => (g i.1)⁻¹) (a * ∏ i ∈ S', g i) := by
  have h' : HasProd (fun i : {i : ι // i ∉ (∅ : Finset ι)} => (g i.1)⁻¹) a :=
    (hasProd_subtype_iff_of_mulSupport_subset (f := fun i => (g i)⁻¹)
      (s := ((↑(∅ : Finset ι) : Set ι)ᶜ)) (by simp)).mpr h
  simpa using peel_inv (Finset.empty_subset S') h' (fun i hi _ => hne i hi)

theorem norm_natCast_cpow_neg_lt {n : ℕ} (hn : 1 < (n : ℝ)) {s : ℂ} (hs : 1 < s.re) :
    ‖(n : ℂ) ^ (-s)‖ < ((n : ℝ))⁻¹ := by
  have hn0 : 0 < n := by exact_mod_cast (zero_lt_one.trans hn)
  rw [Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re, ← Real.rpow_neg_one]
  exact Real.rpow_lt_rpow_of_exponent_lt hn (by linarith)

theorem norm_natCast_cpow_neg {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]

theorem exists_forall_eval_natCast_cpow_neg_ne_zero (p : ℂ[X]) (hp : p.eval 0 ≠ 0) {n : ℕ} (hn : 1 < (n : ℝ)) :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re → p.eval ((n : ℂ) ^ (-s)) ≠ 0 := by

  have hc : ContinuousAt (fun y : ℂ => p.eval y) 0 := p.continuous.continuousAt
  have hopen : ∀ᶠ y in nhds (0 : ℂ), p.eval y ≠ 0 := hc.eventually_ne hp
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hopen

  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans hn
  have ht : Filter.Tendsto (fun σ : ℝ => ((n : ℝ)⁻¹) ^ σ) Filter.atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one _ (by linarith [inv_pos.mpr hn0]) (inv_lt_one_of_one_lt₀ hn)
  obtain ⟨σ₁, hσ₁⟩ := (Filter.tendsto_atTop'.mp ht) (Set.Iio δ) (Iio_mem_nhds hδ)
  refine ⟨σ₁, fun s hs => hball ?_⟩
  rw [dist_zero_right, norm_natCast_cpow_neg (by exact_mod_cast hn0) s, Real.rpow_neg hn0.le, ← Real.inv_rpow hn0.le]
  exact hσ₁ s.re hs.le

end AutomorphicForm.R1Assembly

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat.AutomorphicForm in
open scoped Classical in

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (hΦ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Φ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 ℚ) ℚ χ) (hχc : Continuous χ)
    (S₁ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hnorm : ∀ v ∉ S₁, IsUnramifiedCharAt χ v →
      ‖(((χ (uniformizerIdele ℚ v)) ^ 2 : ℂˣ) : ℂ) * Φ.b v‖ = 1) :
    ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (σ₀ : ℝ) (Λ : ℂ → ℂ),
      Differentiable ℂ Λ →
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele ℚ v.1) : ℂˣ) : ℂ) * Φ.a v.1) * X
              + C ((((χ (uniformizerIdele ℚ v.1)) ^ 2 : ℂˣ) : ℂ) * Φ.b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) →
      Λ 1 ≠ 0 := by
  intro S σ₀ Λ hΛ hprod h1

  obtain ⟨Nv, hNv⟩ : ∃ Nv : HeightOneSpectrum (𝓞 ℚ) → ℂ,
      ∀ v, Nv v = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨uχ, huχ⟩ : ∃ uχ : HeightOneSpectrum (𝓞 ℚ) → ℂ,
      ∀ v, uχ v = ((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨ua, hua⟩ : ∃ ua : HeightOneSpectrum (𝓞 ℚ) → ℂ,
      ∀ v, ua v = ((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) * Φ.a v := ⟨_, fun _ => rfl⟩
  obtain ⟨ub, hub⟩ : ∃ ub : HeightOneSpectrum (𝓞 ℚ) → ℂ,
      ∀ v, ub v = (((χ (uniformizerIdele ℚ v)) ^ 2 : ℂˣ) : ℂ) * Φ.b v := ⟨_, fun _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : HeightOneSpectrum (𝓞 ℚ) → ℂ[X], ∀ v, P v =
      (if IsUnramifiedCharAt χ v
        then C 1 - C (((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ) * Φ.a v) * X
          + C ((((χ (uniformizerIdele ℚ v)) ^ 2 : ℂˣ) : ℂ) * Φ.b v) * X ^ 2
        else C 1 : ℂ[X]) := ⟨_, fun _ => rfl⟩
  obtain ⟨RS, hRS⟩ : ∃ RS : HeightOneSpectrum (𝓞 ℚ) → ℂ[X], ∀ v, RS v =
      rsEulerPoly (Φ.a v / Φ.b v) (Φ.b v)⁻¹ (Φ.a v) (Φ.b v) 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : HeightOneSpectrum (𝓞 ℚ) → ℂ → ℂ, ∀ v y, Q v y =
      (1 - y) * (1 - ua v * y + ub v * y ^ 2) * (1 - (ua v / ub v) * y + (ub v)⁻¹ * y ^ 2) *
        (rsEulerPoly (ua v / ub v) (ub v)⁻¹ (ua v) (ub v) 0).eval y := ⟨_, fun _ _ => rfl⟩
  have hprod' : ∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} => ((P v.1).eval (Nv v.1 ^ (-s)))⁻¹) (Λ s) := by
    intro s hs
    simpa only [hP, hNv] using hprod s hs
  have hNv1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    have h1' : Ideal.absNorm v.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top
    have : 1 < Ideal.absNorm v.asIdeal := by omega
    exact_mod_cast this
  have hNv0 : ∀ v : HeightOneSpectrum (𝓞 ℚ), Nv v ≠ 0 := fun v => by
    rw [hNv]; exact Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

  have hc : 0 < c := by
    by_contra hc
    exact AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
      ℚ c u d₁ d₂ T (not_lt.mp hc) hd hcov Φ hΦ
  have hd₂ : 0 < d₂ := by
    by_contra hle
    apply AutomorphicForm.SiegelCovering.not_coversModCentre_empty (F := ℚ)
    convert hcov using 2
    symm
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hg
    obtain ⟨x, -, y, hy, -⟩ := hg
    obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace ℚ))
    have h4 := ((AutomorphicForm.WindowedSiegel.mem_centreCutSiegelSet_iff.mp hy).2.2.2 w₀).2
    have hpos := NumberField.AdelicVolume.archDetNorm_pos w₀ y
    linarith
  have hd₁' : 0 < max d₁ (d₂ / 2) := lt_max_of_lt_right (by linarith)
  have hle : d₁ ≤ max d₁ (d₂ / 2) := le_max_left _ _
  have hd' : max d₁ (d₂ / 2) < d₂ := max_lt hd (by linarith)
  obtain ⟨hcov', hΦ'⟩ :=
    AutomorphicForm.coversModCentre_and_isArithGenuineCuspRealizable_of_le_of_lt_of_coversModCentre
      ℚ c u d₁ d₂ (max d₁ (d₂ / 2)) T hle hd' hcov Φ hΦ

  obtain ⟨S_RS, σ_RS, x, hx, A, hA, hAprod⟩ :=
    AutomorphicForm.exists_finset_neg_analyticAt_ofReal_hasProd_rsEulerPoly_self_div_sub_one_rat
      c u (max d₁ (d₂ / 2)) d₂ T hc hd₁' hd' hcov' Φ hΦ'
  have hAprod' : ∀ s : ℂ, σ_RS < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S_RS} => ((RS v.1).eval (Nv v.1 ^ (-s)))⁻¹)
        (A s / (s - 1)) := by
    intro s hs
    simpa only [hRS, hNv] using hAprod s hs

  obtain ⟨S_U, hU⟩ :=
    LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable_of_coversModCentre
      ℚ c u (max d₁ (d₂ / 2)) d₂ T hc hd₁' hd' hcov' Φ hΦ'

  obtain ⟨S₂, hconj⟩ :=
    AutomorphicForm.exists_finset_forall_conj_mul_a_eq_div_of_isArithGenuineCuspRealizable_of_norm_twist_b_eq_one
      ℚ c u d₁ d₂ T hd hcov Φ hΦ χ hχ hχc S₁ hnorm

  obtain ⟨S_ram, hram⟩ :=
    NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous ℚ χ hχc

  obtain ⟨𝔭, h𝔭⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let v₀ : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨𝔭, h𝔭.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField ℚ)⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Finset (HeightOneSpectrum (𝓞 ℚ)),
      S' = S ∪ S₁ ∪ S₂ ∪ S_U ∪ S_RS ∪ S_ram ∪ {v₀} := ⟨_, rfl⟩
  have hSS' : S ⊆ S' := by rw [hS']; intro v hv; simp [hv]
  have hS_RS' : S_RS ⊆ S' := by rw [hS']; intro v hv; simp [hv]
  have hv₀ : v₀ ∈ S' := by rw [hS']; simp
  have hout : ∀ v ∉ S', v ∉ S ∧ v ∉ S₁ ∧ v ∉ S₂ ∧ v ∉ S_U ∧ v ∉ S_RS ∧ v ∉ S_ram := by
    intro v hv; rw [hS'] at hv; simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hv; tauto
  have hunr : ∀ v ∉ S', IsUnramifiedCharAt χ v := fun v hv => hram v (hout v hv).2.2.2.2.2
  have hb1 : ∀ v ∉ S', ‖ub v‖ = 1 := fun v hv => by
    rw [hub]; exact hnorm v (hout v hv).2.1 (hunr v hv)
  have hub0 : ∀ v ∉ S', ub v ≠ 0 := fun v hv h => by simpa [h] using hb1 v hv
  have hPv : ∀ v ∉ S', P v = C 1 - C (ua v) * X + C (ub v) * X ^ 2 := fun v hv => by
    rw [hP, if_pos (hunr v hv), hua, hub]
  have hconj_a : ∀ v ∉ S', (starRingEnd ℂ) (ua v) = ua v / ub v := fun v hv => by
    rw [hua, hub]
    exact hconj v (by rw [Finset.mem_union, not_or]; exact ⟨(hout v hv).2.1, (hout v hv).2.2.1⟩) (hunr v hv)
  have hconj_b : ∀ v ∉ S', (starRingEnd ℂ) (ub v) = (ub v)⁻¹ := fun v hv =>
    AutomorphicForm.R1Assembly.conj_eq_inv_of_norm_eq_one (hb1 v hv)

  have hK1 : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ cv : ℕ → ℝ, cv 0 = 0 ∧ (∀ m : ℕ, 0 ≤ cv m) ∧
      (∀ m : ℕ, cv m ≤ 9 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ m) ∧
      (v ∈ S' → ∀ m : ℕ, cv m = 0) ∧
      (v ∉ S' → ∀ y : ℂ, ‖y‖ < (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ →
        Summable (fun m : ℕ => (cv m : ℂ) * y ^ m) ∧
        Complex.exp (∑' m : ℕ, (cv m : ℂ) * y ^ m) = (Q v y)⁻¹) := by
    intro v
    by_cases hv : v ∈ S'
    · exact ⟨fun _ => 0, rfl, fun _ => le_rfl, fun m => by positivity, fun _ _ => rfl, fun h => absurd hv h⟩
    · have hab : ∃ t : ℝ, 0 ≤ t ∧ ua v ^ 2 = (t : ℂ) * ub v := by
        obtain ⟨t, ht, hta⟩ := (hU v (hout v hv).2.2.2.1).1
        refine ⟨t, ht, ?_⟩
        rw [hua, hub, mul_pow, hta, Units.val_pow_eq_pow_val]; ring
      have ha : ‖ua v‖ ^ 2 <
          ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 2 + (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := by
        have h2 := (hU v (hout v hv).2.2.2.1).2
        have hb := hb1 v hv
        rw [hub, norm_mul, Units.val_pow_eq_pow_val, norm_pow] at hb
        rw [hua, norm_mul, mul_pow]
        have hu2 : 0 < ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ)‖ ^ 2 := by
          rcases (sq_nonneg ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ)‖).lt_or_eq with h | h
          · exact h
          · rw [← h, zero_mul] at hb; exact absurd hb zero_ne_one
        calc ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ)‖ ^ 2 * ‖Φ.a v‖ ^ 2
            < ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ)‖ ^ 2 * (‖Φ.b v‖ *
                (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 2 + (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹)) :=
              mul_lt_mul_of_pos_left h2 hu2
          _ = (‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ)‖ ^ 2 * ‖Φ.b v‖) *
                (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 2 + (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹) := by ring
          _ = _ := by rw [hb, one_mul]
      obtain ⟨cv, h0, hnn, hle9, hexp⟩ :=
        LanglandsTunnell.RankinSelberg.exists_nonneg_exp_tsum_mul_pow_eq_inv_one_sub_mul_std_mul_contragredient_mul_eval_rsEulerPoly_self_of_norm_eq_one
          (ua v) (ub v) (((Ideal.absNorm v.asIdeal : ℕ) : ℝ)) (hNv1 v) (hb1 v hv) hab ha
      refine ⟨cv, h0, hnn, hle9, fun h => absurd h hv, fun _ y hy => ?_⟩
      rw [hQ]
      exact hexp y hy
  choose cf hcf0 hcfnn hcfB hcfS' hcfexp using hK1

  obtain ⟨d, hdnn, hdabs, hdsum⟩ :=
    NumberField.exists_nonneg_abscissa_le_hasSum_tsum_mul_absNorm_cpow_eq_lseries_of_le_mul_pow
      ℚ cf hcf0 hcfnn 9 hcfB
  have hexpD : ∀ s : ℂ, 2 < s.re →
      LSeriesSummable (fun n => (d n : ℂ)) s ∧
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S'} => (Q v.1 (Nv v.1 ^ (-s)))⁻¹)
        (Complex.exp (LSeries (fun n => (d n : ℂ)) s)) := by
    intro s hs
    refine ⟨LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt hdabs (by exact_mod_cast hs)), ?_⟩
    have hall := (hdsum s hs).2.cexp
    refine (hasProd_subtype_iff_mulIndicator (s := (↑S' : Set (HeightOneSpectrum (𝓞 ℚ)))ᶜ)
      (f := fun v => (Q v (Nv v ^ (-s)))⁻¹)).mpr ?_
    convert hall using 1
    funext v
    simp only [Function.comp_apply, Set.mulIndicator_apply, Set.mem_compl_iff, Finset.mem_coe]
    by_cases hv : v ∈ S'
    · rw [if_neg (not_not_intro hv)]
      simp [hcfS' v hv]
    · rw [if_pos hv, hNv]
      exact ((hcfexp v hv _ (AutomorphicForm.R1Assembly.norm_natCast_cpow_neg_lt (hNv1 v)
        (by linarith))).2).symm

  obtain ⟨R, hR, hR1, hRζ, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero ℚ

  have h8a : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ σv : ℝ, ∀ s : ℂ, σv < s.re →
      (P v).eval (Nv v ^ (-s)) ≠ 0 ∧ (RS v).eval (Nv v ^ (-s)) ≠ 0 ∧ (1 - Nv v ^ (-s)) ≠ 0 := by
    intro v
    have hP0 : (P v).eval 0 ≠ 0 := by
      rw [hP]; split_ifs <;> simp
    have hRS0 : (RS v).eval 0 ≠ 0 := by
      rw [hRS]; simp [rsEulerPoly]
    have hX0 : (C 1 - X : ℂ[X]).eval 0 ≠ 0 := by simp
    obtain ⟨σ1, h1⟩ := AutomorphicForm.R1Assembly.exists_forall_eval_natCast_cpow_neg_ne_zero _ hP0 (hNv1 v)
    obtain ⟨σ2, h2⟩ := AutomorphicForm.R1Assembly.exists_forall_eval_natCast_cpow_neg_ne_zero _ hRS0 (hNv1 v)
    obtain ⟨σ3, h3⟩ := AutomorphicForm.R1Assembly.exists_forall_eval_natCast_cpow_neg_ne_zero _ hX0 (hNv1 v)
    refine ⟨max (max σ1 σ2) σ3, fun s hs => ?_⟩
    have hs1 : σ1 < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs
    have hs2 : σ2 < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs
    have hs3 : σ3 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
    refine ⟨?_, ?_, ?_⟩
    · rw [hNv]; exact h1 s hs1
    · rw [hNv]; exact h2 s hs2
    · have := h3 s hs3; rw [hNv]; simpa using this
  choose σv hσv using h8a
  obtain ⟨σ₂, hσ₂, hσ₂ne⟩ : ∃ σ₂ : ℝ, max (max 2 σ₀) σ_RS ≤ σ₂ ∧ ∀ s : ℂ, σ₂ < s.re → ∀ v ∈ S',
      (P v).eval (Nv v ^ (-s)) ≠ 0 ∧ (RS v).eval (Nv v ^ (-s)) ≠ 0 ∧ (1 - Nv v ^ (-s)) ≠ 0 := by
    obtain ⟨B, hB⟩ := (S'.image σv).bddAbove
    refine ⟨max (max (max 2 σ₀) σ_RS) B, le_max_left _ _, fun s hs v hv => hσv v s ?_⟩
    have : σv v ≤ B := hB (Finset.mem_image_of_mem σv hv)
    linarith [le_max_right (max (max 2 σ₀) σ_RS) B]
  have hσ₂' : ∀ s : ℂ, σ₂ < s.re → 2 < s.re ∧ σ₀ < s.re ∧ σ_RS < s.re ∧ s ≠ 1 := by
    intro s hs
    refine ⟨by linarith [le_max_left (max 2 σ₀) σ_RS, le_max_left 2 σ₀],
      by linarith [le_max_left (max 2 σ₀) σ_RS, le_max_right 2 σ₀], by linarith [le_max_right (max 2 σ₀) σ_RS], ?_⟩
    rintro rfl
    have : (2 : ℝ) ≤ σ₂ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hσ₂)
    norm_num at hs; linarith

  obtain ⟨ΛS, hΛS⟩ : ∃ ΛS : ℂ → ℂ, ∀ s, ΛS s = Λ s * ∏ v ∈ S' \ S, (P v).eval (Nv v ^ (-s)) :=
    ⟨_, fun _ => rfl⟩
  have hΛSprod : ∀ s : ℂ, σ₂ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S'} => ((P v.1).eval (Nv v.1 ^ (-s)))⁻¹) (ΛS s) := by
    intro s hs
    rw [hΛS]
    exact AutomorphicForm.R1Assembly.peel_inv (g := fun v => (P v).eval (Nv v ^ (-s))) hSS'
      (hprod' s (hσ₂' s hs).2.1) (fun v hv _ => (hσ₂ne s hs v hv).1)
  have hNvdiff : ∀ v : HeightOneSpectrum (𝓞 ℚ), Differentiable ℂ (fun s : ℂ => Nv v ^ (-s)) := fun v =>
    differentiable_neg.const_cpow (Or.inl (hNv0 v))
  have hΛSdiff : Differentiable ℂ ΛS := by
    have : ΛS = fun s => Λ s * ∏ v ∈ S' \ S, (P v).eval (Nv v ^ (-s)) := funext hΛS
    rw [this]
    exact hΛ.mul (Differentiable.fun_finsetProd fun v _ => (P v).differentiable.comp (hNvdiff v))
  have hΛS1 : ΛS 1 = 0 := by rw [hΛS, h1, zero_mul]
  obtain ⟨Λ₁, hΛ₁, hΛ₁eq⟩ := AutomorphicForm.R1Assembly.exists_differentiable_eq_sub_mul hΛSdiff 1 hΛS1

  have hconjprod : ∀ s : ℂ, σ₂ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S'} =>
        (1 - (ua v.1 / ub v.1) * Nv v.1 ^ (-s) + (ub v.1)⁻¹ * (Nv v.1 ^ (-s)) ^ 2)⁻¹)
        ((starRingEnd ℂ) (ΛS ((starRingEnd ℂ) s))) := by
    intro s hs
    have hs' : σ₂ < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
    have h := (hΛSprod _ hs').map (starRingEnd ℂ) Complex.continuous_conj
    convert h using 1
    funext v
    obtain ⟨hvS, hvS₁, hvS₂, -, -, -⟩ := hout v.1 v.2
    simp only [Function.comp_apply, hPv v.1 v.2, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
      eval_one, map_inv₀, map_add, map_sub, map_mul, map_one, map_pow, hconj_a v.1 v.2, hconj_b v.1 v.2,
      hNv, AutomorphicForm.R1Assembly.conj_natCast_cpow, map_neg, Complex.conj_conj]

  obtain ⟨AS, hAS⟩ : ∃ AS : ℂ → ℂ, ∀ s, AS s = A s * ∏ v ∈ S' \ S_RS, (RS v).eval (Nv v ^ (-s)) :=
    ⟨_, fun _ => rfl⟩
  have htwist : ∀ v ∉ S', rsEulerPoly (ua v / ub v) (ub v)⁻¹ (ua v) (ub v) 0 = RS v := by
    intro v hv
    have hb0 : Φ.b v ≠ 0 := by
      intro h; apply hub0 v hv; rw [hub, h, mul_zero]
    rw [hRS, hua, hub, Units.val_pow_eq_pow_val]
    exact AutomorphicForm.R1Assembly.rsEulerPoly_twist _ _ _ (Units.ne_zero _) hb0
  have hASprod : ∀ s : ℂ, σ₂ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S'} =>
        ((rsEulerPoly (ua v.1 / ub v.1) (ub v.1)⁻¹ (ua v.1) (ub v.1) 0).eval (Nv v.1 ^ (-s)))⁻¹)
        (AS s / (s - 1)) := by
    intro s hs
    have h := AutomorphicForm.R1Assembly.peel_inv (g := fun v => (RS v).eval (Nv v ^ (-s))) hS_RS'
      (hAprod' s (hσ₂' s hs).2.2.1) (fun v hv _ => (hσ₂ne s hs v hv).2.1)
    rw [hAS, mul_div_right_comm]
    convert h using 2
    rename_i v
    rw [htwist v.1 v.2]
  have hASan : ∀ σ : ℝ, x < σ → AnalyticAt ℂ AS (σ : ℂ) := by
    intro σ hσ
    have : AS = fun s => A s * ∏ v ∈ S' \ S_RS, (RS v).eval (Nv v ^ (-s)) := funext hAS
    rw [this]
    exact (hA σ hσ).mul ((Differentiable.fun_finsetProd fun v _ =>
      (RS v).differentiable.comp (hNvdiff v)).analyticAt _)

  obtain ⟨ZS, hZS⟩ : ∃ ZS : ℂ → ℂ, ∀ s, ZS s = R s * ∏ v ∈ S', (1 - Nv v ^ (-s)) := ⟨_, fun _ => rfl⟩
  have hZSprod : ∀ s : ℂ, σ₂ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S'} => (1 - Nv v.1 ^ (-s))⁻¹) (ZS s / (s - 1)) := by
    intro s hs
    have h1s : 1 < s.re := by linarith [(hσ₂' s hs).1]
    have hζ := NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta ℚ s h1s
    have h := AutomorphicForm.R1Assembly.peel_inv₀ (g := fun v => 1 - Nv v ^ (-s)) S'
      (by simpa only [hNv] using hζ) (fun v hv => (hσ₂ne s hs v hv).2.2)
    convert h using 1
    rw [hZS, hRζ s h1s, mul_div_right_comm, mul_div_cancel_left₀ _ (sub_ne_zero.mpr (hσ₂' s hs).2.2.2)]
  have hZSdiff : Differentiable ℂ ZS := by
    have : ZS = fun s => R s * ∏ v ∈ S', (1 - Nv v ^ (-s)) := funext hZS
    rw [this]
    exact hR.mul (Differentiable.fun_finsetProd fun v _ => (differentiable_const _).sub (hNvdiff v))

  have hΛ₁c : Differentiable ℂ ((starRingEnd ℂ) ∘ Λ₁ ∘ (starRingEnd ℂ)) := fun z => by
    have := (hΛ₁ ((starRingEnd ℂ) z)).conj_conj
    rwa [Complex.conj_conj] at this
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ s,
      G s = ZS s * Λ₁ s * ((starRingEnd ℂ) ∘ Λ₁ ∘ (starRingEnd ℂ)) s * AS s := ⟨_, fun _ => rfl⟩
  have hGeq : ∀ s : ℂ, σ₂ < s.re → Complex.exp (LSeries (fun n => (d n : ℂ)) s) = G s := by
    intro s hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (hσ₂' s hs).2.2.2
    have H := ((hZSprod s hs).mul (hΛSprod s hs)).mul ((hconjprod s hs).mul (hASprod s hs))
    have HQ := (hexpD s (hσ₂' s hs).1).2
    have heqf : (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S'} => (Q v.1 (Nv v.1 ^ (-s)))⁻¹)
        = fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S'} =>
          ((1 - Nv v.1 ^ (-s))⁻¹ * ((P v.1).eval (Nv v.1 ^ (-s)))⁻¹) *
          ((1 - (ua v.1 / ub v.1) * Nv v.1 ^ (-s) + (ub v.1)⁻¹ * (Nv v.1 ^ (-s)) ^ 2)⁻¹ *
            ((rsEulerPoly (ua v.1 / ub v.1) (ub v.1)⁻¹ (ua v.1) (ub v.1) 0).eval (Nv v.1 ^ (-s)))⁻¹) := by
      funext v
      rw [hQ, hPv v.1 v.2]
      simp only [eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X, mul_inv]
      ring
    rw [heqf] at HQ
    have huniq := HQ.unique H
    rw [huniq, hG, hΛ₁eq, hΛ₁eq]
    simp only [Function.comp_apply, map_mul, map_sub, map_one, Complex.conj_conj]
    field_simp

  have hGan : ∀ σ : ℝ, max x (-1) < σ → AnalyticAt ℂ G (σ : ℂ) := by
    intro σ hσ
    have hxσ : x < σ := lt_of_le_of_lt (le_max_left _ _) hσ
    have : G = fun s => ZS s * Λ₁ s * ((starRingEnd ℂ) ∘ Λ₁ ∘ (starRingEnd ℂ)) s * AS s := funext hG
    rw [this]
    exact (((hZSdiff.mul hΛ₁).mul hΛ₁c).analyticAt _).mul (hASan σ hxσ)

  obtain ⟨-, hreal⟩ :=
    LSeries.abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq d hdnn G (max x (-1)) σ₂ hGan
      (fun s hs => ⟨(hexpD s (hσ₂' s hs).1).1, hGeq s hs⟩)
  have h0 := (hreal 0 (max_lt hx (by norm_num))).2
  have hG0 : G ((0 : ℝ) : ℂ) = 0 := by
    rw [hG, hZS, Complex.ofReal_zero, neg_zero]
    have : ∏ v ∈ S', (1 - Nv v ^ (0 : ℂ)) = 0 :=
      Finset.prod_eq_zero hv₀ (by rw [Complex.cpow_zero, sub_self])
    rw [this]; ring
  exact Complex.exp_ne_zero _ (h0.trans hG0)

end S_AutomorphicForm_apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat
end P2MW
export P2MW.S_AutomorphicForm_apply_one_ne_zero_of_differentiable_of_hasProd_eulerProduct_twist_of_norm_eq_one_rat (solution)
