-- Prove2me | solution 1 for AutomorphicForm.exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e7ed70a9-a919-51b8-9284-a0bff22d6c8c

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_isLevelSphericalOfType_principal_flat_tendsto_rightConv_of_finiteDimensional
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul"
p2m_attr_erase "simp" "M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.TateLocal.conductorExponentAt_one HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open scoped ComplexConjugate Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4ProjCore

section NormOne

variable (F : Type) [Field F] [NumberField F]

theorem fst_mul (a b : AdeleRing (𝓞 F) F) : (a * b).1 = a.1 * b.1 := rfl
theorem snd_mul (a b : AdeleRing (𝓞 F) F) : (a * b).2 = a.2 * b.2 := rfl
theorem fst_one : (1 : AdeleRing (𝓞 F) F).1 = 1 := rfl
theorem snd_one : (1 : AdeleRing (𝓞 F) F).2 = 1 := rfl

theorem smul_adelicBox_eq (x : (AdeleRing (𝓞 F) F)ˣ) (h1 : (x : AdeleRing (𝓞 F) F).1 = 1)
    (hint : (x : AdeleRing (𝓞 F) F).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F)
    (hint' : ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈
      NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F) :
    x • NumberField.AdelicBox.adelicBox F = NumberField.AdelicBox.adelicBox F := by
  have h1' : ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
    have h := congrArg (fun a : AdeleRing (𝓞 F) F => a.1) x.inv_mul
    beta_reduce at h
    rw [fst_mul, fst_one, h1, mul_one] at h
    exact h
  ext a
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  show ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * a ∈ NumberField.AdelicBox.adelicBox F ↔
    a ∈ NumberField.AdelicBox.adelicBox F
  simp only [NumberField.AdelicBox.adelicBox, Set.mem_setOf_eq, fst_mul, snd_mul, h1', one_mul]
  change (_ ∧ _ * a.2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F) ↔
    (_ ∧ a.2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F)
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => mul_mem_integralFiniteAdeles hint' h⟩
  have : (x : AdeleRing (𝓞 F) F).2 * (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * a.2) = a.2 := by
    rw [← mul_assoc, ← snd_mul, x.mul_inv, snd_one, one_mul]
  rw [← this]
  exact mul_mem_integralFiniteAdeles hint h

theorem ideleNorm_eq_one (x : (AdeleRing (𝓞 F) F)ˣ) (h1 : (x : AdeleRing (𝓞 F) F).1 = 1)
    (hint : (x : AdeleRing (𝓞 F) F).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F)
    (hint' : ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈
      NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F) :
    ideleNorm F x = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).Regular := by
    unfold adelicAddHaar Measure.addHaar; infer_instance
  unfold ideleNorm
  rw [distribHaarChar_eq_of_measure_smul_eq_mul (μ := adelicAddHaar (𝓞 F) F)
    (s := NumberField.AdelicBox.adelicBox F)
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos F).ne'
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top F).ne (r := 1)
    (by rw [smul_adelicBox_eq F x h1 hint hint', ENNReal.coe_one, one_mul])]
  rfl

variable {F}

theorem det_snd_mem_integralFiniteAdeles {N : Ideal (𝓞 F)} {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ levelOne (𝓞 F) F N) :
    ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈
      NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F := by
  have hint := (mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp hu)).1.integral
  have h : ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 =
      ((glFin (𝓞 F) F u : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
    rfl
  rw [h, Matrix.det_fin_two]
  exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hint 0 0) (hint 1 1))
    (mul_mem_integralFiniteAdeles (hint 0 1) (hint 1 0))

theorem det_fst_eq_one {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ finiteAdelicGL2Subgroup F) :
    ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  have h1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp hu
  have h : ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 =
      ((glArch (𝓞 F) F u : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
    rfl
  rw [h, h1]
  simp

theorem ideleNorm_det_eq_one_of_mem_levelOne_inf {N : Ideal (𝓞 F)} {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := by
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
  refine ideleNorm_eq_one F _ (det_fst_eq_one hu2) (det_snd_mem_integralFiniteAdeles hu1) ?_
  rw [← map_inv]
  exact det_snd_mem_integralFiniteAdeles (inv_mem hu1)

theorem ideleNorm_det_eq_one_of_mem_principalLevel_inf {N : Ideal (𝓞 F)} {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 :=
  ideleNorm_det_eq_one_of_mem_levelOne_inf (Subgroup.mem_inf.mpr
    ⟨principalLevel_le_levelOne (𝓞 F) F N (Subgroup.mem_inf.mp hu).1, (Subgroup.mem_inf.mp hu).2⟩)

end NormOne

section ArchDet

variable {F : Type} [Field F] [NumberField F]

def archIncl (F : Type) [Field F] [NumberField F] : InfiniteAdeleRing F →* AdeleRing (𝓞 F) F where
  toFun x := (x, (1 : FiniteAdeleRing (𝓞 F) F))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

theorem det_eq_archIncl_mul_finIncl (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det g =
      Units.map (archIncl F) (Matrix.GeneralLinearGroup.det (glArch (𝓞 F) F g)) *
        Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
          (Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F g)) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).1 =
      ((archIncl F (Matrix.det ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))) *
        (finIncl (𝓞 F) F (Matrix.det ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))))).1
    have h : adeleArch (𝓞 F) F (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
        Matrix.det ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
      rw [RingHom.map_det]; rfl
    rw [← adeleArch_apply, h, ← adeleArch_apply, map_mul, adeleArch_apply, adeleArch_apply, finIncl_apply_fst,
      mul_one]
    rfl
  · change (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).2 =
      ((archIncl F (Matrix.det ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))) *
        (finIncl (𝓞 F) F (Matrix.det ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))))).2
    have h : adeleFin (𝓞 F) F (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
        Matrix.det ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := by
      rw [RingHom.map_det]; rfl
    rw [← adeleFin_apply, h, ← adeleFin_apply, map_mul, adeleFin_apply, adeleFin_apply, finIncl_apply_snd]
    change _ = (1 : FiniteAdeleRing (𝓞 F) F) * _
    rw [one_mul]

theorem det_rowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k) = 1 := by
  have hk1 : ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2).1
  rw [rowIsometryInclAt₀_apply, show adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) =
    adelicArchGLIncl F (archGLIncl F w (k : GL (Fin 2) w.Completion)) from rfl, det_eq_archIncl_mul_finIncl,
    glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, map_one, map_one, mul_one, ← map_one (Units.map (archIncl F))]
  congr 1
  refine Units.ext (funext fun u => ?_)
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  change archEval F u (Matrix.det ((archGLIncl F w (k : GL (Fin 2) w.Completion) : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) = 1
  rw [RingHom.map_det]
  change Matrix.det ((archComponent F u (archGLIncl F w (k : GL (Fin 2) w.Completion)) : GL (Fin 2) u.Completion) :
    Matrix (Fin 2) (Fin 2) u.Completion) = 1
  by_cases hu : u = w
  · subst hu
    rw [archComponent_archGLIncl_self, hk1]
  · rw [archComponent_archGLIncl_of_ne F hu, Units.val_one, Matrix.det_one]

theorem ideleNorm_det_rowIsometryInclAt₀_mul (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (x : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k * x)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det x) := by
  rw [map_mul, det_rowIsometryInclAt₀, one_mul]

theorem ideleNorm_det_mul_rowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (x : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (x * rowIsometryInclAt₀ F w k)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det x) := by
  rw [map_mul, det_rowIsometryInclAt₀, mul_one]

end ArchDet

section Cut

variable {F : Type} [Field F] [NumberField F]

theorem mul_mem_typeSubmodule {H G : Type*} [Group H] [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ι : H →* G} {ρ : Representation ℂ H W} {m : G → ℂ} (hm : ∀ (k : H) (x : G), m (x * ι k) = m x)
    {fa : G → ℂ} (hfa : fa ∈ typeSubmodule ι ρ) : (fun x => fa x * m x) ∈ typeSubmodule ι ρ := by
  simpa using comp_mul_mem_typeSubmodule_of_hom (MonoidHom.id G) (ι := ι) (ι' := ι) (fun _ => rfl) hm hfa

theorem mul_mem_archCutSubmodule (tys : ArchTypeFamily F) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : θ ∈ archCutSubmodule F tys) (m : AdelicGL2 (𝓞 F) F → ℂ)
    (hm : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 F) F),
      m (x * rowIsometryInclAt₀ F w k) = m x) :
    (fun x => θ x * m x) ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hθ ⊢
  intro w
  exact comp_mul_mem_iSup_of_forall (fun x => x) m
    (fun i => archTypeSubmoduleAt F w (tys.rep w i)) (fun i => archTypeSubmoduleAt F w (tys.rep w i))
    (fun i fa hfa => mul_mem_typeSubmodule (hm w) hfa) (hθ w)

theorem mul_mem_archDualCutSubmodule (tys : ArchTypeFamily F) {θ : AdelicGL2 (𝓞 F) F → ℂ}
    (hθ : θ ∈ archDualCutSubmodule F tys) (m : AdelicGL2 (𝓞 F) F → ℂ)
    (hm : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 F) F),
      m (x * rowIsometryInclAt₀ F w k) = m x) :
    (fun x => θ x * m x) ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hθ ⊢
  intro w
  exact comp_mul_mem_iSup_of_forall (fun x => x) m
    (fun i => archDualTypeSubmoduleAt F w (tys.rep w i)) (fun i => archDualTypeSubmoduleAt F w (tys.rep w i))
    (fun i fa hfa => mul_mem_typeSubmodule (hm w) hfa) (hθ w)

end Cut

section Flat

variable {F : Type} [Field F] [NumberField F]

theorem flat_admissible (tys : ArchTypeFamily F) (N : Ideal (𝓞 F)) (s : ℝ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : IsBiInvariantUnder F (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) f)
    (hft : IsArchBiFinite F tys f) :
    Continuous (fun y => conj (f y⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) ∧
      HasCompactSupport (fun y => conj (f y⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) ∧
      IsBiInvariantUnder F (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun y => conj (f y⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) ∧
      IsArchBiFinite F tys (fun y => conj (f y⁻¹) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) := by
  set wt : AdelicGL2 (𝓞 F) F → ℂ := fun y =>
    ((ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ) with hwt
  set Ulev : Subgroup (AdelicGL2 (𝓞 F) F) := principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F with hUlev
  have hwtc : Continuous wt := by
    refine Complex.continuous_ofReal.comp ?_
    exact (NumberField.TateGlobal.continuous_ideleNorm_det F).rpow_const fun y =>
      Or.inl (ideleNorm_pos _).ne'

  have hwtU : ∀ u ∈ Ulev, ∀ y, wt (u * y) = wt y ∧ wt (y * u) = wt y := by
    intro u hu y
    have hu1 : ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 :=
      ideleNorm_det_eq_one_of_mem_principalLevel_inf hu
    constructor
    · simp only [hwt, map_mul, ideleNorm_mul, hu1, one_mul]
    · simp only [hwt, map_mul, ideleNorm_mul, hu1, mul_one]
  have hwtK : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F),
      wt (y * rowIsometryInclAt₀ F w k) = wt y := by
    intro w k y
    simp only [hwt, ideleNorm_det_mul_rowIsometryInclAt₀]
  have hwtK' : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F),
      wt (y * rowIsometryInclAt₀ F w k)⁻¹ = wt y⁻¹ := by
    intro w k y
    simp only [hwt, mul_inv_rev, ← map_inv, ideleNorm_det_rowIsometryInclAt₀_mul]
  refine ⟨(Complex.continuous_conj.comp (hf.comp continuous_inv)).mul hwtc, ?_, ?_, ?_⟩
  · exact ((hfc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))).comp_left (g := conj) (map_zero _)).mul_right
  · intro u hu g
    have hu' : u⁻¹ ∈ Ulev := inv_mem hu
    constructor
    · show conj (f (u * g)⁻¹) * wt (u * g) = conj (f g⁻¹) * wt g
      rw [mul_inv_rev, (hfU u⁻¹ hu' g⁻¹).2, (hwtU u hu g).1]
    · show conj (f (g * u)⁻¹) * wt (g * u) = conj (f g⁻¹) * wt g
      rw [mul_inv_rev, (hfU u⁻¹ hu' g⁻¹).1, (hwtU u hu g).2]
  · constructor
    ·
      have hconj : (fun y => conj (f y)) ∈ archCutSubmodule F tys :=
        (AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous
          F tys f hf).1 hft.2
      have h := mul_mem_archCutSubmodule tys hconj (fun x => wt x⁻¹) hwtK'
      have heq : (fun x => (fun y => conj (f y⁻¹) * wt y) x⁻¹) = fun x => conj (f x) * wt x⁻¹ := by
        funext x
        simp only [inv_inv]
      show (fun x => (fun y => conj (f y⁻¹) * wt y) x⁻¹) ∈ archCutSubmodule F tys
      rw [heq]
      exact h
    ·
      have hfinvc : Continuous fun y => f y⁻¹ := hf.comp continuous_inv
      have hconj : (fun y => conj (f y⁻¹)) ∈ archDualCutSubmodule F tys :=
        (AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous
          F tys (fun y => f y⁻¹) hfinvc).2 hft.1
      exact mul_mem_archDualCutSubmodule tys hconj wt hwtK

end Flat

section Spherical

variable {F : Type} [Field F] [NumberField F]

theorem indicator_image_glFin_mul_left {U : Subgroup (AdelicGL2 (𝓞 F) F)} {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ U)
    (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F u * x) =
      Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) x := by
  have key : glFin (𝓞 F) F u * x ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) ↔
      x ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
    rw [← Subgroup.coe_map, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_left _ (Subgroup.mem_map_of_mem _ hu)
  by_cases hx : x ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]

theorem indicator_image_glFin_mul_right {U : Subgroup (AdelicGL2 (𝓞 F) F)} {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ U)
    (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (x * glFin (𝓞 F) F u) =
      Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) x := by
  have key : x * glFin (𝓞 F) F u ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) ↔
      x ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
    rw [← Subgroup.coe_map, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_right _ (Subgroup.mem_map_of_mem _ hu)
  by_cases hx : x ∈ (glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]

theorem admissible_of_isLevelSphericalOfType {N : Ideal (𝓞 F)} {tys : ArchTypeFamily F}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hff : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) f) :
    Continuous f ∧ HasCompactSupport f ∧
      IsBiInvariantUnder F (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) f ∧ IsArchBiFinite F tys f := by
  obtain ⟨hc, hs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hff
  obtain ⟨fa, -, hfa, -, hfac⟩ := hsph
  refine ⟨hc, hs, ?_, IsArchBiFinite.of_factorization F hfac hfa⟩
  intro u hu g
  have hu1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp (Subgroup.mem_inf.mp hu).2
  constructor
  · rw [hfac, hfac, map_mul, map_mul, hu1, one_mul, indicator_image_glFin_mul_left hu]
  · rw [hfac, hfac, map_mul, map_mul, hu1, mul_one, indicator_image_glFin_mul_right hu]

end Spherical

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

theorem isLsXiFunction_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π) :
    IsLsXiFunction (𝓞 L) L ⊤ ξL u :=
  (isLsXiFunction_and_memLp_of_mem hu).1

theorem memLp_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) :=
  (isLsXiFunction_and_memLp_of_mem hu).2

theorem apply_mul_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π)
    (g : AdelicGL2 (𝓞 L) L) (k : AdelicGL2 (𝓞 L) L) (hk : k ∈ U N) : u (g * k) = u g := by
  revert g
  refine Submodule.span_induction (p := fun u _ => ∀ g : AdelicGL2 (𝓞 L) L, u (g * k) = u g) ?_ ?_ ?_ ?_ hu
  · exact fun u h g => h.level_invariant g k hk
  · intro g
    rfl
  · intro u w _ _ hu' hw' g
    simp only [Pi.add_apply, hu' g, hw' g]
  · intro c u _ hu' g
    simp only [Pi.smul_apply, hu' g]

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

theorem ip_sub_left {u w v : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hw : MemLp w 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hv : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ)) :
    ip Φ (u - w) v = ip Φ u v - ip Φ w v := by
  unfold ip
  simp only [Pi.sub_apply, sub_mul]
  exact integral_sub (integrable_mul_conj hu hv) (integrable_mul_conj hw hv)

theorem ip_smul_left (c : ℂ) (u v : AdelicGL2 (𝓞 L) L → ℂ) :
    ip Φ (c • u) v = c * ip Φ u v := by
  unfold ip
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem ip_zero_left (v : AdelicGL2 (𝓞 L) L → ℂ) : ip Φ 0 v = 0 := by
  simp [ip]

theorem ip_zero_right (u : AdelicGL2 (𝓞 L) L → ℂ) : ip Φ u 0 = 0 := by
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

theorem conj_ip (u v : AdelicGL2 (𝓞 L) L → ℂ) : conj (ip Φ u v) = ip Φ v u := by
  unfold ip
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_conj, mul_comm]

theorem ip_sum_smul_right {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → AdelicGL2 (𝓞 L) L → ℂ)
    (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hu : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ)) :
    ip Φ u (∑ i ∈ s, c i • f i) = ∑ i ∈ s, conj (c i) * ip Φ u (f i) := by
  rw [← conj_ip, ip_sum_smul_left s c f u hf hu, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, conj_ip]

end Pairing

theorem main
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (tys : ArchTypeFamily K)
    (Ψ' : HeckeEigensystem K ℂ) (hΨ'N : Ψ'.level = N) (hΨ'S : ∀ w ∈ S, Ψ'.a w = 0 ∧ Ψ'.b w = 0)
    (v : AdelicGL2 (𝓞 K) K → ℂ) (hv : IsLsXiFunction (𝓞 K) K ⊤ ξ v) (hvc : Continuous v)
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ))
    (hR : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
        IsArchBiFinite K tys f →
      convOp K f v ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ' ⊓ archCutSubmodule K tys) :
    ∃ u₁ ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ' ⊓ archCutSubmodule K tys,
      (∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
          IsArchBiFinite K tys f →
        convOp K f v = convOp K f u₁) ∧
      ∀ π ∈ cuspClasses K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S,
      ∀ b ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys,
        ip Φ v b = ip Φ u₁ b := by
  classical
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K

  set P := productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (adelicBox K) with hP
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Ulev : Subgroup (AdelicGL2 (𝓞 K) K) := principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K with hUlev
  let W : HeckeEigensystem K ℂ → Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := fun π =>
    isotypicCuspSubmodule K P ξ N S π ⊓ archCutSubmodule K tys
  change ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →
      IsBiInvariantUnder K Ulev f → IsArchBiFinite K tys f → convOp K f v ∈ W Ψ' at hR
  show ∃ u₁ ∈ W Ψ', (∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →
      IsBiInvariantUnder K Ulev f → IsArchBiFinite K tys f → convOp K f v = convOp K f u₁) ∧
    ∀ π ∈ cuspClasses K P ξ N S, ∀ b ∈ W π, ip Φ v b = ip Φ u₁ b

  by_cases hv0 : v = 0
  · refine ⟨0, Submodule.zero_mem _, fun f _ _ _ _ => by rw [hv0], fun π _ b _ => by rw [hv0]⟩

  have hV : ∀ π, ∀ u ∈ W π, u ∈ isotypicCuspSubmodule K P ξ N S π :=
    fun π u hu => (Submodule.mem_inf.mp hu).1
  have hWc : ∀ π, ∀ u ∈ W π, Continuous u :=
    fun π u hu => continuous_of_mem_isotypicCuspSubmodule (hV π u hu)
  have hW2 : ∀ π, ∀ u ∈ W π, MemLp u 2 (μ.restrict Φ) := fun π u hu => memLp_of_mem (hV π u hu)
  have hWl : ∀ π, ∀ u ∈ W π, IsLsXiFunction (𝓞 K) K ⊤ ξ u := fun π u hu => isLsXiFunction_of_mem (hV π u hu)
  have hWU : ∀ π, ∀ u ∈ W π, ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ Ulev, u (g * k) = u g :=
    fun π u hu g k hk => apply_mul_of_mem (hV π u hu) g k hk
  have hWcut : ∀ π, W π ≤ archCutSubmodule K tys := fun π => inf_le_right

  have hRW : ∀ π (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →
      IsBiInvariantUnder K Ulev f → IsArchBiFinite K tys f → ∀ u ∈ W π, convOp K f u ∈ W π :=
    fun π f hf hfc hfU hft u hu =>
      AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
        K α β hα hαβ Φ hΦs hΦ ξ S N hN tys π f hf hfc hfU hft u hu

  have hNbot : N ≠ ⊥ := hΨ'N ▸ Ψ'.level_ne_bot
  have hfd : ∀ π, FiniteDimensional ℂ (W π) := fun π =>
    AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_isFundamentalDomain
      K α β hα hαβ Φ hΦs hΦ ξ N hNbot S tys π

  have hvne : ∃ g, v g ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  obtain ⟨hprin, hcontχ⟩ :=
    AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous K ξ v hv hvc hvne
  let μξ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ξ.comp Subgroup.topEquiv.symm.toMonoidHom
  obtain ⟨s, hs'⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K μξ (fun u => hprin u) hcontχ
  have hs : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ s := fun z => hs' z

  have hadj : ∀ (a b : AdelicGL2 (𝓞 K) K → ℂ), IsLsXiFunction (𝓞 K) K ⊤ ξ a → IsLsXiFunction (𝓞 K) K ⊤ ξ b →
      Continuous a → Continuous b → MemLp a 2 (μ.restrict Φ) → MemLp b 2 (μ.restrict Φ) →
      ∀ (g : AdelicGL2 (𝓞 K) K → ℂ), Continuous g → HasCompactSupport g →
      ip Φ (convOp K g a) b = ip Φ a (rightConv K b (fun y => conj (g y⁻¹) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ))) := by
    intro a b hal hbl hac hbc ha2 hb2 g hg hgc
    have h :=
      AutomorphicForm.setIntegral_rightConv_mul_conj_eq_setIntegral_mul_conj_rightConv_flat_of_isLsXiFunction_of_isFundamentalDomain_slab
        K α β Φ hΦs hΦ ξ s hs a b hal hbl hac hbc ha2 hb2 g hg hgc
    simpa only [ip, convOp_apply] using h

  have hdef : ∀ b : AdelicGL2 (𝓞 K) K → ℂ, IsLsXiFunction (𝓞 K) K ⊤ ξ b → Continuous b →
      MemLp b 2 (μ.restrict Φ) → ip Φ b b = 0 → b = 0 := by
    intro b hbl hbc hb2 h0
    by_contra hne
    have h :=
      AutomorphicForm.setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
        K α β hα hαβ Φ hΦs hΦ ξ 0 b hbl hbc hb2 hne
    simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one] at h
    exact h h0

  have hΨ'cls : W Ψ' ≠ ⊥ → Ψ' ∈ cuspClasses K P ξ N S := by
    intro hne
    refine ⟨hΨ'N, hΨ'S, ?_⟩
    intro hbot
    apply hne
    show isotypicCuspSubmodule K P ξ N S Ψ' ⊓ archCutSubmodule K tys = ⊥
    rw [hbot, bot_inf_eq]
  have hperp : ∀ π ∈ cuspClasses K P ξ N S, π ≠ Ψ' → ∀ b ∈ W π, ∀ a ∈ W Ψ', ip Φ b a = 0 := by
    intro π hπ hne b hb a ha
    by_cases hbot : W Ψ' = ⊥
    · have ha0 : a = 0 := by
        have : a ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) := hbot ▸ ha
        exact (Submodule.mem_bot ℂ).mp this
      rw [ha0, ip_zero_right]
    · exact AutomorphicForm.setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
        K α β hα hαβ Φ hΦs hΦ ξ N S hN π Ψ' hπ (hΨ'cls hbot) hne b a (hV π b hb) (hV Ψ' a ha)
  have hperp' : ∀ π ∈ cuspClasses K P ξ N S, π ≠ Ψ' → ∀ a ∈ W Ψ', ∀ b ∈ W π, ip Φ a b = 0 := by
    intro π hπ hne a ha b hb
    rw [← conj_ip, hperp π hπ hne b hb a ha, map_zero]

  haveI : FiniteDimensional ℂ (W Ψ') := hfd Ψ'
  set n : ℕ := Module.finrank ℂ (W Ψ') with hn
  let bV : Module.Basis (Fin n) ℂ (W Ψ') := Module.finBasis ℂ (W Ψ')
  let e : Fin n → (AdelicGL2 (𝓞 K) K → ℂ) := fun i => (bV i : AdelicGL2 (𝓞 K) K → ℂ)
  have he : ∀ i, e i ∈ W Ψ' := fun i => (bV i).2
  have he2 : ∀ i, MemLp (e i) 2 (μ.restrict Φ) := fun i => hW2 Ψ' _ (he i)
  let A : W Ψ' →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun b' i => ip Φ (b' : AdelicGL2 (𝓞 K) K → ℂ) (e i)
      map_add' := fun b₁ b₂ => funext fun i => by
        simp only [Submodule.coe_add, Pi.add_apply]
        exact ip_add_left (hW2 Ψ' _ b₁.2) (hW2 Ψ' _ b₂.2) (he2 i)
      map_smul' := fun c b' => funext fun i => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact ip_smul_left c _ _ }
  have hA_apply : ∀ (b' : W Ψ') (i : Fin n), A b' i = ip Φ (b' : AdelicGL2 (𝓞 K) K → ℂ) (e i) :=
    fun _ _ => rfl

  have hexpand : ∀ b' : W Ψ', (b' : AdelicGL2 (𝓞 K) K → ℂ) = ∑ i, (bV.repr b' i) • e i := by
    intro b'
    have h := congrArg (Subtype.val : W Ψ' → AdelicGL2 (𝓞 K) K → ℂ) (bV.sum_repr b')
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hA_inj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b' hb'
    have hzero : ∀ i, ip Φ (b' : AdelicGL2 (𝓞 K) K → ℂ) (e i) = 0 := fun i => by
      rw [← hA_apply, hb']
      rfl
    have hself : ip Φ (b' : AdelicGL2 (𝓞 K) K → ℂ) b' = 0 := by
      rw [congrArg (fun w => ip Φ (b' : AdelicGL2 (𝓞 K) K → ℂ) w) (hexpand b'),
        ip_sum_smul_right Finset.univ (fun i => bV.repr b' i) e _ (fun i _ => he2 i) (hW2 Ψ' _ b'.2)]
      exact Finset.sum_eq_zero fun i _ => by rw [hzero i, mul_zero]
    have h0 := hdef _ (hWl Ψ' _ b'.2) (hWc Ψ' _ b'.2) (hW2 Ψ' _ b'.2) hself
    exact Subtype.ext h0
  have hA_surj : Function.Surjective A := by
    have hfr : Module.finrank ℂ (W Ψ') = Module.finrank ℂ (Fin n → ℂ) := by
      rw [Module.finrank_fin_fun]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hA_inj
  obtain ⟨u₁', hu₁'⟩ := hA_surj (fun i => ip Φ v (e i))
  set u₁ : AdelicGL2 (𝓞 K) K → ℂ := (u₁' : AdelicGL2 (𝓞 K) K → ℂ) with hu₁
  have hu₁W : u₁ ∈ W Ψ' := u₁'.2
  have hproj : ∀ b ∈ W Ψ', ip Φ v b = ip Φ u₁ b := by
    intro b hb
    have hb' := hexpand ⟨b, hb⟩
    simp only at hb'
    rw [hb', ip_sum_smul_right Finset.univ _ e v (fun i _ => he2 i) hv₂,
      ip_sum_smul_right Finset.univ _ e u₁ (fun i _ => he2 i) (hW2 Ψ' _ hu₁W)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ip Φ u₁ (e i) = ip Φ v (e i) := by
      have := congrFun hu₁' i
      rw [hA_apply] at this
      exact this
    rw [h1]
  refine ⟨u₁, hu₁W, ?_, ?_⟩

  · intro f hf hfc hfU hft
    have h1 : convOp K f v ∈ W Ψ' := hR f hf hfc hfU hft
    have h2 : convOp K f u₁ ∈ W Ψ' := hRW Ψ' f hf hfc hfU hft u₁ hu₁W
    obtain ⟨hflc, hfls, hflU, hflt⟩ := flat_admissible tys N s f hf hfc hfU hft
    have hdW : convOp K f v - convOp K f u₁ ∈ W Ψ' := Submodule.sub_mem _ h1 h2
    have hRd : rightConv K (convOp K f v - convOp K f u₁) (fun y => conj (f y⁻¹) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) ∈ W Ψ' :=
      hRW Ψ' _ hflc hfls hflU hflt _ hdW
    have hdd : ip Φ (convOp K f v - convOp K f u₁) (convOp K f v - convOp K f u₁) = 0 := by
      rw [ip_sub_left (hW2 Ψ' _ h1) (hW2 Ψ' _ h2) (hW2 Ψ' _ hdW),
        hadj v _ hv (hWl Ψ' _ hdW) hvc (hWc Ψ' _ hdW) hv₂ (hW2 Ψ' _ hdW) f hf hfc,
        hadj u₁ _ (hWl Ψ' _ hu₁W) (hWl Ψ' _ hdW) (hWc Ψ' _ hu₁W) (hWc Ψ' _ hdW) (hW2 Ψ' _ hu₁W) (hW2 Ψ' _ hdW)
          f hf hfc,
        hproj _ hRd, sub_self]
    have h0 := hdef _ (hWl Ψ' _ hdW) (hWc Ψ' _ hdW) (hW2 Ψ' _ hdW) hdd
    exact sub_eq_zero.1 h0

  · intro π hπ b hb
    by_cases hπΨ : π = Ψ'
    · subst hπΨ
      exact hproj b hb
    ·
      rw [hperp' π hπ hπΨ u₁ hu₁W b hb]

      haveI : FiniteDimensional ℂ (W π) := hfd π
      obtain ⟨fs, hfs, htend⟩ :=
        AutomorphicForm.exists_isLevelSphericalOfType_principal_flat_tendsto_rightConv_of_finiteDimensional
          K N hNbot tys s (W π) (hfd π) (hWc π) (hWU π) (hWcut π)
      have hadm : ∀ m, Continuous (fs m) ∧ HasCompactSupport (fs m) ∧
          IsBiInvariantUnder K Ulev (fs m) ∧ IsArchBiFinite K tys (fs m) :=
        fun m => admissible_of_isLevelSphericalOfType (hfs m).1 (hfs m).2.1
      have hRb : ∀ m, convOp K (fs m) b ∈ W π :=
        fun m => hRW π (fs m) (hadm m).1 (hadm m).2.1 (hadm m).2.2.1 (hadm m).2.2.2 b hb
      have hzero : ∀ m, ip Φ (convOp K (fs m) b) v = 0 := by
        intro m
        rw [hadj b v (hWl π _ hb) hv (hWc π _ hb) hvc (hW2 π _ hb) hv₂ (fs m) (hadm m).1 (hadm m).2.1]
        have hfl : (fun y => conj (fs m y⁻¹) *
            ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) = fs m :=
          (hfs m).2.2
        rw [hfl]
        have hmem : rightConv K v (fs m) ∈ W Ψ' :=
          hR (fs m) (hadm m).1 (hadm m).2.1 (hadm m).2.2.1 (hadm m).2.2.2
        exact hperp π hπ hπΨ b hb _ hmem

      let lam : W π →ₗ[ℂ] ℂ :=
        { toFun := fun y => ip Φ (y : AdelicGL2 (𝓞 K) K → ℂ) v
          map_add' := fun y₁ y₂ => by
            simp only [Submodule.coe_add]
            exact ip_add_left (hW2 π _ y₁.2) (hW2 π _ y₂.2) hv₂
          map_smul' := fun c y => by
            simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
            exact ip_smul_left c _ _ }
      have hlamc : Continuous lam := LinearMap.continuous_of_finiteDimensional lam
      let ys : ℕ → W π := fun m => ⟨convOp K (fs m) b, hRb m⟩
      have hys : Filter.Tendsto ys Filter.atTop (nhds ⟨b, hb⟩) := by
        rw [tendsto_subtype_rng]
        exact tendsto_pi_nhds.2 fun g => htend b hb g
      have hlim : Filter.Tendsto (fun m => lam (ys m)) Filter.atTop (nhds (lam ⟨b, hb⟩)) :=
        (hlamc.tendsto _).comp hys
      have hconst : (fun m => lam (ys m)) = fun _ => (0 : ℂ) := funext fun m => hzero m
      rw [hconst] at hlim
      have h3 : lam ⟨b, hb⟩ = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
      have h4 : ip Φ b v = 0 := h3
      rw [← conj_ip, h4, map_zero]

end R4ProjCore

end

open R4ProjCore in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (tys : ArchTypeFamily K)
    (Ψ' : HeckeEigensystem K ℂ) (hΨ'N : Ψ'.level = N) (hΨ'S : ∀ w ∈ S, Ψ'.a w = 0 ∧ Ψ'.b w = 0)
    (v : AdelicGL2 (𝓞 K) K → ℂ) (hv : IsLsXiFunction (𝓞 K) K ⊤ ξ v) (hvc : Continuous v)
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ))
    (hR : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
        IsArchBiFinite K tys f →
      convOp K f v ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ' ⊓ archCutSubmodule K tys) :
    ∃ u₁ ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ' ⊓ archCutSubmodule K tys,
      (∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
          IsArchBiFinite K tys f →
        convOp K f v = convOp K f u₁) ∧
      ∀ π ∈ cuspClasses K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S,
      ∀ b ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys,
        ∫ x in Φ, v x * conj (b x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          ∫ x in Φ, u₁ x * conj (b x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
  main K α β hα hαβ Φ hΦs hΦ ξ S N hN tys Ψ' hΨ'N hΨ'S v hv hvc hv₂ hR

end S_AutomorphicForm_exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab (solution)
