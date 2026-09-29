-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c22a9a96-b430-5584-af42-7238c07b9dbf

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le
import Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
import Theorems.Thm_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
import Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal"
p2m_attr_erase "simp" "LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar NumberField.InfinitePlace
p2m_open "AutomorphicForm~archDerivAtComplex_comp_mul_left~archDerivAtComplex_smul AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open IsDedekindDomain
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace SupNormAssembly

variable {K : Type} [Field K] [NumberField K]

abbrev Dir (K : Type) [Field K] [NumberField K] : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

abbrev D1 (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d

abbrev Wd (l : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b

theorem Wd_nil (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd [] b = b := rfl

theorem Wd_cons (d : Dir K) (l : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd (d :: l) b = D1 d (Wd l b) := rfl

theorem archDerivAtComplex_comp_mul_left {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d (fun g => φ (h * g)) = fun g => archDerivAtComplex hw d φ (h * g) := by
  funext g
  show deriv (fun t : ℝ => φ (h * (g * archFlowAtComplex hw d t))) 0 =
    deriv (fun t : ℝ => φ (h * g * archFlowAtComplex hw d t)) 0
  simp only [mul_assoc]

theorem archDerivAtComplex_smul {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) (c : ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) : archDerivAtComplex hw d (c • φ) = c • archDerivAtComplex hw d φ := by
  funext g
  show deriv (fun t : ℝ => (c • φ) (g * archFlowAtComplex hw d t)) 0 =
    c • deriv (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) 0
  simp only [Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem D1_comp_mul_left (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : AdelicGL2 (𝓞 K) K) :
    D1 d (fun g => φ (h * g)) = fun g => D1 d φ (h * g) := by
  rcases d with ⟨w, hw, d⟩ | ⟨w, hw, d⟩
  · exact archDerivAt_comp_mul_left hw d φ h
  · exact archDerivAtComplex_comp_mul_left hw d φ h

theorem D1_smul (d : Dir K) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : D1 d (c • φ) = c • D1 d φ := by
  rcases d with ⟨w, hw, d⟩ | ⟨w, hw, d⟩
  · exact archDerivAt_smul hw d c φ
  · exact archDerivAtComplex_smul hw d c φ

theorem Wd_comp_mul_left (l : List (Dir K)) (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : AdelicGL2 (𝓞 K) K) :
    Wd l (fun g => φ (h * g)) = fun g => Wd l φ (h * g) := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [Wd_cons, Wd_cons, ih, D1_comp_mul_left]

theorem Wd_smul (l : List (Dir K)) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : Wd l (c • φ) = c • Wd l φ := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [Wd_cons, Wd_cons, ih, D1_smul]

theorem isLsXiFunction_Wd {Z : Subgroup (AdeleRing (𝓞 K) K)ˣ} {ξ : Z →* ℂˣ} {b : AdelicGL2 (𝓞 K) K → ℂ}
    (hb : IsLsXiFunction (𝓞 K) K Z ξ b) (l : List (Dir K)) : IsLsXiFunction (𝓞 K) K Z ξ (Wd l b) := by
  refine ⟨fun γ g => ?_, fun z g => ?_⟩
  · have h := Wd_comp_mul_left l b (globalPoints (𝓞 K) K γ)
    have hb' : (fun g => b (globalPoints (𝓞 K) K γ * g)) = b := funext fun g => hb.left_invariant γ g
    rw [hb'] at h
    exact (congrFun h g).symm
  · have h := Wd_comp_mul_left l b (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ))
    have hb' : (fun g => b (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g)) = ((ξ z : ℂˣ) : ℂ) • b :=
      funext fun g => by rw [Pi.smul_apply, smul_eq_mul]; exact hb.central_transform z g
    rw [hb', Wd_smul] at h
    have := congrFun h g
    rw [Pi.smul_apply, smul_eq_mul] at this
    exact this.symm

end SupNormAssembly

namespace SupNormAssembly

open NumberField.InfinitePlace.Completion
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

theorem scalar_apply_eq' {R : Type*} [CommRing R] (a : R) (i : Fin 2) : Matrix.scalar (Fin 2) a i i = a := by
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]

theorem scalar_apply_ne' {R : Type*} [CommRing R] (a : R) {i j : Fin 2} (h : i ≠ j) : Matrix.scalar (Fin 2) a i j = 0 := by
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]

theorem coe_GLscalar {R : Type*} [CommRing R] (u : Rˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = Matrix.scalar (Fin 2) (u : R) := rfl

def zR {w : InfinitePlace K} (hw : w.IsReal) : ℝˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (NumberField.TateGlobal.archUnitHom w).comp (Units.map (ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom)

def zC {w : InfinitePlace K} (hw : w.IsComplex) : ℂˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (NumberField.TateGlobal.archUnitHom w).comp (Units.map (ringEquivComplexOfIsComplex hw).symm.toRingHom.toMonoidHom)

theorem archUnitHom_val_fst (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ((NumberField.TateGlobal.archUnitHom w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 =
      Function.update (1 : InfiniteAdeleRing K) w (a : w.Completion) := rfl

theorem archUnitHom_val_snd (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ((NumberField.TateGlobal.archUnitHom w a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem glFin_centralScalar_archUnitHom (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    glFin (𝓞 K) K (centralScalar (𝓞 K) K (NumberField.TateGlobal.archUnitHom w a)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply]
  show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (NumberField.TateGlobal.archUnitHom w a) :
      GL (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 = (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
  rw [coe_GLscalar, Units.val_one]
  by_cases hij : i = j
  · subst hij; rw [scalar_apply_eq', Matrix.one_apply_eq]; rfl
  · rw [scalar_apply_ne' _ hij, Matrix.one_apply_ne hij]; rfl

theorem glArch_centralScalar_archUnitHom (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    glArch (𝓞 K) K (centralScalar (𝓞 K) K (NumberField.TateGlobal.archUnitHom w a)) =
      archGLIncl K w (Matrix.GeneralLinearGroup.scalar (Fin 2) a) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glArch_apply]
  show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (NumberField.TateGlobal.archUnitHom w a) :
      GL (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 = archMatrixUpdate K w (Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) w.Completion) i j
  funext v
  rw [coe_GLscalar, coe_GLscalar]
  by_cases hv : v = w
  · subst hv
    rw [archMatrixUpdate_apply_self]
    by_cases hij : i = j
    · subst hij; rw [scalar_apply_eq', scalar_apply_eq', archUnitHom_val_fst, Function.update_self]
    · rw [scalar_apply_ne' _ hij, scalar_apply_ne' _ hij]; rfl
  · rw [archMatrixUpdate_apply_of_ne K w _ i j hv]
    by_cases hij : i = j
    · subst hij; rw [scalar_apply_eq', Matrix.one_apply_eq, archUnitHom_val_fst, Function.update_of_ne hv]; rfl
    · rw [scalar_apply_ne' _ hij, Matrix.one_apply_ne hij]; rfl

theorem archRealGLAt_scalar {w : InfinitePlace K} (hw : w.IsReal) (t : ℝˣ) :
    archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t) =
      centralScalar (𝓞 K) K (zR hw t) := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [zR, MonoidHom.comp_apply, glArch_centralScalar_archUnitHom]
    show glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm _))) = _
    rw [glArch_adelicArchGLIncl]
    congr 1
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glEquivOfRingEquiv_apply_entry, coe_GLscalar]
    show (ringEquivRealOfIsReal hw).symm ((Matrix.scalar (Fin 2) (t : ℝ)) i j) = _
    by_cases hij : i = j
    · subst hij; rw [scalar_apply_eq', scalar_apply_eq']; rfl
    · rw [scalar_apply_ne' _ hij, scalar_apply_ne' _ hij, map_zero]
  · rw [zR, MonoidHom.comp_apply, glFin_centralScalar_archUnitHom]
    exact glFin_adelicArchGLIncl K _

theorem archComplexGLAt_scalar {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂˣ) :
    archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z) =
      centralScalar (𝓞 K) K (zC hw z) := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [zC, MonoidHom.comp_apply, glArch_centralScalar_archUnitHom]
    show glArch (𝓞 K) K (adelicArchGLIncl K (archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm _))) = _
    rw [glArch_adelicArchGLIncl]
    congr 1
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glEquivOfRingEquiv_apply_entry, coe_GLscalar]
    show (ringEquivComplexOfIsComplex hw).symm ((Matrix.scalar (Fin 2) (z : ℂ)) i j) = _
    by_cases hij : i = j
    · subst hij; rw [scalar_apply_eq', scalar_apply_eq']; rfl
    · rw [scalar_apply_ne' _ hij, scalar_apply_ne' _ hij, map_zero]
  · rw [zC, MonoidHom.comp_apply, glFin_centralScalar_archUnitHom]
    exact glFin_adelicArchGLIncl K _

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    g * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * (Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) _) = _
  rw [coe_GLscalar]
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 K) K) (fun r => mul_comm _ r) _).symm.eq

theorem continuous_zR {w : InfinitePlace K} (hw : w.IsReal) : Continuous (zR (K := K) hw) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t : ℝˣ => ((zR (K := K) hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    have : (fun t : ℝˣ => ((zR (K := K) hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
        fun t : ℝˣ => (Function.update (1 : InfiniteAdeleRing K) w ((ringEquivRealOfIsReal hw).symm (t : ℝ)), (1 : FiniteAdeleRing (𝓞 K) K)) := by
      funext t; rfl
    rw [this]
    refine Continuous.prodMk ?_ continuous_const
    exact continuous_const.update w ((isometryEquivRealOfIsReal hw).symm.continuous.comp Units.continuous_val)
  · show Continuous fun t : ℝˣ => (((zR (K := K) hw t)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    have : (fun t : ℝˣ => (((zR (K := K) hw t)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
        fun t : ℝˣ => (Function.update (1 : InfiniteAdeleRing K) w ((ringEquivRealOfIsReal hw).symm ((t⁻¹ : ℝˣ) : ℝ)), (1 : FiniteAdeleRing (𝓞 K) K)) := by
      funext t; rw [← map_inv]; rfl
    rw [this]
    refine Continuous.prodMk ?_ continuous_const
    exact continuous_const.update w ((isometryEquivRealOfIsReal hw).symm.continuous.comp (Units.continuous_val.comp continuous_inv))

end SupNormAssembly

namespace SupNormAssembly

open NumberField.InfinitePlace.Completion
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

theorem continuous_zC {w : InfinitePlace K} (hw : w.IsComplex) : Continuous (zC (K := K) hw) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t : ℂˣ => ((zC (K := K) hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    have : (fun t : ℂˣ => ((zC (K := K) hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
        fun t : ℂˣ => (Function.update (1 : InfiniteAdeleRing K) w ((ringEquivComplexOfIsComplex hw).symm (t : ℂ)), (1 : FiniteAdeleRing (𝓞 K) K)) := by
      funext t; rfl
    rw [this]
    refine Continuous.prodMk ?_ continuous_const
    exact continuous_const.update w ((isometryEquivComplexOfIsComplex hw).symm.continuous.comp Units.continuous_val)
  · show Continuous fun t : ℂˣ => (((zC (K := K) hw t)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
    have : (fun t : ℂˣ => (((zC (K := K) hw t)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
        fun t : ℂˣ => (Function.update (1 : InfiniteAdeleRing K) w ((ringEquivComplexOfIsComplex hw).symm ((t⁻¹ : ℂˣ) : ℂ)), (1 : FiniteAdeleRing (𝓞 K) K)) := by
      funext t; rw [← map_inv]; rfl
    rw [this]
    refine Continuous.prodMk ?_ continuous_const
    exact continuous_const.update w ((isometryEquivComplexOfIsComplex hw).symm.continuous.comp (Units.continuous_val.comp continuous_inv))

section Unpack

variable {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
  {Φ : HeckeEigensystem K ℂ}

theorem isLsXiFunction_of_mem (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : φ ∈ isotypicCuspSubmodule K pins ξ N S Φ) :
    IsLsXiFunction (𝓞 K) K pins.Z ξ φ := by
  refine Submodule.span_induction (p := fun φ _ => IsLsXiFunction (𝓞 K) K pins.Z ξ φ) ?_ ?_ ?_ ?_ h
  · intro φ hφ
    have h1 : IsAutomorphicFnAt K pins ξ φ := hφ.smoothCusp.1.1
    exact ((@lsXiMemberAt_iff (𝓞 K) K _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D φ).mp h1).1
  · exact isLsXiFunction_zero (𝓞 K) K pins.Z ξ
  · intro u v _ _ hu hv
    exact ⟨fun γ g => by rw [Pi.add_apply, Pi.add_apply, hu.left_invariant, hv.left_invariant],
      fun z g => by rw [Pi.add_apply, Pi.add_apply, hu.central_transform, hv.central_transform, mul_add]⟩
  · intro c u _ hu
    exact ⟨fun γ g => by rw [Pi.smul_apply, Pi.smul_apply, hu.left_invariant],
      fun z g => by rw [Pi.smul_apply, Pi.smul_apply, hu.central_transform, smul_eq_mul, smul_eq_mul]; ring⟩

theorem memLp_of_mem {D : Set (AdelicGL2 (𝓞 K) K)} {U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)}
    {gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K} {B : Set (AdeleRing (𝓞 K) K)}
    {ξ₀ : (productionPinsOf K D U gen B).Z →* ℂˣ}
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : φ ∈ isotypicCuspSubmodule K (productionPinsOf K D U gen B) ξ₀ N S Φ) :
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D) := by
  refine Submodule.span_induction (p := fun φ _ => MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict D)) ?_ ?_ ?_ ?_ h
  · intro φ hφ
    have h1 : IsAutomorphicFnAt K (productionPinsOf K D U gen B) ξ₀ φ := hφ.smoothCusp.1.1
    exact ((lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξ₀ D φ).mp h1).2
  · exact MemLp.zero
  · intro u v _ _ hu hv; exact hu.add hv
  · intro c u _ hu; exact hu.const_smul c

theorem level_invariant_of_mem (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : φ ∈ isotypicCuspSubmodule K pins ξ N S Φ) :
    ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ pins.U N, φ (g * u) = φ g := by
  refine Submodule.span_induction (p := fun φ _ => ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ pins.U N, φ (g * u) = φ g) ?_ ?_ ?_ ?_ h
  · exact fun φ hφ => hφ.level_invariant
  · exact fun _ _ _ => rfl
  · intro u v _ _ hu hv g k hk; rw [Pi.add_apply, Pi.add_apply, hu g k hk, hv g k hk]
  · intro c u _ hu g k hk; rw [Pi.smul_apply, Pi.smul_apply, hu g k hk]

end Unpack

private theorem _root_.SupNormAssembly.exists_notMem_finset (T : Finset (HeightOneSpectrum (𝓞 K))) : ∃ v : HeightOneSpectrum (𝓞 K), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "SupNormAssembly" "exists_notMem_finset"
theorem ne_bot_of_forall_dvd_mem (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S) : N ≠ ⊥ := by
  rintro rfl
  obtain ⟨w, hw⟩ := exists_notMem_finset S
  exact hw (hN w ⟨⊥, by rw [Ideal.mul_bot]⟩)

end SupNormAssembly

open SupNormAssembly NumberField.InfinitePlace.Completion in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    ∃ Cst A : ℝ, 0 ≤ Cst ∧ 0 ≤ A ∧
      ∀ (π : HeckeEigensystem K ℂ) (Λ : ℝ), 1 ≤ Λ →
        (∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ lam : ℂ, ‖lam‖ ≤ Λ ∧
          ∀ b ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
            IsArchSmoothAt hw b ∧ archCasimirAt hw b = lam • b) →
        (∀ (w : InfinitePlace K) (hw : w.IsComplex), ∃ lam lam' : ℂ, ‖lam‖ ≤ Λ ∧ ‖lam'‖ ≤ Λ ∧
          ∀ b ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
            IsArchSmoothAtComplex hw b ∧ archCasimirAtComplex hw b = lam • b ∧
              archCasimirBarAtComplex hw b = lam' • b) →
        ∀ b ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
              (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
          ∀ x ∈ C,
            ‖b x‖ ≤ Cst * Λ ^ A *
              (eLpNorm b 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
                (AutomorphicForm.canonicalTruncationDomain K α β))).toReal := by
  classical
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set Φ₀ := AutomorphicForm.canonicalTruncationDomain K α β with hΦ₀
  set nK : ℕ := 4 * nrRealPlaces K + 8 * nrComplexPlaces K with hnK
  have hN0 : N ≠ ⊥ := ne_bot_of_forall_dvd_mem SK N hN

  let ξ' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ξK.comp (Subgroup.topEquiv : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ≃* _).symm.toMonoidHom
  have hξ' : ∀ z, ξ' z = ξK ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  let ωR : ∀ w : InfinitePlace K, w.IsReal → (ℝˣ →* ℂˣ) := fun w hw => ξ'.comp (zR hw)
  let ωC : ∀ w : InfinitePlace K, w.IsComplex → (ℂˣ →* ℂˣ) := fun w hw => ξ'.comp (zC hw)
  have hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal), Continuous fun t : ℝˣ => ((ωR w hw t : ℂˣ) : ℂ) :=
    fun w hw => hξc.comp (continuous_zR hw)
  have hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), Continuous fun z : ℂˣ => ((ωC w hw z : ℂˣ) : ℂ) :=
    fun w hw => hξc.comp (continuous_zC hw)

  have H2 : ∃ C' : Set (AdelicGL2 (𝓞 K) K), IsCompact C' ∧ C ⊆ C' ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, b (g * u) = b g) →
        (∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ) (g : AdelicGL2 (𝓞 K) K),
            b (g * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t)) =
              ((ωR w hw t : ℂˣ) : ℂ) * b g) →
        (∀ (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ) (g : AdelicGL2 (𝓞 K) K),
            b (g * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z)) =
              ((ωC w hw z : ℂˣ) : ℂ) * b g) →
        (∀ l, l.length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K →
          Continuous (Wd l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (Wd l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (Wd l b))) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ l, l.length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K →
            eLpNorm (Wd l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict C') ≤ ENNReal.ofReal M) →
          ∀ x ∈ C, ‖b x‖ ≤ c * M :=
    AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le K N hN0 ωR hωR ωC hωC C hC
  obtain ⟨C', hC'c, hCC', c₂, hc₂, H2⟩ := H2
  obtain ⟨c₄, H4⟩ :=
    AutomorphicForm.exists_forall_eLpNorm_restrict_le_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isLsXiFunction
      K α β hα hαβ ξK hξc C' hC'c
  have H3 : ∃ c : ℝ, 0 ≤ c ∧
      ∀ (Λ : ℝ), 1 ≤ Λ →
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), b (globalPoints (𝓞 K) K γ * g) = b g) →
        b ∈ archCutSubmodule K tysK →
        (∀ l, l.length ≤ nK + 2 →
          Continuous (Wd l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (Wd l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (Wd l b)) ∧
          ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖Wd l b g‖ ≤ B) →
        (∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ lam : ℂ, ‖lam‖ ≤ Λ ∧ archCasimirAt hw b = lam • b) →
        (∀ (w : InfinitePlace K) (hw : w.IsComplex), ∃ lam lam' : ℂ, ‖lam‖ ≤ Λ ∧ ‖lam'‖ ≤ Λ ∧
          archCasimirAtComplex hw b = lam • b ∧ archCasimirBarAtComplex hw b = lam' • b) →
        ∀ l, l.length ≤ nK →
          eLpNorm (Wd l b) 2 (μ.restrict Φ₀) ≤ ENNReal.ofReal (c * Λ ^ ((l.length : ℝ) / 2)) * eLpNorm b 2 (μ.restrict Φ₀) :=
    AutomorphicForm.exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
      K α β hα hαβ tysK nK
  obtain ⟨c₃, hc₃, H3⟩ := H3
  refine ⟨c₂ * ((c₄ : ℝ) * c₃), (nK : ℝ) / 2, by positivity, by positivity, ?_⟩
  intro π Λ hΛ HR HC b hb x hx
  have hbV := (Submodule.mem_inf.mp hb).1
  have hbT := (Submodule.mem_inf.mp hb).2
  have hLs : IsLsXiFunction (𝓞 K) K ⊤ ξK b := isLsXiFunction_of_mem b hbV
  have hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, b (g * u) = b g :=
    level_invariant_of_mem b hbV
  have hL2 : MemLp b 2 (μ.restrict Φ₀) := memLp_of_mem b hbV

  have hreg : ∀ l, Continuous (Wd l b) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (Wd l b)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (Wd l b)) ∧
      ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖Wd l b g‖ ≤ B :=
    AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
      K α β hα hαβ ξK hξc hξt SK N hN tysK π b hb
      (fun w hw => by obtain ⟨lam, -, h⟩ := HR w hw; exact ⟨(h b hb).1, lam, (h b hb).2⟩)
      (fun w hw => by obtain ⟨lam, lam', -, -, h⟩ := HC w hw; exact ⟨(h b hb).1, lam, lam', (h b hb).2.1, (h b hb).2.2⟩)

  have hCR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ lam : ℂ, ‖lam‖ ≤ Λ ∧ archCasimirAt hw b = lam • b :=
    fun w hw => by obtain ⟨lam, hl, h⟩ := HR w hw; exact ⟨lam, hl, (h b hb).2⟩
  have hCC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ∃ lam lam' : ℂ, ‖lam‖ ≤ Λ ∧ ‖lam'‖ ≤ Λ ∧
      archCasimirAtComplex hw b = lam • b ∧ archCasimirBarAtComplex hw b = lam' • b :=
    fun w hw => by obtain ⟨lam, lam', hl, hl', h⟩ := HC w hw; exact ⟨lam, lam', hl, hl', (h b hb).2.1, (h b hb).2.2⟩

  set E : ℝ≥0∞ := eLpNorm b 2 (μ.restrict Φ₀) with hE
  have hEfin : E ≠ ⊤ := hL2.eLpNorm_ne_top
  set M : ℝ := ((c₄ : ℝ) * c₃) * Λ ^ ((nK : ℝ) / 2) * E.toReal with hM
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hM0 : 0 ≤ M := by positivity
  have hwords : ∀ l, l.length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K →
      eLpNorm (Wd l b) 2 (μ.restrict C') ≤ ENNReal.ofReal M := by
    intro l hl
    have h3 := H3 Λ hΛ b hLs.left_invariant hbT (fun l' _ => hreg l') hCR hCC l hl
    have h4 := H4 (Wd l b) (isLsXiFunction_Wd hLs l)
      (by
        haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
        exact (hreg l).1.aestronglyMeasurable)
    have hpow : Λ ^ ((l.length : ℝ) / 2) ≤ Λ ^ ((nK : ℝ) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le hΛ
      have : (l.length : ℝ) ≤ (nK : ℝ) := by exact_mod_cast hl
      linarith
    calc eLpNorm (Wd l b) 2 (μ.restrict C') ≤ (c₄ : ℝ≥0∞) * eLpNorm (Wd l b) 2 (μ.restrict Φ₀) := h4
      _ ≤ (c₄ : ℝ≥0∞) * (ENNReal.ofReal (c₃ * Λ ^ ((l.length : ℝ) / 2)) * E) := by gcongr
      _ ≤ (c₄ : ℝ≥0∞) * (ENNReal.ofReal (c₃ * Λ ^ ((nK : ℝ) / 2)) * E) := by
          gcongr
      _ = ENNReal.ofReal M := by
          have hE' : E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hEfin).symm
          have h1 : (c₄ : ℝ≥0∞) = ENNReal.ofReal (c₄ : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
          conv_lhs => rw [hE', h1]
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hM]
          congr 1
          ring

  have hcen_R : ∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ) (g : AdelicGL2 (𝓞 K) K),
      b (g * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t)) =
        ((ωR w hw t : ℂˣ) : ℂ) * b g := by
    intro w hw t g
    rw [archRealGLAt_scalar, centralScalar_comm]
    exact hLs.central_transform ⟨zR hw t, Subgroup.mem_top _⟩ g
  have hcen_C : ∀ (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ) (g : AdelicGL2 (𝓞 K) K),
      b (g * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z)) =
        ((ωC w hw z : ℂˣ) : ℂ) * b g := by
    intro w hw z g
    rw [archComplexGLAt_scalar, centralScalar_comm]
    exact hLs.central_transform ⟨zC hw z, Subgroup.mem_top _⟩ g
  have hfin := H2 b hlev hcen_R hcen_C (fun l _ => ⟨(hreg l).1, (hreg l).2.1, (hreg l).2.2.1⟩) M hM0 hwords x hx
  calc ‖b x‖ ≤ c₂ * M := hfin
    _ = c₂ * ((c₄ : ℝ) * c₃) * Λ ^ ((nK : ℝ) / 2) * E.toReal := by rw [hM]; ring

end

end S_AutomorphicForm_exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact (solution)
