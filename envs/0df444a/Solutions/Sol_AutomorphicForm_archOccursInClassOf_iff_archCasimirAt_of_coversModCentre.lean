-- Prove2me | solution 1 for AutomorphicForm.archOccursInClassOf_iff_archCasimirAt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/76c64827-d291-55cf-b07e-7778b24dc045

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_AutomorphicForm_exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous
import Theorems.Thm_LanglandsTunnell_isArchHolomorphicAt_of_agreesAwayFromFinite_of_weightOne_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_forall_archOccursInClassOf_and_centralExponent
import Theorems.Thm_AutomorphicForm_isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_lower_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archCasimirAt_of_coversModCentre
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.whittakerCoefficient_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply"
p2m_attr_erase "simp" "Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AutomorphicForm.rightTranslationEmbed_smul_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace Ws23
namespace L2Reduce

variable {F : Type} [Field F] [NumberField F]

theorem archWeightCharAt_eq {w : InfinitePlace F} (hw : w.IsReal) (n : ℤ) :
    archWeightCharAt hw n =
      (archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)) :=
  rfl

theorem archWeightCharℝ_one_comp {w : InfinitePlace F} (hw : w.IsReal) :
    (archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)) =
      archWeightOneAt hw := by
  ext k
  simp [archWeightCharℝ, archWeightOneAt]

theorem cpow_exponent_eq_one {c₀ : ℂ} (h : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → (((t : ℝ) : ℂ) ^ c₀) = ((t : ℝ) : ℂ)) :
    c₀ = 1 := by

  have h1 : ∀ s : ℝ, Complex.exp ((s : ℂ) * (c₀ - 1)) = 1 := by
    intro s
    have hpos : (0 : ℝ) < Real.exp s := Real.exp_pos s
    have ht := h (Units.mk0 (Real.exp s) hpos.ne') hpos
    simp only [Units.val_mk0, Complex.ofReal_exp] at ht
    rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le)] at ht
    rw [mul_sub, mul_one, Complex.exp_sub, ht, div_self (Complex.exp_ne_zero _)]
  have hd : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * (c₀ - 1))) ((1 : ℂ) * (c₀ - 1) * Complex.exp ((((0 : ℝ) : ℂ)) * (c₀ - 1))) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (c₀ - 1)).cexp
    simpa using this
  have hconst : (fun s : ℝ => Complex.exp ((s : ℂ) * (c₀ - 1))) = fun _ => (1 : ℂ) := funext h1
  rw [hconst] at hd
  have h0 := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, one_mul] at h0
  exact sub_eq_zero.mp h0

set_option maxHeartbeats 3200000 in

theorem main (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (w : InfinitePlace F) (hw : w.IsReal) :
    (∀ χ : rowIsometrySubgroup₀ ℝ →* ℂˣ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) ↔
        ∃ n : ℤ, χ = archWeightCharℝ n ∧ ∃ lam : ℂ,
          ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ)) ∧
    (∀ k : ℤ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchLowestWeightAt w hw φ) ↔
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • φ)) ∧
    (ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchHolomorphicAt w hw φ) ↔
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = ((1 / 4 : ℂ)) • φ ∧
            ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w
                  (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) * φ g)) ∧
    (ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ ¬ IsArchHolomorphicAt w hw φ) ↔
      (∃ lam : ℂ, ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ)) ∧
        ¬ ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = ((1 / 4 : ℂ)) • φ ∧
            ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w
                  (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) * φ g)) ∧
    (∀ (n n' : ℤ) (lam lam' : ℂ),
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) →
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n').comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam') • φ) →
        lam = lam') := by
  classical

  obtain ⟨lam, hrig, hexist0⟩ :=
    AutomorphicForm.exists_forall_archCasimirAt_eq_and_archOccursInClassOf_isArchSmoothAt_of_coversModCentre
      F c u d₁ d₂ T hd hcov Θ w hw
  have hexist : ∀ n : ℤ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) →
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ) :=
    fun n h ↦ (hexist0 n h).mono fun φ hφ ↦ ⟨hφ.1, hφ.2.1, hφ.2.2.2⟩

  obtain ⟨c₀, hc₀⟩ := AutomorphicForm.exists_forall_archOccursInClassOf_and_centralExponent F c u d₁ d₂ T Θ w hw

  have c5 : ∀ (n n' : ℤ) (mu mu' : ℂ),
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (mu) • φ) →
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n').comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (mu') • φ) →
        mu = mu' := fun n n' mu mu' h h' ↦ (hrig n mu h).trans (hrig n' mu' h').symm

  have c1 : ∀ χ : rowIsometrySubgroup₀ ℝ →* ℂˣ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) ↔
        ∃ n : ℤ, χ = archWeightCharℝ n ∧ ∃ lam : ℂ,
          ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) := by
    intro χ
    constructor
    · rintro ⟨Θ', hΘ', R', hR', hP⟩
      obtain ⟨n, rfl⟩ := AutomorphicForm.exists_eq_archWeightCharReal_of_hasArchCharacterAt_of_continuous F w hw χ
        R'.toFun hR' R'.exists_ne_zero hP
      exact ⟨n, rfl, lam, hexist n (⟨Θ', hΘ', R', hR', hP⟩)⟩
    · rintro ⟨n, rfl, mu, h⟩
      exact h.mono fun φ hφ ↦ hφ.1

  have c2 : ∀ k : ℤ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchLowestWeightAt w hw φ) ↔
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • φ) := by
    intro k
    constructor
    · intro h
      refine (hc₀ _ h).mono fun φ hφ ↦ ?_
      obtain ⟨⟨hk, hlw⟩, hcent⟩ := hφ
      have hb := AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
        F hw φ k c₀ hk hcent
      obtain ⟨hs, hL⟩ := hb.1.mp hlw
      exact ⟨hk, hs, AutomorphicForm.archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt F hw φ hs k hk hL⟩
    · intro h

      have hlam : ((k : ℂ) / 2) * (1 - (k : ℂ) / 2) = lam := hrig k _ h
      have hreg := hexist0 k (h.mono fun φ hφ ↦ hφ.1)

      have hL0 := AutomorphicForm.archOccursInClassOf_lower_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
        F c u d₁ d₂ T hd hcov Θ w hw k
        (fun φ => (∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
            φ (adelicArchGLInclAt F w
                (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g) ∧
          HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ)
        ((hc₀ _ hreg).mono fun φ hφ ↦
          ⟨⟨hφ.2, hφ.1.1, hφ.1.2.1⟩, hφ.1.1, hφ.1.2.1, hφ.1.2.2.1, by rw [hlam]; exact hφ.1.2.2.2⟩)

      refine hL0.mono fun φ hφ ↦ ?_
      obtain ⟨⟨hcent, hk, hs⟩, hL⟩ := hφ
      have hb := AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
        F hw φ k c₀ hk hcent
      exact ⟨hk, hb.1.mpr ⟨hs, hL⟩⟩

  have c3 : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchHolomorphicAt w hw φ) ↔
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = ((1 / 4 : ℂ)) • φ ∧
            ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w
                  (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) * φ g) := by
    constructor
    · rintro ⟨Θ', hΘ', R', hR', hk, hhol⟩
      obtain ⟨Θ'', hΘ'', R'', hR'', ⟨hk', hhol'⟩, hcent⟩ :=
        hc₀ (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
          IsArchHolomorphicAt w hw φ) ⟨Θ', hΘ', R', hR', hk, hhol⟩
      have hb := AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
        F hw R''.toFun 1 c₀ hk' hcent
      obtain ⟨hs, hL, hμ⟩ := hb.2.mp hhol'

      have hc1 : c₀ = 1 := by
        obtain ⟨g₀, hg₀⟩ := R''.exists_ne_zero
        have := congrFun hμ g₀
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero, hg₀, or_false] at this
        have : (1 : ℂ) + c₀ - 2 = 0 := by exact_mod_cast this
        linear_combination this
      subst hc1
      refine ⟨Θ'', hΘ'', R'', hR'', hk', hs, ?_, fun t ht g ↦ ?_⟩
      · rw [AutomorphicForm.archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt F hw R''.toFun hs 1 hk' hL]
        norm_num
      · rw [hcent t ht g, Complex.cpow_one]
    · intro h

      have h' : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = ((((1 : ℤ) : ℂ) / 2) * (1 - ((1 : ℤ) : ℂ) / 2)) • φ) := by
        refine h.mono fun φ hφ ↦ ⟨hφ.1, hφ.2.1, ?_⟩
        rw [hφ.2.2.1]; norm_num

      have hc1 : c₀ = 1 := by
        obtain ⟨Θ', hΘ', R', hR', ⟨-, -, -, hone⟩, hcent⟩ := hc₀ _ h
        obtain ⟨g₀, hg₀⟩ := R'.exists_ne_zero
        refine cpow_exponent_eq_one fun t ht ↦ ?_
        have h1 := hcent t ht g₀
        rw [hone t ht g₀] at h1
        exact (mul_right_cancel₀ hg₀ h1).symm
      subst hc1

      obtain ⟨Θ', hΘ', R', hR', ⟨hk, hlw⟩, hcent⟩ := hc₀ _ ((c2 1).mpr h')
      have hb := AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
        F hw R'.toFun 1 1 hk hcent
      obtain ⟨hs, hL⟩ := hb.1.mp hlw
      exact ⟨Θ', hΘ', R', hR', hk, hb.2.mpr ⟨hs, hL, by norm_num⟩⟩
  have c4 : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ ¬ IsArchHolomorphicAt w hw φ) ↔
      (∃ lam : ℂ, ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ)) ∧
        ¬ ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = ((1 / 4 : ℂ)) • φ ∧
            ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w
                  (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) * φ g) := by
    constructor
    · rintro ⟨Θ', hΘ', R', hR', hk, hnh⟩
      refine ⟨⟨lam, hexist 1 (⟨Θ', hΘ', R', hR', hk⟩)⟩, fun h14 ↦ hnh ?_⟩
      obtain ⟨Θ'', hΘ'', R'', hR'', hk'', hhol''⟩ := c3.mpr h14
      have hk1 : HasArchCharacterAt₀ F w (archWeightOneAt hw) R''.toFun := by rwa [archWeightCharℝ_one_comp hw] at hk''
      have hk2 : HasArchCharacterAt₀ F w (archWeightOneAt hw) R'.toFun := by
        have := hk; rwa [archWeightCharℝ_one_comp hw] at this
      exact LanglandsTunnell.isArchHolomorphicAt_of_agreesAwayFromFinite_of_weightOne_of_coversModCentre F c u d₁ d₂ T
        hd hcov Θ'' Θ' (TranslateSpanOccurrence.agrees_trans hΘ'' (TranslateSpanOccurrence.agrees_symm hΘ'))
        R'' hR'' R' hR' w hw hk1 hhol'' hk2
    · rintro ⟨⟨mu, h⟩, hno⟩
      obtain ⟨Θ', hΘ', R', hR', ⟨hk, hs, hΩ⟩, hcent⟩ := hc₀ _ h
      refine ⟨Θ', hΘ', R', hR', hk, fun hhol ↦ hno ?_⟩
      have hb := AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt
        F hw R'.toFun 1 c₀ hk hcent
      obtain ⟨-, hL, hμ⟩ := hb.2.mp hhol
      have hc1 : c₀ = 1 := by
        obtain ⟨g₀, hg₀⟩ := R'.exists_ne_zero
        have := congrFun hμ g₀
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_eq_zero, hg₀, or_false] at this
        have : (1 : ℂ) + c₀ - 2 = 0 := by exact_mod_cast this
        linear_combination this
      subst hc1
      refine ⟨Θ', hΘ', R', hR', hk, hs, ?_, fun t ht g ↦ ?_⟩
      · rw [AutomorphicForm.archCasimirAt_eq_smul_of_lower_eq_zero_of_hasArchCharacterAt F hw R'.toFun hs 1 hk hL]
        norm_num
      · rw [hcent t ht g, Complex.cpow_one]
  exact ⟨c1, c2, c3, c4, c5⟩

end Ws23.L2Reduce

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (w : InfinitePlace F) (hw : w.IsReal) :
    (∀ χ : rowIsometrySubgroup₀ ℝ →* ℂˣ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w (χ.comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) ↔
        ∃ n : ℤ, χ = archWeightCharℝ n ∧ ∃ lam : ℂ,
          ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ)) ∧
    (∀ k : ℤ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchLowestWeightAt w hw φ) ↔
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (((k : ℂ) / 2) * (1 - (k : ℂ) / 2)) • φ)) ∧
    (ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchHolomorphicAt w hw φ) ↔
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = ((1 / 4 : ℂ)) • φ ∧
            ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w
                  (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) * φ g)) ∧
    (ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ ¬ IsArchHolomorphicAt w hw φ) ↔
      (∃ lam : ℂ, ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ)) ∧
        ¬ ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = ((1 / 4 : ℂ)) • φ ∧
            ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
              φ (adelicArchGLInclAt F w
                  (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) * φ g)) ∧
    (∀ (n n' : ℤ) (lam lam' : ℂ),
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) →
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n').comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam') • φ) →
        lam = lam') :=
  Ws23.L2Reduce.main c u d₁ d₂ T hd hcov Θ hΘ w hw

#print axioms solution

end S_AutomorphicForm_archOccursInClassOf_iff_archCasimirAt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_archOccursInClassOf_iff_archCasimirAt_of_coversModCentre (solution)
