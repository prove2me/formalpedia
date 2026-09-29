-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/7eaa50be-f5e1-5fa1-8da8-268f532d743a

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_AdelicHeight
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchType

import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Theorems.Thm_AutomorphicForm_exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection
import Theorems.Thm_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
import Theorems.Thm_AxisWitness_exists_axisContinuation
import Theorems.Thm_AutomorphicForm_exists_norm_lambdaT_axis_continuation_le_mul_adelicHeight_rpow_neg_of_mem_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply"
p2m_attr_erase "simp" "Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open scoped NNReal

noncomputable section

namespace AbsEisGrowthProof

variable (F : Type) [Field F] [NumberField F]

def sph (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ := ((adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)

theorem sph_apply (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    sph F s g = ((adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2) := rfl

theorem sph_mul_of_mem (s : ℂ) (g k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F) :
    sph F s (g * k) = sph F s g := by
  simp only [sph, NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact F g k hk]

theorem sph_ofReal (σ : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    sph F (σ : ℂ) g = ((adelicHeight F g ^ (σ + 1 / 2) : ℝ) : ℂ) := by
  rw [sph, Complex.ofReal_cpow (adelicHeight_pos g).le]
  push_cast
  rfl

theorem norm_sph_ofReal (σ : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    ‖sph F (σ : ℂ) g‖ = adelicHeight F g ^ (σ + 1 / 2) := by
  rw [sph_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (adelicHeight_pos g).le _)]

theorem archRowIsometrySubgroup_le (w : InfinitePlace F) :
    archRowIsometrySubgroup F w ≤ adelicMaximalCompact F := by
  rintro _ ⟨k, hk, rfl⟩
  rw [mem_adelicMaximalCompact_iff']
  refine ⟨?_, fun v => ?_⟩
  · show glFin (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w k)) ∈ _
    rw [glFin_adelicArchGLIncl]
    exact Subgroup.one_mem _
  · show archComponent F v (glArch (𝓞 F) F (adelicArchGLIncl F (archGLIncl F w k))) ∈ _
    rw [glArch_adelicArchGLIncl]
    by_cases hvw : v = w
    · subst hvw
      rw [archComponent_archGLIncl_self]
      exact hk
    · rw [archComponent_archGLIncl_of_ne F hvw]
      exact Subgroup.one_mem _

theorem mem_adelicMaximalCompact_of_mem_finiteAdelicGL2Subgroup {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ finiteAdelicGL2Subgroup F) (hu' : glFin (𝓞 F) F u ∈ finiteIntegralGL2 (𝓞 F) F) :
    u ∈ adelicMaximalCompact F := by
  rw [mem_adelicMaximalCompact_iff']
  refine ⟨hu', fun v => ?_⟩
  rw [(mem_finiteAdelicGL2Subgroup_iff F u).mp hu, map_one]
  exact Subgroup.one_mem _

theorem sph_isArchKFinite (s : ℂ) : IsArchKFinite F (sph F s) := by
  intro w
  refine ⟨{sph F s}, fun k hk => ?_⟩
  have h : (fun x => sph F s (x * k)) = sph F s :=
    funext fun x => sph_mul_of_mem F s x k (archRowIsometrySubgroup_le F w hk)
  rw [h]
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

theorem sph_isKfSmooth (s : ℂ) : IsKfSmooth F (sph F s) := by
  rw [isKfSmooth_iff]
  rw [FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup]
  refine ⟨(finiteIntegralGL2 (𝓞 F) F).comap
      ((glFin (𝓞 F) F).comp (finiteAdelicGL2Subgroup F).subtype), ?_, ?_⟩
  · have hopen : IsOpen (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
      isOpen_finiteLevelZero (R := 𝓞 F) (K := F) (N := ⊤) (by simp)
    exact hopen.preimage ((continuous_glFin (𝓞 F) F).comp continuous_subtype_val)
  · intro u hu
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul]
    show sph F s (x * (u : AdelicGL2 (𝓞 F) F)) = sph F s x
    exact sph_mul_of_mem F s x u
      (mem_adelicMaximalCompact_of_mem_finiteAdelicGL2Subgroup F u.2 (Subgroup.mem_comap.mp hu))

theorem continuous_sph_uncurry : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => sph F p.1 p.2) := by
  unfold sph
  refine Continuous.cpow ?_ (continuous_fst.add continuous_const) fun p => ?_
  · exact Complex.continuous_ofReal.comp
      ((NumberField.AdelicHeight.continuous_adelicHeight F).comp continuous_snd)
  · left
    rw [Complex.ofReal_re]
    exact adelicHeight_pos _

theorem continuous_sph (s : ℂ) : Continuous (sph F s) :=
  (continuous_sph_uncurry F).uncurry_left s

theorem differentiable_sph (g : AdelicGL2 (𝓞 F) F) : Differentiable ℂ (fun s => sph F s g) := by
  unfold sph
  have h0 : ((adelicHeight F g : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (adelicHeight_pos g).ne'
  intro s
  exact ((differentiableAt_id.add (differentiableAt_const _)).const_cpow (Or.inl h0))

theorem sph_hKu (w : InfinitePlace F) :
    ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        (fun k : ↥(archRowIsometrySubgroup F w) => sph F s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W := by
  refine ⟨Submodule.span ℂ {fun _ => (1 : ℂ)}, ?_, fun s g => ?_⟩
  · exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)
  · have h : (fun k : ↥(archRowIsometrySubgroup F w) => sph F s (g * (k : AdelicGL2 (𝓞 F) F))) =
        sph F s g • fun _ => (1 : ℂ) := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, mul_one]
      exact sph_mul_of_mem F s g k (archRowIsometrySubgroup_le F w k.2)
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

theorem growth_combine (h₀ : ℝ) (hh₀ : 0 < h₀) (M₁ M₂ A : ℝ) :
    ∃ C A' : ℝ, 0 ≤ C ∧ ∀ H : ℝ, h₀ ≤ H → M₁ + M₂ * H ^ A ≤ C * H ^ A' := by
  set A' : ℝ := max A 0 with hA'
  refine ⟨|M₁| * h₀ ^ (-A') + |M₂| * h₀ ^ (A - A'), A', by positivity, fun H hH => ?_⟩
  have hHpos : 0 < H := lt_of_lt_of_le hh₀ hH
  have h1 : (1 : ℝ) ≤ H ^ A' * h₀ ^ (-A') := by
    have : H ^ (-A') ≤ h₀ ^ (-A') :=
      Real.rpow_le_rpow_of_nonpos hh₀ hH (by simp [hA'])
    calc (1 : ℝ) = H ^ A' * H ^ (-A') := by
          rw [← Real.rpow_add hHpos, add_neg_cancel, Real.rpow_zero]
      _ ≤ H ^ A' * h₀ ^ (-A') := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hHpos.le _)
  have h2 : H ^ A ≤ H ^ A' * h₀ ^ (A - A') := by
    have : H ^ (A - A') ≤ h₀ ^ (A - A') :=
      Real.rpow_le_rpow_of_nonpos hh₀ hH (by simp [hA'])
    calc H ^ A = H ^ A' * H ^ (A - A') := by
          rw [← Real.rpow_add hHpos, add_sub_cancel]
      _ ≤ H ^ A' * h₀ ^ (A - A') := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hHpos.le _)
  have hHA' : 0 ≤ H ^ A' := Real.rpow_nonneg hHpos.le _
  calc M₁ + M₂ * H ^ A ≤ |M₁| * 1 + |M₂| * H ^ A := by
        rw [mul_one]
        exact add_le_add (le_abs_self _)
          (le_trans (le_abs_self _) (by rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hHpos.le _)]))
    _ ≤ |M₁| * (H ^ A' * h₀ ^ (-A')) + |M₂| * (H ^ A' * h₀ ^ (A - A')) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    _ = (|M₁| * h₀ ^ (-A') + |M₂| * h₀ ^ (A - A')) * H ^ A' := by ring

end AbsEisGrowthProof

attribute [local instance] NumberField.AdelicHaar.glBorel

open AbsEisGrowthProof in
theorem solution
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ),
    ∃ C A : ℝ, 0 ≤ C ∧ ∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β,
      Summable (fun ξ : F => ‖φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) ∧
      ‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ ≤ C * adelicHeight F g ^ A := by
  intro αm hαm μ ν hμ hν s hs φ hφ hφc
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  set σ : ℝ := s.re with hσdef

  obtain ⟨-, h1u, hsph⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have hsph' : ∀ s', IsInducedSection (𝓞 F) F (etaFst 1 αm hαm s') (etaSnd 1 αm hαm s') (sph F s') :=
    fun s' => hsph hαm s'
  have h1c : IsIdeleClassChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun _ => rfl
  have h1k : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => (((1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) x : ℂˣ) : ℂ) := by
    simp only [MonoidHom.one_apply, Units.val_one]
    exact continuous_const

  obtain ⟨O, Ec, Nc, hO, hOc, hO0, hOhalf, hEa, hNa, hEjc, hNjc, hEeq, hNeq, -, -, -, -, -⟩ :=
    AxisWitness.exists_axisContinuation F αm hαm rfl 1 1 h1u h1u h1c h1c h1k h1k (sph F) hsph'
      (sph_isArchKFinite F) (sph_isKfSmooth F) (continuous_sph_uncurry F) (differentiable_sph F) (sph_hKu F)

  set vol : ℂ := (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) with hvol
  have hvol0 : vol ≠ 0 := by
    rw [hvol, Complex.ofReal_ne_zero]
    exact (ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne).ne'
  set Nc' : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun z g => vol * Nc z g with hNc'
  have hpack :
      IsOpen O ∧ IsPreconnected O ∧ {z : ℂ | z.re = 0} ⊆ O ∧ {z : ℂ | 1 / 2 < z.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun z => Ec z g) O) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun z => Nc' z g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc' p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ z : ℂ, 1 / 2 < z.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Ec z g = sph F z g + ∑' ξ : F, sph F z (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ z : ℂ, 1 / 2 < z.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc' z g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (sph F z) g) := by
    refine ⟨hO, hOc, hO0, hOhalf, hEa, fun g => ?_, hEjc, ?_, fun z hz g => ?_, fun z hz g => ?_⟩
    · exact analyticOnNhd_const.mul (hNa g)
    · exact continuousOn_const.mul hNjc
    · rw [hEeq z hz, pseudoEisenstein_apply]
    · show vol * Nc z g = _
      rw [hNeq z hz g, ← mul_assoc, mul_inv_cancel₀ hvol0, one_mul]

  have hσ : (1 : ℝ) / 2 < σ := hs
  have hσO : ((σ : ℝ) : ℂ) ∈ O := hOhalf (by show (1:ℝ)/2 < ((σ:ℝ):ℂ).re; rw [Complex.ofReal_re]; exact hσ)

  obtain ⟨h₀, hh₀, hfloor, -⟩ :=
    AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
      F α β hα hαβ

  obtain ⟨M₁, hM₁⟩ :=
    AutomorphicForm.exists_norm_lambdaT_axis_continuation_le_mul_adelicHeight_rpow_neg_of_mem_of_mem_canonicalTruncationDomain
      F α β hα hαβ (AutomorphicForm.canonicalTruncationDomain F α β) hαm 1 1 h1u h1u h1c h1c h1k h1k (sph F) hsph'
      (sph_isArchKFinite F) (sph_isKfSmooth F) (continuous_sph_uncurry F) (differentiable_sph F) (sph_hKu F)
      O Ec Nc' hpack (σ : ℂ) hσO 0

  obtain ⟨M₂, A, hM₂⟩ :=
    AutomorphicForm.exists_norm_constantTerm_axis_continuation_le_mul_adelicHeight_rpow_of_mem_of_mem_canonicalTruncationDomain
      F α β hα hαβ (AutomorphicForm.canonicalTruncationDomain F α β) hαm 1 1 h1u h1u h1c h1c h1k h1k (sph F) hsph'
      (sph_isArchKFinite F) (sph_isKfSmooth F) (continuous_sph_uncurry F) (differentiable_sph F) (sph_hKu F)
      O Ec Nc' hpack (σ : ℂ) hσO

  have hE : ∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β,
      ‖Ec (σ : ℂ) g‖ ≤ M₁ + M₂ * adelicHeight F g ^ A := by
    intro g hg
    have hlt : Real.exp (Real.log (h₀ / 2)) < adelicHeight F g := by
      rw [Real.exp_log (by positivity)]
      exact lt_of_lt_of_le (by linarith) (hfloor g hg)
    have h1 := hM₁ (Real.log (h₀ / 2)) g hg hlt
    have h2 := hM₂ g hg
    rw [AutomorphicForm.lambdaT_apply_of_lt _ _ hlt] at h1
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at h1
    calc ‖Ec (σ : ℂ) g‖ = ‖(Ec (σ : ℂ) g - _) + _‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ M₁ + M₂ * adelicHeight F g ^ A := add_le_add h1 h2

  obtain ⟨C₁, hC₁, hφle⟩ :=
    AutomorphicForm.exists_forall_norm_le_mul_adelicHeight_rpow_of_isInducedSection F hαm μ ν hμ hν s φ hφ hφc

  obtain ⟨C, A', hC, hgrow⟩ := growth_combine h₀ hh₀ M₁ M₂ A
  refine ⟨C₁ * C, A', mul_nonneg hC₁ hC, fun g hg => ?_⟩

  have hsumφ : Summable (fun ξ : F => ‖φ (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) :=
    AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hαm μ ν hμ hν s hs φ hφ hφc g
  have hsumS : Summable (fun ξ : F => ‖sph F (σ : ℂ) (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) :=
    AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half F hαm 1 1 h1u h1u (σ : ℂ)
      (by rw [Complex.ofReal_re]; exact hσ) (sph F σ) (hsph' σ) (continuous_sph F σ) g
  set a : F → ℝ := fun ξ => adelicHeight F (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) ^ (σ + 1 / 2) with ha
  have hsumA : Summable a := by
    refine hsumS.congr fun ξ => ?_
    exact norm_sph_ofReal F σ _
  have ha0 : ∀ ξ, 0 ≤ a ξ := fun ξ => Real.rpow_nonneg (adelicHeight_pos _).le _

  have hEcσ : Ec (σ : ℂ) g = ((adelicHeight F g ^ (σ + 1 / 2) + ∑' ξ : F, a ξ : ℝ) : ℂ) := by
    rw [hpack.2.2.2.2.2.2.2.2.1 (σ : ℂ) (by rw [Complex.ofReal_re]; exact hσ) g]
    rw [Complex.ofReal_add, Complex.ofReal_tsum, sph_ofReal]
    congr 1
    exact tsum_congr fun ξ => sph_ofReal F σ _
  have hnormE : ‖Ec (σ : ℂ) g‖ = adelicHeight F g ^ (σ + 1 / 2) + ∑' ξ : F, a ξ := by
    rw [hEcσ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact add_nonneg (Real.rpow_nonneg (adelicHeight_pos _).le _) (tsum_nonneg ha0)
  refine ⟨hsumφ, ?_⟩
  have hσ' : s.re + 1 / 2 = σ + 1 / 2 := by rw [hσdef]
  calc ‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖
      ≤ C₁ * adelicHeight F g ^ (σ + 1 / 2) + ∑' ξ : F, C₁ * a ξ := by
        refine add_le_add (by rw [← hσ']; exact hφle g) ?_
        refine hsumφ.tsum_le_tsum (fun ξ => ?_) (hsumA.mul_left C₁)
        rw [ha, ← hσ']; exact hφle _
    _ = C₁ * ‖Ec (σ : ℂ) g‖ := by rw [tsum_mul_left, hnormE, mul_add]
    _ ≤ C₁ * (M₁ + M₂ * adelicHeight F g ^ A) := mul_le_mul_of_nonneg_left (hE g hg) hC₁
    _ ≤ C₁ * (C * adelicHeight F g ^ A') := mul_le_mul_of_nonneg_left (hgrow _ (hfloor g hg)) hC₁
    _ = C₁ * C * adelicHeight F g ^ A' := by ring

end
end S_AutomorphicForm_exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain (solution)
