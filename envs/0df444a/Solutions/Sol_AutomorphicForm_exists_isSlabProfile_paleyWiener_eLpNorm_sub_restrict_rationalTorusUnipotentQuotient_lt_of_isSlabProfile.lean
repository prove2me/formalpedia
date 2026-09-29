-- Prove2me | solution 1 for AutomorphicForm.exists_isSlabProfile_paleyWiener_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_lt_of_isSlabProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fbb0e19b-7d0f-5170-88ca-575aca15dcc7

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import Theorems.Thm_AutomorphicForm_exists_isSlabProfile_paleyWiener_eLpNorm_sub_lt_of_forall_eLpNorm_le_of_dense
import Theorems.Thm_AutomorphicForm_exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener
import Theorems.Thm_AutomorphicForm_exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
import Theorems.Thm_NumberField_Idele_exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi
import Theorems.Thm_AutomorphicForm_exists_forall_isSlabProfile_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_le_mul_eLpNorm_sub_diagOne_mul
import Theorems.Thm_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_isSlabProfile
import Theorems.Thm_AutomorphicForm_exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile
import Theorems.Thm_AutomorphicForm_IsSlabProfile_apply_eq_one_of_mem_principalIdeles_of_apply_ne_zero
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSlabProfile_paleyWiener_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_lt_of_isSlabProfile
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass"
p2m_attr_erase "instance" "instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U"
p2m_attr_erase "simp" "AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.genuineβ_fst"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

open AutomorphicForm in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
      (_hξ : Continuous ξ) (_hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ),
    ∃ a b : ℝ, 0 < a ∧ (∀ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b) ∧
    ∀ ε > (0 : ℝ),
    ∃ (ι : Type) (_ : Fintype ι) (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (r : ι → ι)
      (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ) (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ e, IsUnitaryChar (𝓞 F) F (μ e)) ∧ (∀ e, IsUnitaryChar (𝓞 F) F (ν e)) ∧
      (∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) ∧ (∀ e, IsIdeleClassChar (𝓞 F) F (ν e)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ)) ∧
      (∀ (e : ι) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z) ∧
      (∀ e, μ (r e) = ν e ∧ ν (r e) = μ e) ∧
      (∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x) ∧
      (∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s)) ∧
      (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2)) ∧
      (∀ e g, Differentiable ℂ (fun s => ψf e s g)) ∧
      (∀ e s, IsArchKFinite F (ψf e s)) ∧ (∀ e s, IsKfSmooth F (ψf e s)) ∧
      (∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
      (∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) ∧
      AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ ∧
      (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ψ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b) ∧
      eLpNorm (fun q : AutomorphicForm.RationalTorusUnipotentQuotient F => φ q.out - ψ q.out) 2
        ((AutomorphicForm.rationalTorusUnipotentQuotientMeasure F).restrict
          {q | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂}) <
        ENNReal.ofReal ε := by

  intro α hα d₁ d₂ hd₁ hd Φ ξ hξ hξu φ hφ
  classical

  obtain ⟨a, b, ha, hband⟩ := hφ.height_band
  have ha' : (0 : ℝ) < a / 2 := by positivity
  have haa' : a / 2 < a := by linarith
  have hbb' : b < b + 1 := by linarith
  have hband' : ∀ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0 →
      NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc (a / 2) (b + 1) := by
    intro g hg
    obtain ⟨h1, h2⟩ := hband g hg
    exact ⟨by linarith, by linarith⟩

  obtain ⟨c, -, hcT, hc⟩ :=
    AutomorphicForm.exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa F
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar F
  obtain ⟨D, hDm, hDF, -⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow F
      (NumberField.Idele.idelicHaar F)
  obtain ⟨V, hV0, hVT, hV⟩ :=
    NumberField.Idele.exists_setLIntegral_comp_ideleNorm_eq_mul_lintegral_Ioi F D hDm hDF

  obtain ⟨κ, hκ, hL2⟩ :=
    AutomorphicForm.exists_forall_isSlabProfile_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_le_mul_eLpNorm_sub_diagOne_mul
      F c hcT hc D hDm hDF V hV0 hVT hV d₁ d₂ hd₁ hd Φ ξ hξu

  refine AutomorphicForm.exists_isSlabProfile_paleyWiener_eLpNorm_sub_lt_of_forall_eLpNorm_le_of_dense F hα d₁ d₂ hd₁ hd Φ ξ
    hξ hξu φ hφ (a / 2) (b + 1) ha' hband'
    ((AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F))
    ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
        (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
      (maximalCompactHaar F))
    (fun p => NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F))
    κ hκ (fun ψ hψ => hL2 φ ψ hφ hψ)
    {ψ | ∃ (μ₀ ν₀ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ψf₀ : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (IsUnitaryChar (𝓞 F) F μ₀ ∧ IsUnitaryChar (𝓞 F) F ν₀ ∧
       IsIdeleClassChar (𝓞 F) F μ₀ ∧ IsIdeleClassChar (𝓞 F) F ν₀ ∧
       (Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ₀ x : ℂˣ) : ℂ)) ∧
       (Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν₀ x : ℂˣ) : ℂ)) ∧
       (∀ z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z, μ₀ (z : (AdeleRing (𝓞 F) F)ˣ) * ν₀ (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)) ∧
      ((∀ s, IsInducedSection (𝓞 F) F (etaFst μ₀ α hα s) (etaSnd ν₀ α hα s) (ψf₀ s)) ∧
       Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf₀ p.1 p.2) ∧
       (∀ g, Differentiable ℂ (fun s => ψf₀ s g)) ∧
       (∀ s, IsArchKFinite F (ψf₀ s)) ∧ (∀ s, IsKfSmooth F (ψf₀ s)) ∧
       (∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
         FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
           (fun k : ↥(archRowIsometrySubgroup F w) => ψf₀ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
       (∀ (m₀ : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
         ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
           ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ m₀ * ‖ψf₀ ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) ∧
       AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ ∧
       (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
         ψ g = (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₀ ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
       (∀ g : AdelicGL2 (𝓞 F) F, ψ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc (a / 2) (b + 1)))}
    ?hPW ?hdense
  ·
    intro n e he
    choose μ₀ ν₀ ψf₀ hch hcl using he
    exact AutomorphicForm.exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener F hα d₁ d₂ hd₁ hd Φ ξ
      hξ hξu (a / 2) (b + 1) n μ₀ ν₀
      (fun j => (hch j).1) (fun j => (hch j).2.1) (fun j => (hch j).2.2.1) (fun j => (hch j).2.2.2.1)
      (fun j => (hch j).2.2.2.2.1) (fun j => (hch j).2.2.2.2.2.1) (fun j => (hch j).2.2.2.2.2.2)
      ψf₀ (fun j => (hcl j).1) (fun j => (hcl j).2.1) (fun j => (hcl j).2.2.1) (fun j => (hcl j).2.2.2.1)
      (fun j => (hcl j).2.2.2.2.1) (fun j => (hcl j).2.2.2.2.2.1) (fun j => (hcl j).2.2.2.2.2.2.1)
      e (fun j => (hcl j).2.2.2.2.2.2.2.1) (fun j => (hcl j).2.2.2.2.2.2.2.2.1)
      (fun j => (hcl j).2.2.2.2.2.2.2.2.2)
  ·
    intro δ hδ
    by_cases hz : ∃ g₀ : AdelicGL2 (𝓞 F) F, φ g₀ ≠ 0
    · obtain ⟨g₀, hg₀⟩ := hz
      have hb' : (0 : ℝ) < b + 1 := by
        obtain ⟨h1, h2⟩ := hband g₀ hg₀
        linarith
      have hξt : ∀ z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z,
          (z : (AdeleRing (𝓞 F) F)ˣ) ∈ M4aHerbrand.principalIdeles (𝓞 F) F → ξ z = 1 :=
        fun z hz' => AutomorphicForm.IsSlabProfile.apply_eq_one_of_mem_principalIdeles_of_apply_ne_zero F _ ξ φ hφ
          g₀ hg₀ z hz'
      obtain ⟨n, μ, h, m, hμu, hμic, hμc, hhs, hhc, hhb, hmc, hmW, hmsm, hlt⟩ :=
        AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_isSlabProfile F Φ ξ φ hφ a b ha
          hband (a / 2) (b + 1) ha' haa' hbb' D hDm hDF δ hδ
      obtain ⟨ν, φ₀, hνu, hνic, hνc, hprod, hind, hK, hsm, hφ₀c, hle⟩ :=
        AutomorphicForm.exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile F hα Φ ξ
          hξ hξu hξt φ hφ D hDm hDF n μ hμu hμic hμc h (fun j => (hhs j).continuous) m hmc hmW hmsm
      have hel := fun j : Fin n =>
        AutomorphicForm.exists_paleyWiener_oneIndex_apply_diagOne_mul_eq_of_isInducedSection_of_contDiff_of_pos F hα Φ ξ (μ j) (ν j)
          (hμu j) (hνu j) (hμic j) (hνic j) (hμc j) (hνc j) (hprod j) (φ₀ j) (hind j) (hK j) (hsm j) (hφ₀c j)
          (a / 2) (b + 1) ha' hb' (h j) (hhs j) (hhc j) (hhb j)
      choose ψf₀ ψ₀ hE using hel
      refine ⟨n, ψ₀, fun j => ⟨μ j, ν j, ψf₀ j, ⟨hμu j, hνu j, hμic j, hνic j, hμc j, hνc j, hprod j⟩,
        (hE j).1, (hE j).2.1, (hE j).2.2.1, (hE j).2.2.2.1, (hE j).2.2.2.2.1, (hE j).2.2.2.2.2.1,
        (hE j).2.2.2.2.2.2.1, (hE j).2.2.2.2.2.2.2.1, (hE j).2.2.2.2.2.2.2.2.1, (hE j).2.2.2.2.2.2.2.2.2.1⟩, ?_⟩
      have heq : (fun τ : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
            φ ((fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
              NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) τ) -
            ∑ i, ψ₀ i ((fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
              NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) τ)) =
          (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
            φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
              ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) *
                φ₀ j (p.2 : AdelicGL2 (𝓞 F) F)) := by
        funext p
        simp only
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hk := AutomorphicForm.mem_adelicMaximalCompact_iff.mp p.2.prop
        exact (hE j).2.2.2.2.2.2.2.2.2.2 p.1 (p.2 : AdelicGL2 (𝓞 F) F) hk.1 hk.2
      rw [heq]
      exact lt_of_le_of_lt hle hlt
    · push_neg at hz
      refine ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
      simpa [hz] using hδ

end

end S_AutomorphicForm_exists_isSlabProfile_paleyWiener_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_lt_of_isSlabProfile
end P2MW
export P2MW.S_AutomorphicForm_exists_isSlabProfile_paleyWiener_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_lt_of_isSlabProfile (solution)
