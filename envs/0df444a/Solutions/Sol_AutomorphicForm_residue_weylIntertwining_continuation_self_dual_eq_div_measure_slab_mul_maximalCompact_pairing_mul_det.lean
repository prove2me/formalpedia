-- Prove2me | solution 1 for AutomorphicForm.residue_weylIntertwining_continuation_self_dual_eq_div_measure_slab_mul_maximalCompact_pairing_mul_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ac3cb2b5-10a2-54ba-9748-8de0c4f84e35

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
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ConstantTerm
import Theorems.Thm_AutomorphicForm_constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_FnTwist
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab
import Theorems.Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_AutomorphicForm_exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_residue_weylIntertwining_continuation_self_dual_eq_div_measure_slab_mul_maximalCompact_pairing_mul_det
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi"
p2m_attr_erase "simp" "LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply"
p2m_attr_erase "simp" "IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_residue_weylIntertwining_continuation_self_dual_eq_div_measure_slab_mul_maximalCompact_pairing_mul_det.AutomorphicForm"
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

section MeromorphicLimitAlongRay

open Filter Topology

private theorem tendsto_nhdsNE_of_meromorphicAt_of_tendsto_add_ofReal
    {f H : ℂ → ℂ} {z₀ L : ℂ} (hf : MeromorphicAt f z₀)
    (hfH : ∀ s : ℂ, z₀.re < s.re → f s = H s)
    (hH : Tendsto (fun t : ℝ => H (z₀ + t)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto f (𝓝[≠] z₀) (𝓝 L) := by
  have hray : Tendsto (fun t : ℝ => z₀ + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Tendsto (fun t : ℝ => z₀ + (t : ℂ)) (𝓝 (0 : ℝ)) (𝓝 z₀) := by
        have h : Continuous (fun t : ℝ => z₀ + (t : ℂ)) := continuous_const.add Complex.continuous_ofReal
        simpa using h.tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall fun t (ht : (0 : ℝ) < t) => ?_
      intro h
      have h' : (t : ℂ) = 0 := by simpa using h
      exact ht.ne' (Complex.ofReal_eq_zero.1 h')
  have hfray : (fun t : ℝ => f (z₀ + t)) =ᶠ[𝓝[>] (0 : ℝ)] fun t : ℝ => H (z₀ + t) := by
    refine eventually_nhdsWithin_of_forall fun t (ht : (0 : ℝ) < t) => ?_
    apply hfH
    simp [ht]
  have hfL : Tendsto (fun t : ℝ => f (z₀ + t)) (𝓝[>] (0 : ℝ)) (𝓝 L) := hH.congr' hfray.symm
  by_cases ho : 0 ≤ meromorphicOrderAt f z₀
  · obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
    have hcL : c = L := tendsto_nhds_unique (hc.comp hray) hfL
    exact hcL ▸ hc
  · exfalso
    have hcob : Tendsto (fun t : ℝ => f (z₀ + t)) (𝓝[>] (0 : ℝ)) (Bornology.cobounded ℂ) :=
      (tendsto_cobounded_of_meromorphicOrderAt_neg (not_le.1 ho)).comp hray
    have h1 : Tendsto (fun t : ℝ => ‖f (z₀ + t)‖) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_norm_cobounded_atTop.comp hcob
    have h2 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖L‖ + 1 ≤ ‖f (z₀ + t)‖ := h1.eventually_ge_atTop _
    have h3 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ‖f (z₀ + t)‖ < ‖L‖ + 1 :=
      hfL.norm.eventually (gt_mem_nhds (lt_add_one _))
    obtain ⟨t, ht2, ht3⟩ := (h2.and h3).exists
    exact absurd ht2 (not_le.2 ht3)

private theorem limUnder_nhdsNE_sub_mul_eq_of_meromorphicNFOn_of_tendsto_add_ofReal
    {m H : ℂ → ℂ} {L : ℂ} (hm : MeromorphicNFOn m Set.univ)
    (hH : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → (s - (1 / 2 : ℂ)) * m s = H s)
    (hL : Tendsto (fun t : ℝ => H ((1 / 2 : ℂ) + t)) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Filter.limUnder (𝓝[≠] (1 / 2 : ℂ)) (fun s : ℂ => (s - (1 / 2 : ℂ)) * m s) = L := by
  have hf : MeromorphicAt (fun s : ℂ => (s - (1 / 2 : ℂ)) * m s) (1 / 2 : ℂ) :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt.mul (hm.meromorphicOn _ (Set.mem_univ _))
  have hre : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by norm_num
  refine Tendsto.limUnder_eq ?_
  refine tendsto_nhdsNE_of_meromorphicAt_of_tendsto_add_ofReal hf (fun s hs => hH s ?_) hL
  rwa [hre] at hs

end MeromorphicLimitAlongRay

section TrivialSectionAndProductFormula

variable (F : Type) [Field F] [NumberField F]

private theorem isInducedSection_etaFst_etaSnd_one_neg_half_const_one
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) :
    AutomorphicForm.IsInducedSection (𝓞 F) F (AutomorphicForm.etaFst 1 α hα (-(1 / 2 : ℂ)))
      (AutomorphicForm.etaSnd 1 α hα (-(1 / 2 : ℂ))) (fun _ : AdelicGL2 (𝓞 F) F => (1 : ℂ)) := by
  intro b hb g
  simp [AutomorphicForm.etaFst_apply, AutomorphicForm.etaSnd_apply]

private theorem det_globalPoints_diagOne (u : Fˣ) :
    Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 F) F (NumberField.AdelicLevel.diagOne u))
      = Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u := by
  ext
  change ((algebraMap F (AdeleRing (𝓞 F) F)).mapMatrix
      (NumberField.AdelicLevel.diagOne u : Matrix (Fin 2) (Fin 2) F)).det
    = algebraMap F (AdeleRing (𝓞 F) F) (u : F)
  rw [← RingHom.map_det]
  congr 1
  change (Matrix.diagonal ![(u : F), 1]).det = (u : F)
  simp [Fin.prod_univ_succ]

private theorem isPrincipalTrivial_distribHaarChar_adeleRing :
    AutomorphicForm.IsPrincipalTrivial (R := 𝓞 F) (K := F)
      (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits) := by
  intro u
  ext
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := F) (NumberField.AdelicLevel.diagOne u)
  rw [det_globalPoints_diagOne F u] at h
  simpa [NumberField.TateGlobal.ideleNorm] using h

end TrivialSectionAndProductFormula

section RegularisedValueAtTheRay

open Filter Topology

private theorem eq_of_continuousAt_of_eq_sub_mul_of_tendsto_sub_mul
    {X : Type*} {G S : ℂ → X → ℂ} {E' : ℂ → ℂ} {x : X} {r : ℂ}
    (hGc : ContinuousAt (fun s : ℂ => G s x) (1 / 2 : ℂ))
    (hGS : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → G s x = (s - (1 / 2 : ℂ)) * S s x)
    (hE' : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → E' s = S s x)
    (hr : Tendsto (fun s : ℂ => (s - (1 / 2 : ℂ)) * E' s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 r)) :
    G (1 / 2 : ℂ) x = r := by
  have hray : Tendsto (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (1 / 2 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) := continuous_const.add Complex.continuous_ofReal
      have h0 := h.tendsto (0 : ℝ)
      simp only [Complex.ofReal_zero, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall fun t (ht : (0 : ℝ) < t) => ?_
      intro h
      have h' : (t : ℂ) = 0 := by simpa using h
      exact ht.ne' (Complex.ofReal_eq_zero.1 h')
  have h1 : Tendsto (fun t : ℝ => G ((1 / 2 : ℂ) + (t : ℂ)) x) (𝓝[>] (0 : ℝ)) (𝓝 (G (1 / 2 : ℂ) x)) :=
    Tendsto.comp hGc (hray.mono_right nhdsWithin_le_nhds)
  have h2 : Tendsto (fun t : ℝ => G ((1 / 2 : ℂ) + (t : ℂ)) x) (𝓝[>] (0 : ℝ)) (𝓝 r) := by
    refine (hr.comp hray).congr' ?_
    refine eventually_nhdsWithin_of_forall fun t (ht : (0 : ℝ) < t) => ?_
    have hre : (1 / 2 : ℝ) < ((1 / 2 : ℂ) + (t : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      norm_num [ht]
    show ((1 / 2 : ℂ) + (t : ℂ) - (1 / 2 : ℂ)) * E' ((1 / 2 : ℂ) + (t : ℂ)) = G ((1 / 2 : ℂ) + (t : ℂ)) x
    rw [hE' _ hre, hGS _ hre]
  exact tendsto_nhds_unique h1 h2

private theorem tendsto_setIntegral_add_ofReal_of_norm_le_of_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {Ω : Set X} {G : ℂ → X → ℂ} {M : ℝ}
    (hΩm : MeasurableSet Ω) (hΩ : μ Ω ≠ ⊤)
    (hmeas : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (G ((1 / 2 : ℂ) + (t : ℂ))) (μ.restrict Ω))
    (hb : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ x ∈ Ω, ‖G ((1 / 2 : ℂ) + (t : ℂ)) x‖ ≤ M)
    (hlim : ∀ x ∈ Ω, Tendsto (fun t : ℝ => G ((1 / 2 : ℂ) + (t : ℂ)) x) (𝓝[>] (0 : ℝ)) (𝓝 (G (1 / 2 : ℂ) x))) :
    Tendsto (fun t : ℝ => ∫ x in Ω, G ((1 / 2 : ℂ) + (t : ℂ)) x ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in Ω, G (1 / 2 : ℂ) x ∂μ)) :=
  tendsto_integral_filter_of_dominated_convergence (fun _ => M) hmeas
    (hb.mono fun _ ht => ae_restrict_of_forall_mem hΩm ht) (integrableOn_const hΩ)
    (ae_restrict_of_forall_mem hΩm hlim)

private theorem tendsto_setIntegral_add_ofReal_of_norm_le_of_tendsto_const
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {Ω : Set X} {G : ℂ → X → ℂ} {M : ℝ} {r : ℂ}
    (hΩm : MeasurableSet Ω) (hΩ : μ Ω ≠ ⊤)
    (hmeas : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (G ((1 / 2 : ℂ) + (t : ℂ))) (μ.restrict Ω))
    (hb : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ x ∈ Ω, ‖G ((1 / 2 : ℂ) + (t : ℂ)) x‖ ≤ M)
    (hlim : ∀ x ∈ Ω, Tendsto (fun t : ℝ => G ((1 / 2 : ℂ) + (t : ℂ)) x) (𝓝[>] (0 : ℝ)) (𝓝 (G (1 / 2 : ℂ) x)))
    (hr : ∀ x ∈ Ω, G (1 / 2 : ℂ) x = r) :
    Tendsto (fun t : ℝ => ∫ x in Ω, G ((1 / 2 : ℂ) + (t : ℂ)) x ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (((μ Ω).toReal : ℂ) * r)) := by
  have h := tendsto_setIntegral_add_ofReal_of_norm_le_of_tendsto hΩm hΩ hmeas hb hlim
  have hc : ∫ x in Ω, G (1 / 2 : ℂ) x ∂μ = ((μ Ω).toReal : ℂ) * r := by
    rw [setIntegral_congr_fun hΩm hr, setIntegral_const, measureReal_def, Complex.real_smul]
  rwa [hc] at h

end RegularisedValueAtTheRay

section ConstantTermOfAContinuousFamily

open Filter Topology

variable (F : Type) [Field F] [NumberField F]

private theorem continuous_unipotentGL2_adeleRing :
    Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ x : AdeleRing (𝓞 F) F,
        (((unipotentGL2 x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
          !![1, -x; 0, 1] :=
      fun _ => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

variable {F}

variable {G : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {a : ℝ}

private theorem isOpen_setOf_lt_re_prod_univ :
    IsOpen ({s : ℂ | a < s.re} ×ˢ (Set.univ : Set (AdelicGL2 (𝓞 F) F))) :=
  (isOpen_lt continuous_const Complex.continuous_re).prod isOpen_univ

private theorem continuous_of_continuousOn_lt_re_prod_univ
    (hG : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    {s : ℂ} (hs : a < s.re) : Continuous (G s) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmem : ({s : ℂ | a < s.re} ×ˢ (Set.univ : Set (AdelicGL2 (𝓞 F) F))) ∈ 𝓝 (s, x) :=
    isOpen_setOf_lt_re_prod_univ.mem_nhds ⟨hs, Set.mem_univ _⟩
  exact (hG.continuousAt hmem).comp (continuous_const.prodMk continuous_id).continuousAt

private theorem continuousAt_of_continuousOn_lt_re_prod_univ
    (hG : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    {s₀ : ℂ} (hs₀ : a < s₀.re) (x : AdelicGL2 (𝓞 F) F) : ContinuousAt (fun s : ℂ => G s x) s₀ := by
  have hmem : ({s : ℂ | a < s.re} ×ˢ (Set.univ : Set (AdelicGL2 (𝓞 F) F))) ∈ 𝓝 (s₀, x) :=
    isOpen_setOf_lt_re_prod_univ.mem_nhds ⟨hs₀, Set.mem_univ _⟩
  exact Tendsto.comp (hG.continuousAt hmem) ((Continuous.prodMk_left x).tendsto s₀)

private theorem tendsto_add_ofReal_of_continuousOn_lt_re_prod_univ
    (hG : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (ha : a < 1 / 2) (x : AdelicGL2 (𝓞 F) F) :
    Tendsto (fun t : ℝ => G ((1 / 2 : ℂ) + (t : ℂ)) x) (𝓝[>] (0 : ℝ)) (𝓝 (G (1 / 2 : ℂ) x)) := by
  have hs : a < ((1 / 2 : ℂ)).re := by norm_num [ha]
  have hc := continuousAt_of_continuousOn_lt_re_prod_univ hG hs x
  have hray : Tendsto (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
    have h : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) := continuous_const.add Complex.continuous_ofReal
    have h0 := h.tendsto (0 : ℝ)
    simp only [Complex.ofReal_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact Tendsto.comp hc hray

private theorem aestronglyMeasurable_of_continuousOn_lt_re_prod_univ
    (hG : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    {s : ℂ} (hs : a < s.re) (μ : Measure (AdelicGL2 (𝓞 F) F)) : AEStronglyMeasurable (G s) μ :=
  (continuous_of_continuousOn_lt_re_prod_univ hG hs).aestronglyMeasurable

private theorem constantTerm_cond_adelicBox_const (r : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
      (fun _ : AdelicGL2 (𝓞 F) F => r) g = r := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  simp [constantTerm, constantTermIntegrand]

private theorem continuousAt_constantTerm_cond_adelicBox
    (hG : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    {s₀ : ℂ} (hs₀ : a < s₀.re) (g : AdelicGL2 (𝓞 F) F) :
    ContinuousAt (fun s : ℂ =>
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 (G s) g) s₀ := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  have hopen : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen s₀ hs₀
  have hN : Metric.closedBall s₀ (ε / 2) ⊆ {s : ℂ | a < s.re} :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hmul : Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) * g :=
    (continuous_unipotentGL2_adeleRing F).mul continuous_const
  have hK : IsCompact (Metric.closedBall s₀ (ε / 2) ×ˢ
      ((fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) * g) '' C)) :=
    (isCompact_closedBall s₀ (ε / 2)).prod (hC.image hmul)
  have hKsub : Metric.closedBall s₀ (ε / 2) ×ˢ
      ((fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) * g) '' C) ⊆
        {s : ℂ | a < s.re} ×ˢ Set.univ :=
    Set.prod_mono hN (Set.subset_univ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hG.mono hKsub)
  simp only [constantTerm, constantTermIntegrand]
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · filter_upwards [hopen.mem_nhds hs₀] with s hs
    exact ((continuous_of_continuousOn_lt_re_prod_univ hG hs).comp hmul).aestronglyMeasurable
  · filter_upwards [Metric.closedBall_mem_nhds s₀ (half_pos hε)] with s hs
    filter_upwards [ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)] with x hx
    exact hM (s, unipotentGL2 x * g) ⟨hs, ⟨x, hsub hx, rfl⟩⟩
  · exact Eventually.of_forall fun x => continuousAt_of_continuousOn_lt_re_prod_univ hG hs₀ _

private theorem exists_forall_norm_constantTerm_cond_adelicBox_le
    (hG : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    {N : Set ℂ} (hN : IsCompact N) (hNa : N ⊆ {s : ℂ | a < s.re}) :
    ∃ M : ℝ, ∀ s ∈ N, ∀ k : adelicMaximalCompact F,
      ‖constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 (G s)
        (k : AdelicGL2 (𝓞 F) F)‖ ≤ M := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hmul : Continuous fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
      (unipotentGL2 p.1 : AdelicGL2 (𝓞 F) F) * p.2 :=
    ((continuous_unipotentGL2_adeleRing F).comp continuous_fst).mul continuous_snd
  have hK : IsCompact (N ×ˢ ((fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
      (unipotentGL2 p.1 : AdelicGL2 (𝓞 F) F) * p.2) ''
        (C ×ˢ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F))))) :=
    hN.prod ((hC.prod (isCompact_adelicMaximalCompact F)).image hmul)
  have hKsub : N ×ˢ ((fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
      (unipotentGL2 p.1 : AdelicGL2 (𝓞 F) F) * p.2) ''
        (C ×ˢ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)))) ⊆ {s : ℂ | a < s.re} ×ˢ Set.univ :=
    Set.prod_mono hNa (Set.subset_univ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hG.mono hKsub)
  refine ⟨M, fun s hs k => ?_⟩
  have hbound : ∀ᵐ x ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)),
      ‖constantTermIntegrand unipotentGL2 (G s) (k : AdelicGL2 (𝓞 F) F) x‖ ≤ M := by
    filter_upwards [ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)] with x hx
    exact hM (s, unipotentGL2 x * (k : AdelicGL2 (𝓞 F) F)) ⟨hs, ⟨(x, (k : AdelicGL2 (𝓞 F) F)), ⟨hsub hx, k.2⟩, rfl⟩⟩
  have h := norm_integral_le_of_norm_le_const hbound
  simpa [constantTerm] using h

end ConstantTermOfAContinuousFamily

namespace NormDisintegration

variable {X : Type*} [MeasurableSpace X]

private theorem map_restrict_eq_smul_withDensity (ρ : Measure X) (D : Set X) (N : X → ℝ) (hN : Measurable N)
    (V : ℝ≥0∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (N z) ∂ρ = V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹) :
    (ρ.restrict D).map N
      = V • (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun y : ℝ => ENNReal.ofReal y⁻¹) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hN hs, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul]
  have hleft : (ρ.restrict D) (N ⁻¹' s)
      = ∫⁻ z in D, s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (N z) ∂ρ := by
    rw [← lintegral_indicator_one (hN hs)]
    refine lintegral_congr fun z => ?_
    by_cases hz : N z ∈ s
    · simp [Set.indicator_of_mem, hz]
    · simp [Set.indicator_of_notMem, hz]
  have hright : ∫⁻ y in Set.Ioi (0 : ℝ), s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹
      = ∫⁻ y in s, ENNReal.ofReal y⁻¹ ∂(volume.restrict (Set.Ioi (0 : ℝ))) := by
    rw [← lintegral_indicator hs]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ s
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  rw [hleft, hV _ (measurable_const.indicator hs), hright]

private theorem setIntegral_comp_eq_toReal_smul (ρ : Measure X) (D : Set X) (N : X → ℝ) (hN : Measurable N)
    (V : ℝ≥0∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (N z) ∂ρ = V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (g : ℝ → ℂ) (hg : Measurable g) :
    ∫ z in D, g (N z) ∂ρ = V.toReal • ∫ y in Set.Ioi (0 : ℝ), y⁻¹ • g y := by
  rw [← integral_map hN.aemeasurable hg.aestronglyMeasurable,
    map_restrict_eq_smul_withDensity ρ D N hN V hV, integral_smul_measure]
  congr 1
  have hd : (fun y : ℝ => ENNReal.ofReal y⁻¹) = fun y : ℝ => ((Real.toNNReal y⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    funext fun _ => rfl
  rw [hd, integral_withDensity_eq_integral_smul (f := fun y : ℝ => Real.toNNReal y⁻¹)
    (measurable_real_toNNReal.comp measurable_inv) g]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  calc (Real.toNNReal y⁻¹) • g y = ((Real.toNNReal y⁻¹ : ℝ≥0) : ℝ) • g y := NNReal.smul_def _ _
    _ = y⁻¹ • g y := by rw [Real.coe_toNNReal _ (inv_nonneg.mpr (le_of_lt hy))]

private theorem setIntegral_comp_eq_toReal_mul (ρ : Measure X) (D : Set X) (N : X → ℝ) (hN : Measurable N)
    (V : ℝ≥0∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (N z) ∂ρ = V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (g : ℝ → ℂ) (hg : Measurable g) :
    ∫ z in D, g (N z) ∂ρ = (V.toReal : ℂ) * ∫ y in Set.Ioi (0 : ℝ), ((y : ℂ))⁻¹ * g y := by
  rw [setIntegral_comp_eq_toReal_smul ρ D N hN V hV g hg, Complex.real_smul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [Complex.real_smul, Complex.ofReal_inv]

end NormDisintegration

section ConstantTermContinuousInTheGroupVariable

open Filter Topology

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_constantTerm_cond_adelicBox_of_continuous {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : Continuous f) :
    Continuous fun g : AdelicGL2 (𝓞 F) F =>
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 f g := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hmul : Continuous fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
      (unipotentGL2 p.1 : AdelicGL2 (𝓞 F) F) * p.2 :=
    ((continuous_unipotentGL2_adeleRing F).comp continuous_fst).mul continuous_snd
  refine continuous_iff_seqContinuous.2 ?_
  intro γ g₀ hγ
  have hK : IsCompact ((fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
      (unipotentGL2 p.1 : AdelicGL2 (𝓞 F) F) * p.2) '' (C ×ˢ insert g₀ (Set.range γ))) :=
    (hC.prod hγ.isCompact_insert_range).image hmul
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  simp only [Function.comp_def, constantTerm, constantTermIntegrand]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_ (integrable_const M) ?_
  · refine Eventually.of_forall fun m => ?_
    have hm : Continuous fun x : AdeleRing (𝓞 F) F => f ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) * γ m) :=
      hf.comp ((continuous_unipotentGL2_adeleRing F).mul continuous_const)
    exact hm.aestronglyMeasurable
  · refine Eventually.of_forall fun m => ?_
    filter_upwards [ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox F)] with x hx
    exact hM _ ⟨(x, γ m), ⟨hsub hx, Set.mem_insert_of_mem _ ⟨m, rfl⟩⟩, rfl⟩
  · refine Eventually.of_forall fun x => ?_
    have ht : Tendsto (fun m => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) * γ m) atTop
        (𝓝 ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) * g₀)) :=
      tendsto_const_nhds.mul hγ
    exact (hf.tendsto _).comp ht

end ConstantTermContinuousInTheGroupVariable

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.AdelicLevel AutomorphicForm.WindowedSiegel"
open scoped NNReal

section Height

variable (F : Type) [Field F] [NumberField F]

private noncomputable abbrev modChar : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

variable {F}

private theorem adelicHeight_borel_mul (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    {b : AdelicGL2 (𝓞 F) F} (hb : b ∈ adelicBorel (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (b * g) =
      ((modChar F (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ) *
        (((modChar F (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℝˣ) : ℝ))⁻¹ *
          adelicHeight F g := by
  dsimp only [modChar] at hα ⊢
  have hsec := (AutomorphicForm.isInducedSection_adelicHeight_cpow F).2.2 hα (1 / 2) b hb g
  have hone : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  simp only [etaFst_apply, etaSnd_apply, MonoidHom.one_apply, one_mul, cpowChar_apply_val, hone, Complex.cpow_one,
    Complex.cpow_neg_one] at hsec
  exact_mod_cast hsec

private theorem adelicHeight_unipotentGL2_mul (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (unipotentGL2 x * g) = adelicHeight F g := by
  rw [adelicHeight_borel_mul hα (unipotentGL2_mem_borelSubgroup x) g, borelDiagFst_unipotentGL2,
    borelDiagSnd_unipotentGL2, map_one, Units.val_one, inv_one, one_mul, one_mul]

private theorem adelicHeight_centralScalar_mul (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  rw [adelicHeight_borel_mul hα (centralScalar_mem_adelicBorel (𝓞 F) F z) g,
    borelDiagFst_centralScalar (𝓞 F) F z (centralScalar_mem_adelicBorel (𝓞 F) F z),
    borelDiagSnd_centralScalar (𝓞 F) F z (centralScalar_mem_adelicBorel (𝓞 F) F z),
    mul_inv_cancel₀ (hα z).ne', one_mul]

private theorem diagOne_mem_adelicBorel (t : (AdeleRing (𝓞 F) F)ˣ) :
    (diagOne t : AdelicGL2 (𝓞 F) F) ∈ adelicBorel (𝓞 F) F := by
  show ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem borelDiagFst_diagOne (t : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨diagOne t, diagOne_mem_adelicBorel t⟩ : ↥(adelicBorel (𝓞 F) F)) = t := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = (t : AdeleRing (𝓞 F) F)
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq]
  rfl

private theorem borelDiagSnd_diagOne (t : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨diagOne t, diagOne_mem_adelicBorel t⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = 1
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq]
  rfl

private theorem adelicHeight_diagOne_mul (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (t : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (diagOne t * g) = ((modChar F t : ℝˣ) : ℝ) * adelicHeight F g := by
  rw [adelicHeight_borel_mul hα (diagOne_mem_adelicBorel t) g, borelDiagFst_diagOne, borelDiagSnd_diagOne,
    map_one, Units.val_one, inv_one, mul_one]

private theorem adelicHeight_eq_one_of_mem_adelicMaximalCompact {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ adelicMaximalCompact F) : adelicHeight F k = 1 := by
  rw [adelicHeight_eq_archHeight_of_mem (glFin_mem_finiteIntegralGL2 hk)]
  have h := archHeight_mul_rowIsometry F 1 (k := glArch (𝓞 F) F k) (isRowIsometry_archComponent hk)
  rwa [one_mul, archHeight_one] at h

private theorem adelicHeight_iwasawa (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (x : AdeleRing (𝓞 F) F) (u t : (AdeleRing (𝓞 F) F)ˣ) {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ adelicMaximalCompact F) :
    adelicHeight F (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * k) = ((modChar F t : ℝˣ) : ℝ) := by
  rw [mul_assoc, mul_assoc, adelicHeight_unipotentGL2_mul hα, adelicHeight_centralScalar_mul hα,
    adelicHeight_diagOne_mul hα, adelicHeight_eq_one_of_mem_adelicMaximalCompact hk, mul_one]

end Height

section Bruhat

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel

private theorem globalPoints_unipotentGL2 (ξ : F) :
    globalPoints (𝓞 F) F (unipotentGL2 ξ) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply (𝓞 F) F (unipotentGL2 ξ) i j, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem globalPoints_gl2Weyl_mul_unipotentGL2 (ξ : F) :
    globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 ξ) =
      adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  rw [map_mul, globalPoints_unipotentGL2]
  rfl

omit [NumberField F] in
private theorem gl2Weyl_mul_unipotentGL2_apply_one_zero (ξ : F) :
    ((gl2Weyl * unipotentGL2 ξ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem adelicHeight_weyl_unipotent_mul_mul_le_one (ξ : F) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) *
      adelicHeight F g ≤ 1 := by
  rw [← globalPoints_gl2Weyl_mul_unipotentGL2]
  exact adelicHeight_globalPoints_mul_mul_adelicHeight_le_one _
    (by rw [gl2Weyl_mul_unipotentGL2_apply_one_zero]; exact one_ne_zero) g

private theorem adelicHeight_weyl_unipotent_mul_mul_weyl_unipotent_mul_le_one {ξ ξ' : F} (hne : ξ ≠ ξ')
    (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g) *
      adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) ≤ 1 := by
  set γ : GL (Fin 2) F := gl2Weyl * unipotentGL2 ξ' * (gl2Weyl * unipotentGL2 ξ)⁻¹ with hγ
  have hprod : globalPoints (𝓞 F) F γ *
      (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) =
        adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g := by
    rw [hγ, map_mul, map_inv, globalPoints_gl2Weyl_mul_unipotentGL2, globalPoints_gl2Weyl_mul_unipotentGL2,
      ← mul_assoc, inv_mul_cancel_right]
  have h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = ξ' - ξ := by
    have hinv : ((gl2Weyl * unipotentGL2 ξ)⁻¹ : GL (Fin 2) F) = unipotentGL2 (-ξ) * gl2Weyl := by
      rw [mul_inv_rev, gl2Weyl_inv,
        inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])]
    rw [hγ, hinv]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hne' : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    rw [h10]; exact sub_ne_zero.mpr (Ne.symm hne)
  have h := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hne'
    (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)
  rwa [hprod] at h

private theorem lt_of_mul_le_one_of_lt {a b T : ℝ} (hT : 1 ≤ T) (hb : 0 < b) (hab : a * b ≤ 1) (hTb : T < b) :
    a < T :=
  calc a ≤ 1 / b := (le_div_iff₀ hb).mpr hab
    _ < 1 := (div_lt_one hb).mpr (lt_of_le_of_lt hT hTb)
    _ ≤ T := hT

private theorem adelicHeight_weyl_unipotent_mul_lt_of_lt {T : ℝ} (hT : 1 ≤ T) {g : AdelicGL2 (𝓞 F) F}
    (hg : T < adelicHeight F g) (ξ : F) :
    adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) < T :=
  lt_of_mul_le_one_of_lt hT (adelicHeight_pos g) (adelicHeight_weyl_unipotent_mul_mul_le_one ξ g) hg

private theorem adelicHeight_lt_of_lt_weyl_unipotent_mul {T : ℝ} (hT : 1 ≤ T) {g : AdelicGL2 (𝓞 F) F} {ξ : F}
    (hξ : T < adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) :
    adelicHeight F g < T ∧ ∀ ξ' : F, ξ' ≠ ξ →
      adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g) < T := by
  have hpos := adelicHeight_pos (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)
  refine ⟨lt_of_mul_le_one_of_lt hT hpos ?_ hξ, fun ξ' hne => lt_of_mul_le_one_of_lt hT hpos
    (adelicHeight_weyl_unipotent_mul_mul_weyl_unipotent_mul_le_one (Ne.symm hne) g) hξ⟩
  rw [mul_comm]
  exact adelicHeight_weyl_unipotent_mul_mul_le_one ξ g

end Bruhat

end AutomorphicForm.SlabCovolume

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory NumberField NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc AutomorphicForm.SiegelCovering AutomorphicForm.WindowedSiegel"

section Transport

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private theorem countable_globalPoints_range : Countable (globalPoints (𝓞 F) F).range := by
  haveI : Countable F := Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  haveI : Countable (GL (Fin 2) F) :=
    Function.Injective.countable (f := fun M : GL (Fin 2) F => fun i j => (M : Matrix (Fin 2) (Fin 2) F) i j)
      fun a b h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 F) F))

private theorem measurableSet_setOf_ideleNorm_det_mem_Icc (d₁ d₂ : ℝ) :
    MeasurableSet {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} :=
  (continuous_ideleNorm_det F).measurable measurableSet_Icc

private theorem ideleNorm_det_globalPoints_mul (γ : (globalPoints (𝓞 F) F).range) (g : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
  obtain ⟨γ₀, hγ₀⟩ := MonoidHom.mem_range.mp γ.2
  rw [map_mul, ideleNorm_mul, ← hγ₀, AutomorphicForm.ideleNorm_det_globalPoints γ₀, one_mul]

private theorem preimage_smul_setOf_ideleNorm_det_mem_Icc (γ : (globalPoints (𝓞 F) F).range) (d₁ d₂ : ℝ) :
    (fun g : AdelicGL2 (𝓞 F) F => γ • g) ⁻¹'
        {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} =
      {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} := by
  ext g
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Subgroup.smul_def, smul_eq_mul, ideleNorm_det_globalPoints_mul]

private theorem smulInvariantMeasure_restrict_setOf_ideleNorm_det_mem_Icc (d₁ d₂ : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}) := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  have hS := measurableSet_setOf_ideleNorm_det_mem_Icc (F := F) d₁ d₂
  have hmeas : Measurable fun g : AdelicGL2 (𝓞 F) F => γ • g := by
    show Measurable fun g : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * g
    exact (continuous_const.mul continuous_id).measurable
  rw [Measure.restrict_apply' hS, Measure.restrict_apply' hS]
  have hpre : (fun g : AdelicGL2 (𝓞 F) F => γ • g) ⁻¹' s ∩
      {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} =
        (fun g : AdelicGL2 (𝓞 F) F => γ • g) ⁻¹'
          (s ∩ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}) := by
    rw [Set.preimage_inter, preimage_smul_setOf_ideleNorm_det_mem_Icc]
  rw [hpre]
  exact SMulInvariantMeasure.measure_preimage_smul (μ := adelicGLHaar (Fin 2) (𝓞 F) F) γ (hs.inter hS)

private theorem measurableConstSMul_globalPoints_range :
    MeasurableConstSMul (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F) := by
  refine ⟨fun γ => ?_⟩
  show Measurable fun g : AdelicGL2 (𝓞 F) F => (γ : AdelicGL2 (𝓞 F) F) * g
  exact (continuous_const.mul continuous_id).measurable

private theorem measure_eq_of_isFundamentalDomain_slab {d₁ d₂ : ℝ} {Φ Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦs : Φ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})) :
    adelicGLHaar (Fin 2) (𝓞 F) F Φ = adelicGLHaar (Fin 2) (𝓞 F) F Φ₀ := by
  haveI := countable_globalPoints_range (F := F)
  haveI := measurableConstSMul_globalPoints_range (F := F)
  haveI := smulInvariantMeasure_restrict_setOf_ideleNorm_det_mem_Icc (F := F) d₁ d₂
  have hS := measurableSet_setOf_ideleNorm_det_mem_Icc (F := F) d₁ d₂
  have h := hΦ.measure_eq hΦ₀
  rwa [Measure.restrict_apply' hS, Measure.restrict_apply' hS, Set.inter_eq_left.mpr hΦs,
    Set.inter_eq_left.mpr hΦ₀s] at h

private theorem setIntegral_eq_of_isFundamentalDomain_slab {d₁ d₂ : ℝ} {Φ Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦs : Φ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * g) = f g) :
    ∫ g in Φ, f g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = ∫ g in Φ₀, f g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI := countable_globalPoints_range (F := F)
  haveI := measurableConstSMul_globalPoints_range (F := F)
  haveI := smulInvariantMeasure_restrict_setOf_ideleNorm_det_mem_Icc (F := F) d₁ d₂
  have hS := measurableSet_setOf_ideleNorm_det_mem_Icc (F := F) d₁ d₂
  have hf' : ∀ (γ : (globalPoints (𝓞 F) F).range) (g : AdelicGL2 (𝓞 F) F), f (γ • g) = f g := by
    intro γ g
    obtain ⟨γ₀, hγ₀⟩ := MonoidHom.mem_range.mp γ.2
    rw [Subgroup.smul_def, smul_eq_mul, ← hγ₀, hf]
  have h := hΦ.setIntegral_eq hΦ₀ hf'
  rwa [Measure.restrict_restrict' hS, Measure.restrict_restrict' hS, Set.inter_eq_left.mpr hΦs,
    Set.inter_eq_left.mpr hΦ₀s] at h

private theorem exists_isFundamentalDomain_slab_subset_iUnion_centreCutSiegelSet {d₁ d₂ : ℝ} (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) :
    ∃ (c u e₁ e₂ : ℝ) (tset : Finset (AdelicGL2 (𝓞 F) F)) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)),
      0 < c ∧ 0 < e₁ ∧ MeasurableSet Φ₀ ∧
      Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}) ∧
      Φ₀ ⊆ ⋃ t ∈ tset, (· * t) '' centreCutSiegelSet F c u e₁ e₂ := by
  obtain ⟨T, c, hc, u, hcov⟩ := SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet F
  obtain ⟨e₁, e₂, tset, Φ₀, he₁, hm, hs, hΦ₀, hsub⟩ :=
    AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre F c u
      1 2 T hc one_pos one_lt_two (hcov 1 2 two_pos one_le_two) d₁ d₂ hd₁ hd
  exact ⟨c, u, e₁, e₂, tset, Φ₀, hc, he₁, hm, hs, hΦ₀, hsub⟩

end Transport

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section TruncatedSectionProfile

variable (F : Type) [Field F] [NumberField F]

private theorem isIdeleClassChar_one : AutomorphicForm.IsIdeleClassChar (𝓞 F) F 1 := fun _ => rfl

private theorem isInducedSection_globalPoints_mul_of_isIdeleClassChar
    {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (h₁ : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ₁)
    (h₂ : AutomorphicForm.IsIdeleClassChar (𝓞 F) F χ₂) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : AutomorphicForm.IsInducedSection (𝓞 F) F χ₁ χ₂ φ)
    {γ : Matrix.GeneralLinearGroup (Fin 2) F} (hγ : γ ∈ AutomorphicForm.borelSubgroup F)
    (g : AdelicGL2 (𝓞 F) F) :
    φ (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = φ g := by
  have hmem := AutomorphicForm.globalPoints_mem_adelicBorel (𝓞 F) F hγ
  rw [hφ _ hmem g, AutomorphicForm.borelDiagFst_globalPoints (𝓞 F) F hγ hmem,
    AutomorphicForm.borelDiagSnd_globalPoints (𝓞 F) F hγ hmem, h₁, h₂]
  simp

private theorem globalPoints_mul_eq_of_isInducedSection_etaFst_etaSnd_one
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hprin : AutomorphicForm.IsPrincipalTrivial (R := 𝓞 F) (K := F) α) (s : ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : AutomorphicForm.IsInducedSection (𝓞 F) F (AutomorphicForm.etaFst 1 α hα s)
      (AutomorphicForm.etaSnd 1 α hα s) φ)
    {γ : Matrix.GeneralLinearGroup (Fin 2) F} (hγ : γ ∈ AutomorphicForm.borelSubgroup F)
    (g : AdelicGL2 (𝓞 F) F) :
    φ (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = φ g :=
  isInducedSection_globalPoints_mul_of_isIdeleClassChar F
    (AutomorphicForm.etaFst_isIdeleClassChar (isIdeleClassChar_one F) (hα := hα) hprin s)
    (AutomorphicForm.etaSnd_isIdeleClassChar (isIdeleClassChar_one F) (hα := hα) hprin s) hφ hγ g

private theorem centralScalar_mul_eq_of_isInducedSection_etaFst_etaSnd_one
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : AutomorphicForm.IsInducedSection (𝓞 F) F (AutomorphicForm.etaFst 1 α hα s)
      (AutomorphicForm.etaSnd 1 α hα s) φ)
    (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    φ (AutomorphicForm.centralScalar (𝓞 F) F z * g) = φ g := by
  rw [AutomorphicForm.isInducedSection_centralScalar_mul hφ z g, ← Units.val_mul,
    AutomorphicForm.etaFst_mul_etaSnd 1 1 α hα s z]
  simp

private def heightBand (a b : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  (NumberField.AdelicHeight.adelicHeight F ⁻¹' Set.Ioc a b).indicator φ

private theorem heightBand_apply (a b : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    heightBand F a b φ g
      = (Set.Ioc a b).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F g) * φ g := by
  by_cases h : NumberField.AdelicHeight.adelicHeight F g ∈ Set.Ioc a b
  · rw [heightBand, Set.indicator_of_mem (show g ∈ NumberField.AdelicHeight.adelicHeight F ⁻¹' Set.Ioc a b from h),
      Set.indicator_of_mem h, one_mul]
  · rw [heightBand, Set.indicator_of_notMem (show g ∉ NumberField.AdelicHeight.adelicHeight F ⁻¹' Set.Ioc a b from h),
      Set.indicator_of_notMem h, zero_mul]

private theorem heightBand_mul_left_eq (a b : ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} {x g : AdelicGL2 (𝓞 F) F}
    (hh : NumberField.AdelicHeight.adelicHeight F (x * g) = NumberField.AdelicHeight.adelicHeight F g)
    (hφ : φ (x * g) = φ g) :
    heightBand F a b φ (x * g) = heightBand F a b φ g := by
  rw [heightBand_apply, heightBand_apply, hh, hφ]

private theorem isSlabProfile_heightBand_of_isInducedSection_etaFst_etaSnd_one
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hprin : AutomorphicForm.IsPrincipalTrivial (R := 𝓞 F) (K := F) α) (s : ℂ)
    (hmeas : Measurable (NumberField.AdelicHeight.adelicHeight F))
    (hN : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.unipotentGL2 x * g)
        = NumberField.AdelicHeight.adelicHeight F g)
    (hB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g)
        = NumberField.AdelicHeight.adelicHeight F g)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.centralScalar (𝓞 F) F z * g)
        = NumberField.AdelicHeight.adelicHeight F g)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : AutomorphicForm.IsInducedSection (𝓞 F) F (AutomorphicForm.etaFst 1 α hα s)
      (AutomorphicForm.etaSnd 1 α hα s) φ)
    (hφm : Measurable φ) {a b C : ℝ} (ha : 0 < a)
    (hC : ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.AdelicHeight.adelicHeight F g ∈ Set.Ioc a b → ‖φ g‖ ≤ C) :
    AutomorphicForm.IsSlabProfile F Z 1 (heightBand F a b φ) where
  measurable := hφm.indicator (hmeas measurableSet_Ioc)
  unipotent_mul x g :=
    heightBand_mul_left_eq F a b (hN x g) (AutomorphicForm.isInducedSection_unipotent_mul hφ x g)
  borel_mul γ hγ g :=
    heightBand_mul_left_eq F a b (hB γ hγ g)
      (globalPoints_mul_eq_of_isInducedSection_etaFst_etaSnd_one F α hα hprin s hφ hγ g)
  central_transform z g := by
    rw [heightBand_mul_left_eq F a b (hZ z g)
      (centralScalar_mul_eq_of_isInducedSection_etaFst_etaSnd_one F α hα s hφ z g)]
    simp
  bounded_on_slab _ _ _ := by
    refine ⟨max C 0, fun g _ => ?_⟩
    rw [heightBand_apply]
    by_cases hg : NumberField.AdelicHeight.adelicHeight F g ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hg, one_mul]
      exact (hC g hg).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hg, zero_mul, norm_zero]
      exact le_max_right _ _
  height_band := by
    refine ⟨a, b, ha, fun g hg => ?_⟩
    rw [heightBand_apply] at hg
    by_cases hmem : NumberField.AdelicHeight.adelicHeight F g ∈ Set.Ioc a b
    · exact Set.Ioc_subset_Icc_self hmem
    · exact (hg (by rw [Set.indicator_of_notMem hmem, zero_mul])).elim

end TruncatedSectionProfile

end AutomorphicForm.SlabCovolume

section ResidueLimitThroughTheConstantTerm

open Filter Topology

variable (F : Type) [Field F] [NumberField F]

private theorem ofReal_toReal_adelicAddHaar_adelicBox_ne_zero :
    ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2
    (ENNReal.toReal_pos (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne).ne'

variable {F}

private theorem det_unipotentGL2_mul (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) * g) = Matrix.GeneralLinearGroup.det g := by
  have h1 : Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 := by
    ext
    show ((unipotentGL2 x : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det = 1
    rw [unipotentGL2_coe, Matrix.det_fin_two_of]
    ring
  rw [map_mul, h1, one_mul]

private theorem constantTerm_cond_adelicBox_const_mul (c : ℂ) (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 (fun x => c * f x) g =
      c * constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 f g := by
  simp only [constantTerm, constantTermIntegrand]
  exact integral_const_mul _ _

private theorem constantTerm_cond_adelicBox_char_det_mul (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
        (fun x => ((χ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * f x) g =
      ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 f g := by
  simp only [constantTerm, constantTermIntegrand, det_unipotentGL2_mul]
  exact integral_const_mul _ _

private theorem sub_mul_weylIntertwiningIntegral_eq_mul_constantTerm_sub :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ' : IsUnitaryChar (𝓞 F) F μ') (_hν' : IsUnitaryChar (𝓞 F) F ν')
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ' α hα s) (etaSnd ν' α hα s) φ)
      (_hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F),
    (s - 1 / 2) * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g =
      (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) *
        (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
            (fun x => (s - 1 / 2) * (φ x + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F *
              unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))) g
          - (s - 1 / 2) * φ g) := by
  intro α hα μ' ν' hμ' hν' s hs φ hφ hφc g
  have hb := ofReal_toReal_adelicAddHaar_adelicBox_ne_zero F
  have h := AutomorphicForm.constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hα μ' ν'
    hμ' hν' s hs φ hφ hφc g
  have h' : constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
      (fun x => φ x + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)) g
        = φ g + ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g := h
  rw [constantTerm_cond_adelicBox_const_mul, h']
  set b : ℂ := (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) with hb_def
  set m : ℂ := weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ g with hm_def
  calc (s - 1 / 2) * m = (s - 1 / 2) * (b * b⁻¹) * m := by rw [mul_inv_cancel₀ hb, mul_one]
    _ = b * ((s - 1 / 2) * (φ g + b⁻¹ * m) - (s - 1 / 2) * φ g) := by ring

variable {G : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {a : ℝ} {r : ℂ}

private theorem tendsto_mul_constantTerm_sub_add_ofReal
    (hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (ha : a < 1 / 2) (hG : ∀ g : AdelicGL2 (𝓞 F) F, G (1 / 2) g = r)
    {ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
    (g : AdelicGL2 (𝓞 F) F) :
    Tendsto (fun t : ℝ => (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) *
        (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
            (G ((1 / 2 : ℂ) + (t : ℂ))) g
          - (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * ψ ((1 / 2 : ℂ) + (t : ℂ)) g))
      (𝓝[>] (0 : ℝ)) (𝓝 ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) * r)) := by
  haveI := isProbabilityMeasure_cond_adelicBox F
  have hs : a < ((1 / 2 : ℂ)).re := by norm_num [ha]
  have hray : Tendsto (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
    have h : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) := continuous_const.add Complex.continuous_ofReal
    have h0 := h.tendsto (0 : ℝ)
    simp only [Complex.ofReal_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hG' : G (1 / 2 : ℂ) = fun _ => r := funext hG
  have h1 : Tendsto (fun t : ℝ => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (G ((1 / 2 : ℂ) + (t : ℂ))) g) (𝓝[>] (0 : ℝ)) (𝓝 r) := by
    have hc : Tendsto (fun s : ℂ => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        unipotentGL2 (G s) g) (𝓝 (1 / 2 : ℂ))
        (𝓝 (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
          (G (1 / 2 : ℂ)) g)) :=
      continuousAt_constantTerm_cond_adelicBox hGc hs g
    have h := hc.comp hray
    rw [hG', constantTerm_const] at h
    exact h
  have hψc : Continuous (fun s : ℂ => ψ s g) := hψjc.comp (Continuous.prodMk_left g)
  have h2 : Tendsto (fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * ψ ((1 / 2 : ℂ) + (t : ℂ)) g) (𝓝[>] (0 : ℝ))
      (𝓝 (((1 / 2 : ℂ) - 1 / 2) * ψ (1 / 2 : ℂ) g)) :=
    (hray.sub tendsto_const_nhds).mul (Tendsto.comp (hψc.tendsto (1 / 2 : ℂ)) hray)
  have h3 : Tendsto (fun t : ℝ => (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) *
      (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
          (G ((1 / 2 : ℂ) + (t : ℂ))) g
        - (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * ψ ((1 / 2 : ℂ) + (t : ℂ)) g)) (𝓝[>] (0 : ℝ))
      (𝓝 ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) * (r - ((1 / 2 : ℂ) - 1 / 2) * ψ (1 / 2 : ℂ) g))) :=
    tendsto_const_nhds.mul (h1.sub h2)
  simpa using h3

private theorem limUnder_sub_mul_eq_char_det_mul :
    ∀ (hα : ∀ x, 0 < ((AutomorphicForm.SlabCovolume.modChar F x : ℝˣ) : ℝ))
      (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hμ : IsUnitaryChar (𝓞 F) F μ)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ (AutomorphicForm.SlabCovolume.modChar F) hα s)
        (etaSnd μ (AutomorphicForm.SlabCovolume.modChar F) hα s) (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ g : AdelicGL2 (𝓞 F) F, MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g)
      (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
      (_hψ : ∀ (s : ℂ) (x : AdelicGL2 (𝓞 F) F),
        ψf s x = ((μ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * ψ s x)
      (_hE : ∀ (s : ℂ) (x : AdelicGL2 (𝓞 F) F),
        ψf s x + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x) =
          ((μ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) *
            (ψ s x + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)))
      (_ha : a < 1 / 2)
      (_hGser : ∀ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        G s x = (s - 1 / 2) * (ψ s x + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F *
          unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)))
      (_hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
      (_hG : ∀ g : AdelicGL2 (𝓞 F) F, G (1 / 2) g = r)
      (g : AdelicGL2 (𝓞 F) F),
    Filter.limUnder (𝓝[≠] (1 / 2 : ℂ)) (fun s : ℂ => (s - (1 / 2 : ℂ)) * Mc s g) =
      ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) * r) := by
  intro hα μ hμ ψf hψf hψfjc Mc hMc ψ hψjc hψ hE ha hGser hGc hG g
  set b : ℂ := (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) with hb_def
  set χg : ℂ := ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) with hχg_def

  have hH : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → (s - (1 / 2 : ℂ)) * Mc s g =
      χg * (b * (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2 (G s) g
        - (s - 1 / 2) * ψ s g)) := by
    intro s hs
    have hψfc : Continuous (ψf s) := hψfjc.comp (continuous_const.prodMk continuous_id)
    have h1 := sub_mul_weylIntertwiningIntegral_eq_mul_constantTerm_sub hα μ μ hμ hμ s hs (ψf s) (hψf s) hψfc g
    have hfun : (fun x : AdelicGL2 (𝓞 F) F => (s - 1 / 2) * (ψf s x + ∑' ξ : F,
        ψf s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))) =
          fun x => ((μ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * G s x := by
      funext x
      rw [hE s x, hGser s x hs]
      ring
    rw [(hMc g).2 s hs, h1, hfun, constantTerm_cond_adelicBox_char_det_mul, hψ s g]
    ring
  have hL := tendsto_const_nhds (x := χg) |>.mul (tendsto_mul_constantTerm_sub_add_ofReal hGc ha hG hψjc g)
  exact limUnder_nhdsNE_sub_mul_eq_of_meromorphicNFOn_of_tendsto_add_ofReal (hMc g).1 hH hL

private theorem tendsto_sub_mul_integral_weylIntertwiningIntegral_add_ofReal :
    ∀ (hα : ∀ x, 0 < ((AutomorphicForm.SlabCovolume.modChar F x : ℝˣ) : ℝ))
      (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 (AutomorphicForm.SlabCovolume.modChar F) hα s)
        (etaSnd 1 (AutomorphicForm.SlabCovolume.modChar F) hα s) (ψ s))
      (_hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
      (_ha : a < 1 / 2)
      (_hGser : ∀ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        G s x = (s - 1 / 2) * (ψ s x + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F *
          unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)))
      (_hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
      (_hG : ∀ g : AdelicGL2 (𝓞 F) F, G (1 / 2) g = r),
    Tendsto (fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) *
        ∫ k, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ ((1 / 2 : ℂ) + (t : ℂ)))
          (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F))
      (𝓝[>] (0 : ℝ)) (𝓝 ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) * r)) := by
  intro hα ψ hψ hψjc ha hGser hGc hG
  set b : ℂ := (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) with hb_def
  have hone : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun _ => by simp
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := eventually_nhdsWithin_of_forall fun t ht => ht
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 := eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)

  set Hf : ℝ → adelicMaximalCompact F → ℂ := fun t k =>
    b * (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
        (G ((1 / 2 : ℂ) + (t : ℂ))) (k : AdelicGL2 (𝓞 F) F)
      - (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * ψ ((1 / 2 : ℂ) + (t : ℂ)) (k : AdelicGL2 (𝓞 F) F)) with hHf_def
  have hre : ∀ t : ℝ, 0 < t → 1 / 2 < ((1 / 2 : ℂ) + (t : ℂ)).re := by
    intro t ht
    simp only [Complex.add_re, Complex.ofReal_re]
    norm_num [ht]
  have hare : ∀ t : ℝ, 0 ≤ t → a < ((1 / 2 : ℂ) + (t : ℂ)).re := by
    intro t ht
    have h : a < 1 / 2 + t := by linarith
    simp only [Complex.add_re, Complex.ofReal_re]
    norm_num [h]

  have heq : (fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) *
      ∫ k, weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψ ((1 / 2 : ℂ) + (t : ℂ)))
        (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun t => ∫ k, Hf t k ∂(maximalCompactHaar F) := by
    filter_upwards [hpos] with t ht
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    have hψc : Continuous (ψ ((1 / 2 : ℂ) + (t : ℂ))) := hψjc.comp (continuous_const.prodMk continuous_id)
    have h1 := sub_mul_weylIntertwiningIntegral_eq_mul_constantTerm_sub hα 1 1 hone hone _ (hre t ht) _
      (hψ ((1 / 2 : ℂ) + (t : ℂ))) hψc (k : AdelicGL2 (𝓞 F) F)
    have hfun : (fun x : AdelicGL2 (𝓞 F) F => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * (ψ ((1 / 2 : ℂ) + (t : ℂ)) x +
        ∑' ξ : F, ψ ((1 / 2 : ℂ) + (t : ℂ))
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))) =
            G ((1 / 2 : ℂ) + (t : ℂ)) :=
      funext fun x => (hGser _ x (hre t ht)).symm
    rw [hfun] at h1
    exact h1
  refine Tendsto.congr' heq.symm ?_

  have hN : IsCompact ((fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image (continuous_const.add Complex.continuous_ofReal)
  have hNa : ((fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) '' Set.Icc (0 : ℝ) 1) ⊆ {s : ℂ | a < s.re} := by
    rintro _ ⟨t, ⟨ht0, -⟩, rfl⟩
    exact hare t ht0
  obtain ⟨M₁, hM₁⟩ := exists_forall_norm_constantTerm_cond_adelicBox_le hGc hN hNa
  obtain ⟨M₂, hM₂⟩ := (hN.prod (isCompact_adelicMaximalCompact F)).exists_bound_of_continuousOn hψjc.continuousOn
  have hlim : ∫ (_k : adelicMaximalCompact F), b * r ∂(maximalCompactHaar F) = b * r := by simp
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖b‖ * (M₁ + 1 * M₂)) ?_ ?_
    (integrable_const (μ := maximalCompactHaar F) (‖b‖ * (M₁ + 1 * M₂))) ?_
  · filter_upwards [hpos] with t ht
    have hGt : Continuous (G ((1 / 2 : ℂ) + (t : ℂ))) :=
      continuous_of_continuousOn_lt_re_prod_univ hGc (hare t ht.le)
    have hct : Continuous fun k : adelicMaximalCompact F =>
        constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
          (G ((1 / 2 : ℂ) + (t : ℂ))) (k : AdelicGL2 (𝓞 F) F) :=
      (continuous_constantTerm_cond_adelicBox_of_continuous hGt).comp continuous_subtype_val
    have hψt : Continuous (ψ ((1 / 2 : ℂ) + (t : ℂ))) := hψjc.comp (continuous_const.prodMk continuous_id)
    have hψk : Continuous fun k : adelicMaximalCompact F => ψ ((1 / 2 : ℂ) + (t : ℂ)) (k : AdelicGL2 (𝓞 F) F) :=
      hψt.comp continuous_subtype_val
    exact (continuous_const.mul (hct.sub (continuous_const.mul hψk))).aestronglyMeasurable
  · filter_upwards [hpos, hlt] with t ht0 ht1
    refine Eventually.of_forall fun k => ?_
    have hmem : (1 / 2 : ℂ) + (t : ℂ) ∈ (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) '' Set.Icc (0 : ℝ) 1 :=
      ⟨t, ⟨ht0.le, ht1.le⟩, rfl⟩
    have e1 := hM₁ _ hmem k
    have e2 : ‖ψ ((1 / 2 : ℂ) + (t : ℂ)) (k : AdelicGL2 (𝓞 F) F)‖ ≤ M₂ :=
      hM₂ ((1 / 2 : ℂ) + (t : ℂ), (k : AdelicGL2 (𝓞 F) F)) ⟨hmem, k.2⟩
    have e3 : ‖((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2‖ ≤ 1 := by
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact ht1.le
    calc ‖Hf t k‖
        = ‖b‖ * ‖constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
            (G ((1 / 2 : ℂ) + (t : ℂ))) (k : AdelicGL2 (𝓞 F) F)
          - (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * ψ ((1 / 2 : ℂ) + (t : ℂ)) (k : AdelicGL2 (𝓞 F) F)‖ := norm_mul _ _
      _ ≤ ‖b‖ * (‖constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
            (G ((1 / 2 : ℂ) + (t : ℂ))) (k : AdelicGL2 (𝓞 F) F)‖
          + ‖((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2‖ * ‖ψ ((1 / 2 : ℂ) + (t : ℂ)) (k : AdelicGL2 (𝓞 F) F)‖) := by
          gcongr
          rw [← norm_mul]
          exact norm_sub_le _ _
      _ ≤ ‖b‖ * (M₁ + 1 * M₂) := by
          gcongr
  · exact Eventually.of_forall fun k => tendsto_mul_constantTerm_sub_add_ofReal hGc ha hG hψjc (k : AdelicGL2 (𝓞 F) F)

private theorem forall_eq_of_series_clauses {a₂ : ℝ} {ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (ha : a < 1 / 2)
    (hGser : ∀ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
      G s x = (s - 1 / 2) * (ψ s x + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)))
    (hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (hr : ∀ g : AdelicGL2 (𝓞 F) F, ∃ E' : ℂ → ℂ,
      MeromorphicOn E' Set.univ ∧
      AnalyticOnNhd ℂ E' ({s : ℂ | a₂ < s.re} \ {(1 / 2 : ℂ)}) ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        E' s = ψ s g + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F *
          unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      Tendsto (fun s : ℂ => (s - 1 / 2) * E' s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 r)) :
    ∀ g : AdelicGL2 (𝓞 F) F, G (1 / 2) g = r := by
  intro g
  obtain ⟨E', -, -, hser, hlim⟩ := hr g
  have hs : a < ((1 / 2 : ℂ)).re := by norm_num [ha]
  exact eq_of_continuousAt_of_eq_sub_mul_of_tendsto_sub_mul
    (S := fun s x => ψ s x +
      ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))
    (continuousAt_of_continuousOn_lt_re_prod_univ hGc hs g) (fun s hs' => hGser s g hs') (fun s hs' => hser s hs') hlim

end ResidueLimitThroughTheConstantTerm

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc"
open scoped Pointwise

section AdaptedDomain

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel

private noncomputable def bruhatRep : Option F → AdelicGL2 (𝓞 F) F
  | none => 1
  | some ξ => adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ)

private theorem bruhatRep_mem_range (τ : Option F) : bruhatRep τ ∈ (globalPoints (𝓞 F) F).range := by
  cases τ with
  | none => exact one_mem _
  | some ξ => exact ⟨gl2Weyl * unipotentGL2 ξ, globalPoints_gl2Weyl_mul_unipotentGL2 ξ⟩

private theorem bruhatRep_eq_of_lt_of_lt {T : ℝ} (hT : 1 ≤ T) {g : AdelicGL2 (𝓞 F) F} {τ τ' : Option F}
    (hτ : T < adelicHeight F (bruhatRep τ * g)) (hτ' : T < adelicHeight F (bruhatRep τ' * g)) : τ = τ' := by
  cases τ with
  | none =>
    cases τ' with
    | none => rfl
    | some ξ' =>
      exfalso
      have h := adelicHeight_weyl_unipotent_mul_lt_of_lt hT (g := g) (by simpa [bruhatRep] using hτ) ξ'
      exact absurd hτ' (not_lt.mpr (by simpa [bruhatRep] using h.le))
  | some ξ =>
    cases τ' with
    | none =>
      exfalso
      have h := (adelicHeight_lt_of_lt_weyl_unipotent_mul hT (g := g) (ξ := ξ) (by simpa [bruhatRep] using hτ)).1
      exact absurd hτ' (not_lt.mpr (by simpa [bruhatRep] using h.le))
    | some ξ' =>
      by_contra hne
      have hne' : ξ' ≠ ξ := fun h => hne (by rw [h])
      have h := (adelicHeight_lt_of_lt_weyl_unipotent_mul hT (g := g) (ξ := ξ) (by simpa [bruhatRep] using hτ)).2
        ξ' hne'
      exact absurd hτ' (not_lt.mpr (by simpa [bruhatRep] using h.le))

variable (F) in

private def highPiece (T : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (τ : Option F) : Set (AdelicGL2 (𝓞 F) F) :=
  Φ₀ ∩ {g | T < adelicHeight F (bruhatRep τ * g)}

variable (F) in

private def lowPart (T : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F) :=
  Φ₀ ∩ {g | ∀ τ : Option F, adelicHeight F (bruhatRep τ * g) ≤ T}

variable (F) in

private def highPart (T : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F) :=
  ⋃ τ : Option F, (fun g => bruhatRep τ * g) '' highPiece F T Φ₀ τ

variable (F) in

private def adaptedDomain (T : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F) :=
  lowPart F T Φ₀ ∪ highPart F T Φ₀

private theorem continuous_adelicHeight_mul (a : AdelicGL2 (𝓞 F) F) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => adelicHeight F (a * g) :=
  (continuous_adelicHeight F).comp (continuous_const.mul continuous_id)

private theorem countable_field : Countable F :=
  Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective

private theorem measurableSet_highPiece {T : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀m : MeasurableSet Φ₀)
    (τ : Option F) : MeasurableSet (highPiece F T Φ₀ τ) :=
  hΦ₀m.inter (isOpen_lt continuous_const (continuous_adelicHeight_mul _)).measurableSet

private theorem measurableSet_lowPart {T : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀m : MeasurableSet Φ₀) :
    MeasurableSet (lowPart F T Φ₀) := by
  haveI := countable_field (F := F)
  have h : {g : AdelicGL2 (𝓞 F) F | ∀ τ : Option F, adelicHeight F (bruhatRep τ * g) ≤ T} =
      ⋂ τ : Option F, {g | adelicHeight F (bruhatRep τ * g) ≤ T} := by
    ext g; simp
  rw [lowPart, h]
  exact hΦ₀m.inter (MeasurableSet.iInter fun τ =>
    (isClosed_le (continuous_adelicHeight_mul _) continuous_const).measurableSet)

private theorem measurableSet_highPart {T : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀m : MeasurableSet Φ₀) :
    MeasurableSet (highPart F T Φ₀) := by
  haveI := countable_field (F := F)
  refine MeasurableSet.iUnion fun τ => ?_
  rw [Set.image_mul_left]
  exact (measurableSet_highPiece hΦ₀m τ).preimage (continuous_const.mul continuous_id).measurable

private theorem measurableSet_adaptedDomain {T : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀m : MeasurableSet Φ₀) :
    MeasurableSet (adaptedDomain F T Φ₀) :=
  (measurableSet_lowPart hΦ₀m).union (measurableSet_highPart hΦ₀m)

private theorem adaptedDomain_subset {T d₁ d₂ : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}) :
    adaptedDomain F T Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} := by
  rintro g (⟨hg, -⟩ | hg)
  · exact hΦ₀s hg
  · obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp hg
    obtain ⟨p, ⟨hp, -⟩, rfl⟩ := hτ
    have h : ideleNorm F (Matrix.GeneralLinearGroup.det (bruhatRep τ * p)) =
        ideleNorm F (Matrix.GeneralLinearGroup.det p) :=
      ideleNorm_det_globalPoints_mul ⟨bruhatRep τ, bruhatRep_mem_range τ⟩ p
    simp only [Set.mem_setOf_eq]
    rw [h]
    exact hΦ₀s hp

private theorem lt_adelicHeight_of_mem_highPart {T : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ highPart F T Φ₀) : T < adelicHeight F g := by
  obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp hg
  obtain ⟨p, ⟨-, hp⟩, rfl⟩ := hτ
  exact hp

private theorem adelicHeight_weyl_unipotent_mul_lt_of_mem_highPart {T : ℝ} (hT : 1 ≤ T) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ highPart F T Φ₀) (ξ : F) :
    adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) < T :=
  adelicHeight_weyl_unipotent_mul_lt_of_lt hT (lt_adelicHeight_of_mem_highPart hg) ξ

private theorem adelicHeight_bruhatRep_mul_le_of_mem_lowPart {T : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ lowPart F T Φ₀) (τ : Option F) : adelicHeight F (bruhatRep τ * g) ≤ T :=
  hg.2 τ

private theorem lowPart_subset (T : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) : lowPart F T Φ₀ ⊆ Φ₀ :=
  Set.inter_subset_left

private theorem disjoint_lowPart_highPart (T : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) :
    Disjoint (lowPart F T Φ₀) (highPart F T Φ₀) :=
  Set.disjoint_left.mpr fun g hl hh =>
    absurd (lt_adelicHeight_of_mem_highPart hh) (not_lt.mpr (by simpa [bruhatRep] using hl.2 none))

private theorem measure_smul_inter_smul_eq_zero {d₁ d₂ : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    {a b : (globalPoints (𝓞 F) F).range} (hab : a ≠ b) :
    (adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}
      (a • Φ₀ ∩ b • Φ₀) = 0 :=
  hΦ₀.aedisjoint hab

private theorem isFundamentalDomain_adaptedDomain {T d₁ d₂ : ℝ} (hT : 1 ≤ T) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀m : MeasurableSet Φ₀)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})) :
    IsFundamentalDomain (globalPoints (𝓞 F) F).range (adaptedDomain F T Φ₀)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}) := by
  haveI := countable_globalPoints_range (F := F)
  haveI := measurableConstSMul_globalPoints_range (F := F)
  haveI := smulInvariantMeasure_restrict_setOf_ideleNorm_det_mem_Icc (F := F) d₁ d₂
  haveI := countable_field (F := F)
  set Γ := (globalPoints (𝓞 F) F).range with hΓ
  set μS := (adelicGLHaar (Fin 2) (𝓞 F) F).restrict
    {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} with hμS

  set t : Option F → Γ := fun τ => ⟨bruhatRep τ, bruhatRep_mem_range τ⟩ with ht
  have ht_smul : ∀ (τ : Option F) (g : AdelicGL2 (𝓞 F) F), t τ • g = bruhatRep τ * g := fun τ g => rfl
  refine IsFundamentalDomain.mk'' (measurableSet_adaptedDomain hΦ₀m).nullMeasurableSet ?_ ?_
    fun γ => (measurePreserving_smul γ μS).quasiMeasurePreserving
  ·
    filter_upwards [hΦ₀.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    by_cases hlow : ∀ τ : Option F, adelicHeight F (bruhatRep τ * (γ • x)) ≤ T
    · exact ⟨γ, Or.inl ⟨hγ, hlow⟩⟩
    · simp only [not_forall, not_le] at hlow
      obtain ⟨τ, hτ⟩ := hlow
      refine ⟨t τ * γ, Or.inr (Set.mem_iUnion.mpr ⟨τ, γ • x, ⟨hγ, hτ⟩, ?_⟩)⟩
      rw [mul_smul, ht_smul]
  ·
    intro γ hγ1

    have hN : μS (⋃ a : Γ, ⋃ b : Γ, ⋃ (_ : a ≠ b), a • Φ₀ ∩ b • Φ₀) = 0 := by
      refine (measure_iUnion_null_iff.mpr fun a => measure_iUnion_null_iff.mpr fun b =>
        measure_iUnion_null_iff.mpr fun hab => ?_)
      exact measure_smul_inter_smul_eq_zero hΦ₀ hab
    refine measure_mono_null ?_ hN
    rintro g ⟨hgγ, hg⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hgγ

    have hsep : ∀ {a b : Γ}, g ∈ a • Φ₀ → g ∈ b • Φ₀ → a ≠ b →
        g ∈ ⋃ a : Γ, ⋃ b : Γ, ⋃ (_ : a ≠ b), a • Φ₀ ∩ b • Φ₀ := fun ha hb hab =>
      Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨hab, ha, hb⟩⟩⟩

    have memA : ∀ {y : AdelicGL2 (𝓞 F) F}, y ∈ adaptedDomain F T Φ₀ →
        (y ∈ lowPart F T Φ₀ ∧ y ∈ (1 : Γ) • Φ₀) ∨
          ∃ τ p, p ∈ highPiece F T Φ₀ τ ∧ y = bruhatRep τ * p ∧ y ∈ t τ • Φ₀ := by
      rintro y (hy | hy)
      · exact Or.inl ⟨hy, by rw [one_smul]; exact hy.1⟩
      · obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp hy
        obtain ⟨p, hp, rfl⟩ := hτ
        exact Or.inr ⟨τ, p, hp, rfl, ⟨p, hp.1, ht_smul τ p⟩⟩
    rcases memA hg with ⟨hgl, hg1⟩ | ⟨τ', p', hp', hgp', hgτ'⟩
    · rcases memA hgγ with ⟨hγl, hγ1'⟩ | ⟨τ, p, hp, hγp, hγτ⟩
      ·
        have hgγ0 : g ∈ γ • Φ₀ := by
          rw [Set.mem_smul_set_iff_inv_smul_mem]; rwa [one_smul] at hγ1'
        exact hsep hg1 hgγ0 (Ne.symm hγ1)
      ·
        have hgγ0 : g ∈ (γ * t τ) • Φ₀ := by
          rw [Set.mem_smul_set_iff_inv_smul_mem, mul_inv_rev, mul_smul]
          have : (t τ)⁻¹ • (γ⁻¹ • g) = p := by rw [hγp, ← ht_smul, inv_smul_smul]
          rw [this]; exact hp.1
        refine hsep hg1 hgγ0 fun h1 => ?_

        have hginv : γ⁻¹ = t τ := inv_eq_of_mul_eq_one_right h1.symm
        have hgp : g = p := by
          rw [hginv] at hγp
          have h2 : t τ • g = t τ • p := by rw [hγp, ht_smul]
          exact MulAction.injective (t τ) h2
        subst hgp
        exact absurd hp.2 (not_lt.mpr (hgl.2 τ))
    · rcases memA hgγ with ⟨hγl, hγ1'⟩ | ⟨τ, p, hp, hγp, hγτ⟩
      ·
        have hgγ0 : g ∈ γ • Φ₀ := by
          rw [Set.mem_smul_set_iff_inv_smul_mem]; rwa [one_smul] at hγ1'
        refine hsep hgτ' hgγ0 fun h1 => ?_

        have hgp : γ⁻¹ • g = p' := by rw [← h1, hgp', ← ht_smul, inv_smul_smul]
        have hle := hγl.2 τ'
        rw [hgp] at hle
        exact absurd hp'.2 (not_lt.mpr hle)
      ·
        have hgγ0 : g ∈ (γ * t τ) • Φ₀ := by
          rw [Set.mem_smul_set_iff_inv_smul_mem, mul_inv_rev, mul_smul]
          have : (t τ)⁻¹ • (γ⁻¹ • g) = p := by rw [hγp, ← ht_smul, inv_smul_smul]
          rw [this]; exact hp.1
        refine hsep hgτ' hgγ0 fun h1 => ?_

        have hpp : p' = p := by
          have h2 : (t τ')⁻¹ • g = p' := by rw [hgp', ← ht_smul, inv_smul_smul]
          have h3 : (t τ')⁻¹ • g = p := by
            rw [h1, mul_inv_rev, mul_smul, hγp, ← ht_smul, inv_smul_smul]
          rw [← h2, h3]
        have hp'2 : T < adelicHeight F (bruhatRep τ' * p) := by rw [← hpp]; exact hp'.2
        have hττ' : τ = τ' := bruhatRep_eq_of_lt_of_lt hT (g := p) hp.2 hp'2
        subst hττ'
        exact hγ1 (mul_right_cancel (h1.symm.trans (one_mul _).symm))

private theorem measure_adaptedDomain_eq {T d₁ d₂ : ℝ} (hT : 1 ≤ T) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀m : MeasurableSet Φ₀)
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})) :
    adelicGLHaar (Fin 2) (𝓞 F) F (adaptedDomain F T Φ₀) = adelicGLHaar (Fin 2) (𝓞 F) F Φ₀ :=
  measure_eq_of_isFundamentalDomain_slab (adaptedDomain_subset hΦ₀s) (isFundamentalDomain_adaptedDomain hT hΦ₀m hΦ₀)
    hΦ₀s hΦ₀

end AdaptedDomain

end AutomorphicForm.SlabCovolume

namespace ShellIntegrals

private theorem setIntegral_inv_mul_indicator_slab_sq_mul {d₁ d₂ c : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hc : 0 < c) :
    ∫ y in Set.Ioi (0 : ℝ), ((y : ℂ))⁻¹ * (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℂ)) (y ^ 2 * c)
      = ((Real.log (d₂ / d₁) / 2 : ℝ) : ℂ) := by
  set l : ℝ := Real.sqrt (d₁ / c) with hl_def
  set u : ℝ := Real.sqrt (d₂ / c) with hu_def
  have hl : 0 < l := Real.sqrt_pos.mpr (div_pos hd₁ hc)
  have hu : 0 < u := Real.sqrt_pos.mpr (div_pos (hd₁.trans_le hd) hc)
  have hlu : l ≤ u := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hd hc.le)
  have hpt : ∀ y ∈ Set.Ioi (0 : ℝ),
      ((y : ℂ))⁻¹ * (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℂ)) (y ^ 2 * c)
        = (Set.Icc l u).indicator (fun y : ℝ => ((y : ℂ))⁻¹) y := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    have hmem : y ^ 2 * c ∈ Set.Icc d₁ d₂ ↔ y ∈ Set.Icc l u := by
      simp only [Set.mem_Icc, hl_def, hu_def]
      rw [Real.sqrt_le_left hy'.le, Real.le_sqrt hy'.le (div_pos (hd₁.trans_le hd) hc).le,
        div_le_iff₀ hc, le_div_iff₀ hc]
    by_cases h : y ^ 2 * c ∈ Set.Icc d₁ d₂
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h), mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.mpr h')), mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.mpr (show Set.Icc l u ⊆ Set.Ioi (0 : ℝ) from fun y hy => hl.trans_le hy.1),
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hlu]
  have hcast : ∀ y : ℝ, ((y : ℂ))⁻¹ = ((y⁻¹ : ℝ) : ℂ) := fun y => (Complex.ofReal_inv y).symm
  simp_rw [hcast]
  rw [intervalIntegral.integral_ofReal, integral_inv_of_pos hl hu]
  congr 1
  have hd₂c : 0 ≤ d₂ / c := (div_pos (hd₁.trans_le hd) hc).le
  rw [hu_def, hl_def, ← Real.sqrt_div hd₂c, Real.log_sqrt (div_nonneg hd₂c (div_pos hd₁ hc).le)]
  congr 2
  field_simp

private theorem setIntegral_inv_mul_indicator_shell_mul_cpow_mul_inv {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂)
    {e : ℂ} (he : e ≠ 1) :
    ∫ y in Set.Ioi (0 : ℝ),
        ((y : ℂ))⁻¹ * ((Set.Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) y * ((y : ℂ) ^ e * ((y⁻¹ : ℝ) : ℂ)))
      = ((x₂ : ℂ) ^ (e - 1) - (x₁ : ℂ) ^ (e - 1)) / (e - 1) := by
  have hpt : ∀ y ∈ Set.Ioi (0 : ℝ),
      ((y : ℂ))⁻¹ * ((Set.Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) y * ((y : ℂ) ^ e * ((y⁻¹ : ℝ) : ℂ)))
        = (Set.Ioc x₁ x₂).indicator (fun y : ℝ => (y : ℂ) ^ (e - 2)) y := by
    intro y hy
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hy)
    by_cases h : y ∈ Set.Ioc x₁ x₂
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.cpow_sub _ _ hy0, Complex.cpow_ofNat,
        Complex.ofReal_inv]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul, mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr (show Set.Ioc x₁ x₂ ⊆ Set.Ioi (0 : ℝ) from fun y hy => hx₁.trans hy.1),
    ← intervalIntegral.integral_of_le hx,
    integral_cpow (Or.inr ⟨?_, Set.notMem_uIcc_of_lt hx₁ (hx₁.trans_le hx)⟩)]
  · have h21 : e - 2 + 1 = e - 1 := by ring
    rw [h21]
  · exact fun h => he (by linear_combination h)

end ShellIntegrals

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc NumberField.AdelicLevel"
open scoped Pointwise

section HighSheet

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel

private theorem adelicHeight_globalPoints_mul_of_mem_borelSubgroup {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F)
    (g : AdelicGL2 (𝓞 F) F) : adelicHeight F (globalPoints (𝓞 F) F γ * g) = adelicHeight F g := by
  have hα := (AutomorphicForm.isInducedSection_adelicHeight_cpow F).1
  have h := globalPoints_mul_eq_of_isInducedSection_etaFst_etaSnd_one F _ hα
    (isPrincipalTrivial_distribHaarChar_adeleRing F) (1 / 2)
    ((AutomorphicForm.isInducedSection_adelicHeight_cpow F).2.2 hα (1 / 2)) hγ g
  have hone : (1 / 2 : ℂ) + 1 / 2 = 1 := by norm_num
  simp only [hone, Complex.cpow_one, Complex.ofReal_inj] at h
  exact h

omit [NumberField F] in

private theorem exists_mem_borelSubgroup_eq_mul_gl2Weyl_mul_unipotentGL2 (δ : GL (Fin 2) F)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    ∃ β ∈ borelSubgroup F, ∃ ξ : F, δ = β * (gl2Weyl * unipotentGL2 ξ) := by
  refine ⟨δ * (gl2Weyl * unipotentGL2 ((δ : Matrix (Fin 2) (Fin 2) F) 1 1 / (δ : Matrix (Fin 2) (Fin 2) F) 1 0))⁻¹,
    ?_, (δ : Matrix (Fin 2) (Fin 2) F) 1 1 / (δ : Matrix (Fin 2) (Fin 2) F) 1 0, by rw [inv_mul_cancel_right]⟩
  have hinv : ∀ ξ : F, (unipotentGL2 ξ)⁻¹ = unipotentGL2 (-ξ) := fun ξ =>
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  rw [mem_borelSubgroup_iff, mul_inv_rev, gl2Weyl_inv, hinv]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp
  ring

variable (F) in

private def highSlab (T d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | T < adelicHeight F g} ∩ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

private theorem measurableSet_highSlab (T d₁ d₂ : ℝ) : MeasurableSet (highSlab F T d₁ d₂) :=
  (isOpen_lt continuous_const (continuous_adelicHeight F)).measurableSet.inter
    (measurableSet_setOf_ideleNorm_det_mem_Icc (F := F) d₁ d₂)

private def leftStabilizer (S : Set (AdelicGL2 (𝓞 F) F)) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {x | ∀ g, x * g ∈ S ↔ g ∈ S}
  mul_mem' := by
    intro x y hx hy g
    rw [mul_assoc, hx (y * g), hy g]
  one_mem' := by
    intro g
    rw [one_mul]
  inv_mem' := by
    intro x hx g
    rw [← hx (x⁻¹ * g), mul_inv_cancel_left]

private theorem det_unipotentGL2_eq_one (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  ext
  simp [Matrix.det_fin_two]

private theorem map_borelSubgroup_le_leftStabilizer_highSlab (T d₁ d₂ : ℝ) :
    (borelSubgroup F).map (globalPoints (𝓞 F) F) ≤ leftStabilizer (highSlab F T d₁ d₂) := by
  rintro _ ⟨γ, hγ, rfl⟩
  show ∀ g : AdelicGL2 (𝓞 F) F, globalPoints (𝓞 F) F γ * g ∈ highSlab F T d₁ d₂ ↔ g ∈ highSlab F T d₁ d₂
  intro g
  have hdet : ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F γ * g)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    ideleNorm_det_globalPoints_mul ⟨globalPoints (𝓞 F) F γ, γ, rfl⟩ g
  simp only [highSlab, Set.mem_inter_iff, Set.mem_setOf_eq, adelicHeight_globalPoints_mul_of_mem_borelSubgroup hγ,
    hdet]

private theorem rationalTorus_le_map_borelSubgroup :
    rationalTorus F ≤ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  refine sup_le ?_ ?_
  · rintro _ ⟨a, rfl⟩
    refine ⟨Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom a, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_borelSubgroup_iff, Units.coe_map]
    simp
  · rintro _ ⟨a, rfl⟩
    refine ⟨diagOne a, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_borelSubgroup_iff, diagOne_coe_apply]
    simp

private theorem rationalTorusUnipotent_le_leftStabilizer_highSlab (T d₁ d₂ : ℝ) :
    rationalTorusUnipotent F ≤ leftStabilizer (highSlab F T d₁ d₂) := by
  refine sup_le (rationalTorus_le_map_borelSubgroup.trans (map_borelSubgroup_le_leftStabilizer_highSlab T d₁ d₂)) ?_
  rintro _ ⟨x, rfl⟩
  have hα := (AutomorphicForm.isInducedSection_adelicHeight_cpow F).1
  show ∀ g : AdelicGL2 (𝓞 F) F, unipotentGL2 x.toAdd * g ∈ highSlab F T d₁ d₂ ↔ g ∈ highSlab F T d₁ d₂
  intro g
  simp only [highSlab, Set.mem_inter_iff, Set.mem_setOf_eq, adelicHeight_unipotentGL2_mul hα, map_mul,
    det_unipotentGL2_eq_one, one_mul]

private theorem mul_mem_highSlab_iff_of_mem_map_borelSubgroup {T d₁ d₂ : ℝ} {b : AdelicGL2 (𝓞 F) F}
    (hb : b ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F)) (g : AdelicGL2 (𝓞 F) F) :
    b * g ∈ highSlab F T d₁ d₂ ↔ g ∈ highSlab F T d₁ d₂ :=
  map_borelSubgroup_le_leftStabilizer_highSlab T d₁ d₂ hb g

private theorem mul_mem_highSlab_iff_of_mem_rationalTorusUnipotent {T d₁ d₂ : ℝ} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ rationalTorusUnipotent F) (g : AdelicGL2 (𝓞 F) F) :
    x * g ∈ highSlab F T d₁ d₂ ↔ g ∈ highSlab F T d₁ d₂ :=
  rationalTorusUnipotent_le_leftStabilizer_highSlab T d₁ d₂ hx g

private theorem highPart_subset_highSlab {T d₁ d₂ : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}) :
    highPart F T Φ₀ ⊆ highSlab F T d₁ d₂ := fun _ hg =>
  ⟨lt_adelicHeight_of_mem_highPart hg, adaptedDomain_subset hΦ₀s (Or.inr hg)⟩

private theorem mem_map_borelSubgroup_of_lt_of_lt {T : ℝ} (hT : 1 ≤ T) {γ : GL (Fin 2) F} {g : AdelicGL2 (𝓞 F) F}
    (hg : T < adelicHeight F g) (hγg : T < adelicHeight F (globalPoints (𝓞 F) F γ * g)) :
    globalPoints (𝓞 F) F γ ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  by_cases h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · exact ⟨γ, h10, rfl⟩
  · exfalso
    have hle := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ h10 g
    have hlt : (1 : ℝ) < adelicHeight F (globalPoints (𝓞 F) F γ * g) * adelicHeight F g := by
      calc (1 : ℝ) ≤ T * T := by nlinarith
        _ < adelicHeight F (globalPoints (𝓞 F) F γ * g) * adelicHeight F g :=
          mul_lt_mul'' hγg hg (by linarith) (by linarith)
    linarith

private theorem isFundamentalDomain_highPart {T d₁ d₂ : ℝ} (hT : 1 ≤ T) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀m : MeasurableSet Φ₀) (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})) :
    IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) (highPart F T Φ₀)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (highSlab F T d₁ d₂)) := by
  haveI := countable_globalPoints_range (F := F)
  haveI := measurableConstSMul_globalPoints_range (F := F)
  haveI := smulInvariantMeasure_restrict_setOf_ideleNorm_det_mem_Icc (F := F) d₁ d₂
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hΦ₁ := isFundamentalDomain_adaptedDomain hT hΦ₀m hΦ₀
  have hle : (borelSubgroup F).map (globalPoints (𝓞 F) F) ≤ (globalPoints (𝓞 F) F).range :=
    Subgroup.map_le_range _ _

  haveI : Countable ↥((borelSubgroup F).map (globalPoints (𝓞 F) F)) :=
    Function.Injective.countable (Subgroup.inclusion_injective hle)
  haveI : MeasurableConstSMul ↥((borelSubgroup F).map (globalPoints (𝓞 F) F)) (AdelicGL2 (𝓞 F) F) := by
    refine ⟨fun b => ?_⟩
    show Measurable fun g : AdelicGL2 (𝓞 F) F => (b : AdelicGL2 (𝓞 F) F) * g
    exact (continuous_const.mul continuous_id).measurable
  have hS := measurableSet_highSlab (F := F) T d₁ d₂
  haveI : SMulInvariantMeasure ↥((borelSubgroup F).map (globalPoints (𝓞 F) F)) (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (highSlab F T d₁ d₂)) := by
    refine ⟨fun b s hs => ?_⟩
    have hmeas : Measurable fun g : AdelicGL2 (𝓞 F) F => b • g := by
      show Measurable fun g : AdelicGL2 (𝓞 F) F => (b : AdelicGL2 (𝓞 F) F) * g
      exact (continuous_const.mul continuous_id).measurable
    have hpreS : (fun g : AdelicGL2 (𝓞 F) F => b • g) ⁻¹' highSlab F T d₁ d₂ = highSlab F T d₁ d₂ := by
      ext g
      exact mul_mem_highSlab_iff_of_mem_map_borelSubgroup b.2 g
    rw [Measure.restrict_apply' hS, Measure.restrict_apply' hS]
    have hpre : (fun g : AdelicGL2 (𝓞 F) F => b • g) ⁻¹' s ∩ highSlab F T d₁ d₂ =
        (fun g : AdelicGL2 (𝓞 F) F => b • g) ⁻¹' (s ∩ highSlab F T d₁ d₂) := by
      rw [Set.preimage_inter, hpreS]
    rw [hpre]
    show adelicGLHaar (Fin 2) (𝓞 F) F ((fun g => (b : AdelicGL2 (𝓞 F) F) * g) ⁻¹' (s ∩ highSlab F T d₁ d₂)) = _
    rw [measure_preimage_mul]
  have hsub : highPart F T Φ₀ ⊆ highSlab F T d₁ d₂ := highPart_subset_highSlab hΦ₀s
  have hrest : (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (highSlab F T d₁ d₂) ≤
      (adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  refine IsFundamentalDomain.mk'' ((measurableSet_highPart hΦ₀m).nullMeasurableSet) ?_ ?_
    fun b => (measurePreserving_smul b _).quasiMeasurePreserving
  ·
    have h1 : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F).restrict (highSlab F T d₁ d₂), g ∈ highSlab F T d₁ d₂ :=
      ae_restrict_mem hS
    have h2 : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F).restrict (highSlab F T d₁ d₂),
        ∃ γ : (globalPoints (𝓞 F) F).range, γ • g ∈ adaptedDomain F T Φ₀ :=
      hΦ₁.ae_covers.filter_mono (ae_mono hrest)
    filter_upwards [h1, h2] with g hg hγ
    obtain ⟨γ, hγ⟩ := hγ
    obtain ⟨δ₀, hδ₀⟩ := MonoidHom.mem_range.mp γ.2
    have hγg : γ • g = globalPoints (𝓞 F) F δ₀ * g := by rw [Subgroup.smul_def, smul_eq_mul, hδ₀]
    rcases hγ with hlow | hhigh
    ·
      exfalso
      have hback : globalPoints (𝓞 F) F δ₀⁻¹ * (γ • g) = g := by
        rw [hγg, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      by_cases h10 : ((δ₀⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      · have h := adelicHeight_globalPoints_mul_of_mem_borelSubgroup h10 (γ • g)
        rw [hback] at h
        have hle := adelicHeight_bruhatRep_mul_le_of_mem_lowPart hlow none
        simp only [bruhatRep, one_mul] at hle
        have hle' : adelicHeight F g ≤ T := by rw [h]; exact hle
        exact absurd hg.1 (not_lt.mpr hle')
      · obtain ⟨β, hβ, ξ, hδ⟩ := exists_mem_borelSubgroup_eq_mul_gl2Weyl_mul_unipotentGL2 δ₀⁻¹ h10
        have h := adelicHeight_globalPoints_mul_of_mem_borelSubgroup hβ (bruhatRep (some ξ) * (γ • g))
        have hprod : globalPoints (𝓞 F) F β * (bruhatRep (some ξ) * (γ • g)) =
            globalPoints (𝓞 F) F δ₀⁻¹ * (γ • g) := by
          simp only [bruhatRep]
          rw [hδ, map_mul, globalPoints_gl2Weyl_mul_unipotentGL2]
          simp only [mul_assoc]
        rw [hback] at hprod
        rw [hprod] at h
        have hle := adelicHeight_bruhatRep_mul_le_of_mem_lowPart hlow (some ξ)
        have hle' : adelicHeight F g ≤ T := by rw [h]; exact hle
        exact absurd hg.1 (not_lt.mpr hle')
    ·
      have hmem : (γ : AdelicGL2 (𝓞 F) F) ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
        rw [← hδ₀]
        exact mem_map_borelSubgroup_of_lt_of_lt hT hg.1 (by rw [← hγg]; exact lt_adelicHeight_of_mem_highPart hhigh)
      exact ⟨⟨γ, hmem⟩, hhigh⟩
  ·
    intro b hb
    set γ : (globalPoints (𝓞 F) F).range := ⟨b, hle b.2⟩ with hγdef
    have hγ1 : γ ≠ 1 := fun h => hb (Subtype.ext (by simpa [hγdef] using congrArg Subtype.val h))
    have hnull := hΦ₁.aedisjoint hγ1
    refine measure_mono_null ?_ (Measure.absolutelyContinuous_of_le hrest hnull)
    rintro x ⟨⟨y, hy, rfl⟩, hx⟩
    exact ⟨⟨y, Or.inr hy, rfl⟩, ⟨b • y, Or.inr hx, one_smul _ _⟩⟩

end HighSheet

end AutomorphicForm.SlabCovolume

section UntwistingTheSelfDualFamily

variable {F : Type} [Field F] [NumberField F]

private theorem val_inv_char_apply (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((μ⁻¹ x : ℂˣ) : ℂ) = (((μ x : ℂˣ) : ℂ))⁻¹ := by
  rw [← Units.val_inv_eq_inv_val]
  rfl

private theorem det_eq_borelDiagFst_mul_borelDiagSnd (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det b =
      borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) * borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) := by
  have h10 : (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := hb
  ext
  show (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)).det =
    (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 * (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero]

private theorem isInducedSection_fnTwist_inv (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd μ α hα s) ψ) :
    IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (fnTwist F μ⁻¹ ψ) := by
  intro b hb g
  have hdet : Matrix.GeneralLinearGroup.det (b * g) =
      borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) * borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) *
        Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, det_eq_borelDiagFst_mul_borelDiagSnd b hb]
  have h1 : (((μ (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)) ≠ 0 := Units.ne_zero _
  have h2 : (((μ (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)) ≠ 0 := Units.ne_zero _
  have h3 : (((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) ≠ 0 := Units.ne_zero _
  simp only [fnTwist_apply, chiDet, hdet, hψ b hb g, etaFst_apply, etaSnd_apply, val_inv_char_apply, map_mul,
    MonoidHom.one_apply, Units.val_mul, one_mul]
  field_simp

private theorem rightTranslatesSpanFinite_mul_of_mul {G : Type*} [Group G] (K : Subgroup G) {χ f : G → ℂ}
    (hχ : ∀ x k : G, χ (x * k) = χ x * χ k) (hf : RightTranslatesSpanFinite K f) :
    RightTranslatesSpanFinite K (fun x => χ x * f x) := by
  classical
  obtain ⟨t, ht⟩ := hf
  let L : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun h x => χ x * h x
      map_add' := fun h₁ h₂ => by
        funext x
        simp only [Pi.add_apply, mul_add]
      map_smul' := fun c h => by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine ⟨t.image L, fun k hk => ?_⟩
  have hmem : L (fun x => f (x * k)) ∈ Submodule.span ℂ ((t.image L : Finset (G → ℂ)) : Set (G → ℂ)) := by
    rw [Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem (ht k hk)
  have hfun : (fun x => χ (x * k) * f (x * k)) = χ k • L (fun x => f (x * k)) := by
    funext x
    show χ (x * k) * f (x * k) = χ k * (χ x * f (x * k))
    rw [hχ x k]
    ring
  rw [hfun]
  exact Submodule.smul_mem _ _ hmem

private theorem isArchKFinite_fnTwist (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hψ : IsArchKFinite F ψ) : IsArchKFinite F (fnTwist F η ψ) :=
  fun w => rightTranslatesSpanFinite_mul_of_mul (archRowIsometrySubgroup F w) (AutomorphicForm.chiDet_mul η) (hψ w)

private theorem continuous_det_adelicGL2 :
    Continuous (fun g : AdelicGL2 (𝓞 F) F => Matrix.GeneralLinearGroup.det g) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_det Units.continuous_val
  · exact Continuous.matrix_det Units.continuous_coe_inv

private theorem continuous_chiDet_inv (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ)) : Continuous (chiDet (𝓞 F) F μ⁻¹) := by
  have h : chiDet (𝓞 F) F μ⁻¹ = fun g => (((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))⁻¹ := by
    funext g
    simp only [chiDet, val_inv_char_apply]
  rw [h]
  exact (hμc.comp continuous_det_adelicGL2).inv₀ fun g => Units.ne_zero _

private theorem continuous_uncurry_fnTwist_inv (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ)) {ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2)) :
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => fnTwist F μ⁻¹ (ψf p.1) p.2) := by
  simp only [fnTwist_apply]
  exact ((continuous_chiDet_inv μ hμc).comp continuous_snd).mul hψjc

private theorem differentiable_fnTwist_inv (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hψhol : ∀ g, Differentiable ℂ (fun s => ψf s g)) (g : AdelicGL2 (𝓞 F) F) :
    Differentiable ℂ (fun s => fnTwist F μ⁻¹ (ψf s) g) := by
  simp only [fnTwist_apply]
  exact (hψhol g).const_mul _

private theorem eq_char_det_mul_fnTwist_inv (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (s : ℂ) (x : AdelicGL2 (𝓞 F) F) :
    ψf s x = ((μ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * fnTwist F μ⁻¹ (ψf s) x := by
  simp only [fnTwist_apply, chiDet, val_inv_char_apply]
  exact (mul_inv_cancel_left₀ (Units.ne_zero _) _).symm

private theorem bruhat_series_eq_char_det_mul (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμic : IsIdeleClassChar (𝓞 F) F μ)
    (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (s : ℂ) (x : AdelicGL2 (𝓞 F) F) :
    ψf s x + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x) =
      ((μ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) *
        (fnTwist F μ⁻¹ (ψf s) x + ∑' ξ : F, fnTwist F μ⁻¹ (ψf s)
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)) := by
  have hterm : ∀ ξ : F,
      ψf s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x) =
        ((μ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * fnTwist F μ⁻¹ (ψf s)
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x) := by
    intro ξ
    have hχ : chiDet (𝓞 F) F μ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x) =
        chiDet (𝓞 F) F μ x := by
      rw [mul_assoc, adelicWeyl, chiDet_globalPoints_mul F μ hμic]
      simp only [chiDet, det_unipotentGL2_mul]
    have hχ' : ((μ (Matrix.GeneralLinearGroup.det
        (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)) : ℂˣ) : ℂ) =
          ((μ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) := hχ
    rw [eq_char_det_mul_fnTwist_inv μ ψf s
      (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x), hχ']
  rw [mul_add, ← tsum_mul_left]
  congr 1
  · exact eq_char_det_mul_fnTwist_inv μ ψf s x
  · exact tsum_congr hterm

private theorem integral_mul_conj_char_det_eq_integral_fnTwist_inv (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    (∫ k, φ (k : AdelicGL2 (𝓞 F) F)
        * starRingEnd ℂ ((μ (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) : ℂˣ) : ℂ)
      ∂(maximalCompactHaar F)) =
      ∫ k, fnTwist F μ⁻¹ φ (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  have hconj : ∀ z : ℂ, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := by
    intro z hz
    have hn : Complex.normSq z = 1 := by rw [← Complex.sq_norm, hz, one_pow]
    rw [Complex.inv_def, hn, inv_one, Complex.ofReal_one, mul_one]
  simp only [fnTwist_apply, chiDet, val_inv_char_apply]
  rw [hconj _ (hμ _)]
  ring

end UntwistingTheSelfDualFamily

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc"
open scoped Pointwise

section TruncatedBracket

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel

private noncomputable def brT (T : ℝ) (φ m : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) : ℂ :=
  (Set.Ioc 0 T).indicator (fun _ => (1 : ℂ)) (adelicHeight F x) * φ x -
    (Set.Ioi T).indicator (fun _ => (1 : ℂ)) (adelicHeight F x) * m x

private theorem brT_apply_of_le {T : ℝ} (φ m : AdelicGL2 (𝓞 F) F → ℂ) {x : AdelicGL2 (𝓞 F) F}
    (hx : adelicHeight F x ≤ T) : brT T φ m x = φ x := by
  have h1 : adelicHeight F x ∈ Set.Ioc 0 T := ⟨adelicHeight_pos x, hx⟩
  have h2 : adelicHeight F x ∉ Set.Ioi T := fun h => not_lt.mpr hx (Set.mem_Ioi.mp h)
  rw [brT, Set.indicator_of_mem h1, Set.indicator_of_notMem h2, one_mul, zero_mul, sub_zero]

private theorem brT_apply_of_lt {T : ℝ} (φ m : AdelicGL2 (𝓞 F) F → ℂ) {x : AdelicGL2 (𝓞 F) F}
    (hx : T < adelicHeight F x) : brT T φ m x = -m x := by
  have h1 : adelicHeight F x ∉ Set.Ioc 0 T := fun h => not_le.mpr hx h.2
  have h2 : adelicHeight F x ∈ Set.Ioi T := Set.mem_Ioi.mpr hx
  rw [brT, Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_mul, one_mul, zero_sub]

private theorem pseudoEisenstein_brT_of_mem_lowPart {T : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (φ m : AdelicGL2 (𝓞 F) F → ℂ) {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ lowPart F T Φ₀) :
    pseudoEisenstein F (brT T φ m) g =
      φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) := by
  have h0 : adelicHeight F g ≤ T := by simpa [bruhatRep] using adelicHeight_bruhatRep_mul_le_of_mem_lowPart hg none
  have hξ : ∀ ξ : F,
      adelicHeight F (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) ≤ T :=
    fun ξ => by simpa [bruhatRep] using adelicHeight_bruhatRep_mul_le_of_mem_lowPart hg (some ξ)
  rw [pseudoEisenstein_apply, brT_apply_of_le φ m h0, tsum_congr fun ξ => brT_apply_of_le φ m (hξ ξ)]

private theorem pseudoEisenstein_brT_of_mem_highPart {T : ℝ} (hT : 1 ≤ T) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (φ m : AdelicGL2 (𝓞 F) F → ℂ) {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ highPart F T Φ₀) :
    pseudoEisenstein F (brT T φ m) g =
      (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) - m g := by
  rw [pseudoEisenstein_apply, brT_apply_of_lt φ m (lt_adelicHeight_of_mem_highPart hg),
    tsum_congr fun ξ => brT_apply_of_le φ m (adelicHeight_weyl_unipotent_mul_lt_of_mem_highPart hT hg ξ).le]
  ring

private theorem setIntegral_adaptedDomain_eq_add {T : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀m : MeasurableSet Φ₀)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IntegrableOn f (adaptedDomain F T Φ₀) (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    ∫ g in adaptedDomain F T Φ₀, f g ∂adelicGLHaar (Fin 2) (𝓞 F) F =
      (∫ g in lowPart F T Φ₀, f g ∂adelicGLHaar (Fin 2) (𝓞 F) F) +
        ∫ g in highPart F T Φ₀, f g ∂adelicGLHaar (Fin 2) (𝓞 F) F :=
  setIntegral_union (disjoint_lowPart_highPart T Φ₀) (measurableSet_highPart hΦ₀m)
    (hf.mono_set Set.subset_union_left) (hf.mono_set Set.subset_union_right)

private theorem measure_lowPart_add_measure_highPart {T d₁ d₂ : ℝ} (hT : 1 ≤ T) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀m : MeasurableSet Φ₀)
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})) :
    adelicGLHaar (Fin 2) (𝓞 F) F (lowPart F T Φ₀) + adelicGLHaar (Fin 2) (𝓞 F) F (highPart F T Φ₀) =
      adelicGLHaar (Fin 2) (𝓞 F) F Φ₀ := by
  rw [← measure_union (disjoint_lowPart_highPart T Φ₀) (measurableSet_highPart hΦ₀m),
    ← measure_adaptedDomain_eq hT hΦ₀m hΦ₀s hΦ₀]
  rfl

end TruncatedBracket

end AutomorphicForm.SlabCovolume

section ShellLimits

open Filter

private theorem tendsto_cpow_sub_cpow_div_nhdsGT_zero_of_re_pos (x₂ : ℝ) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun x₁ : ℝ => ((x₂ : ℂ) ^ w - (x₁ : ℂ) ^ w) / w) (𝓝[>] (0 : ℝ)) (𝓝 ((x₂ : ℂ) ^ w / w)) := by
  have hne : w ≠ 0 := fun h => by simp [h] at hw
  have h0 : Tendsto (fun x₁ : ℝ => (x₁ : ℂ) ^ w) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc := (Complex.continuousAt_ofReal_cpow_const 0 w (Or.inl hw)).tendsto
    rw [Complex.ofReal_zero, Complex.zero_cpow hne] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  simpa using (tendsto_const_nhds.sub h0).div_const w

private theorem tendsto_cpow_sub_cpow_div_atTop_of_re_neg (x₁ : ℝ) {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun x₂ : ℝ => ((x₂ : ℂ) ^ w - (x₁ : ℂ) ^ w) / w) atTop (𝓝 (-(x₁ : ℂ) ^ w / w)) := by
  have h0 : Tendsto (fun x₂ : ℝ => (x₂ : ℂ) ^ w) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_rpow_neg_atTop (neg_pos.mpr hw)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, neg_neg]
  have h := (h0.sub (tendsto_const_nhds (x := (x₁ : ℂ) ^ w))).div_const w
  rwa [zero_sub] at h

private theorem tendsto_exp_cpow_sub_exp_cpow_div_atBot_of_half_lt_re (R' : ℝ) {s : ℂ} (hs : 1 / 2 < s.re) :
    Filter.Tendsto
      (fun R : ℝ =>
        (((Real.exp R' : ℝ) : ℂ) ^ (s - 1 / 2) - ((Real.exp R : ℝ) : ℂ) ^ (s - 1 / 2)) / (s - 1 / 2))
      Filter.atBot (nhds (((Real.exp R' : ℝ) : ℂ) ^ (s - 1 / 2) / (s - 1 / 2))) := by
  have hw : 0 < (s - 1 / 2 : ℂ).re := by
    have : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by simp [Complex.sub_re]
    rw [this]; linarith
  exact (tendsto_cpow_sub_cpow_div_nhdsGT_zero_of_re_pos (Real.exp R') hw).comp Real.tendsto_exp_atBot_nhdsGT

private theorem tendsto_exp_cpow_sub_exp_cpow_div_atTop_of_re_lt_half (R : ℝ) {s : ℂ} (hs : s.re < 1 / 2) :
    Filter.Tendsto
      (fun R' : ℝ =>
        (((Real.exp R' : ℝ) : ℂ) ^ (s - 1 / 2) - ((Real.exp R : ℝ) : ℂ) ^ (s - 1 / 2)) / (s - 1 / 2))
      Filter.atTop (nhds (-(((Real.exp R : ℝ) : ℂ) ^ (s - 1 / 2)) / (s - 1 / 2))) := by
  have hw : (s - 1 / 2 : ℂ).re < 0 := by
    have : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by simp [Complex.sub_re]
    rw [this]; linarith
  exact (tendsto_cpow_sub_cpow_div_atTop_of_re_neg (Real.exp R) hw).comp Real.tendsto_exp_atTop

end ShellLimits

section SmoothnessOfTheTwistedFamily

open FLT.SmoothVectors

variable {F : Type} [Field F] [NumberField F]

private theorem eq_one_of_rpow_eq_one {a r : ℝ} (ha : 0 < a) (hr : r ≠ 0) (h : a ^ r = 1) : a = 1 := by
  have hl := Real.log_rpow ha r
  rw [h, Real.log_one] at hl
  have h0 : Real.log a = 0 := (mul_eq_zero.1 hl.symm).resolve_left hr
  calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
    _ = 1 := by rw [h0, Real.exp_zero]

private theorem exists_re_add_half_ne_zero_and_ne_zero {f : ℂ → ℂ} (hf : Continuous f) {s : ℂ} (hs : f s ≠ 0) :
    ∃ s₁ : ℂ, (s₁ + 1 / 2).re ≠ 0 ∧ f s₁ ≠ 0 := by
  by_cases hre : (s + 1 / 2).re = 0
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hf.continuousAt.eventually_ne hs)
    refine ⟨s + ((ε / 2 : ℝ) : ℂ), ?_, hball ?_⟩
    · rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]
      rw [Complex.add_re] at hre
      intro h
      linarith
    · rw [Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
  · exact ⟨s, hre, hs⟩

private theorem diagonalOne_mem_adelicBorel (t : (AdeleRing (𝓞 F) F)ˣ) :
    (diagOne t : AdelicGL2 (𝓞 F) F) ∈ adelicBorel (𝓞 F) F := by
  show ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
  rw [diagOne_coe_apply]
  exact Matrix.diagonal_apply_ne _ (by decide)

private theorem borelDiagFst_diagonalOne (t : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨diagOne t, diagonalOne_mem_adelicBorel t⟩ : ↥(adelicBorel (𝓞 F) F)) = t := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = (t : AdeleRing (𝓞 F) F)
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq]
  rfl

private theorem borelDiagSnd_diagonalOne (t : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨diagOne t, diagonalOne_mem_adelicBorel t⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
  apply Units.ext
  show ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = 1
  rw [diagOne_coe_apply, Matrix.diagonal_apply_eq]
  rfl

private theorem continuous_diagonalOne :
    Continuous (fun t : (AdeleRing (𝓞 F) F)ˣ => (diagOne t : AdelicGL2 (𝓞 F) F)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · exact Units.continuous_val
    · exact continuous_const
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · exact Units.continuous_coe_inv
    · exact continuous_const

private theorem continuous_generalLinearGroup_det :
    Continuous (fun g : AdelicGL2 (𝓞 F) F => Matrix.GeneralLinearGroup.det g) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_det Units.continuous_val
  · exact Continuous.matrix_det Units.continuous_coe_inv

private theorem fst_det_eq_one_of_mem_finiteAdelicGL2Subgroup {w : AdelicGL2 (𝓞 F) F}
    (hw : w ∈ finiteAdelicGL2Subgroup F) :
    (Matrix.det ((w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).1 = 1 := by
  have hw' : NumberField.AdelicLevel.glArch (𝓞 F) F w = 1 := (mem_finiteAdelicGL2Subgroup_iff F w).1 hw
  have h1 : ((NumberField.AdelicLevel.glArch (𝓞 F) F w : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = 1 := by
    rw [hw']
    rfl
  have h2 := (NumberField.AdelicLevel.adeleArch (𝓞 F) F).map_det
    ((w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
  change NumberField.AdelicLevel.adeleArch (𝓞 F) F
    (Matrix.det ((w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) = 1
  rw [h2]
  change Matrix.det ((NumberField.AdelicLevel.glArch (𝓞 F) F w : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = 1
  rw [h1, Matrix.det_one]

private theorem glArch_diagonalOne_det_eq_one {w : AdelicGL2 (𝓞 F) F} (hw : w ∈ finiteAdelicGL2Subgroup F) :
    NumberField.AdelicLevel.glArch (𝓞 F) F (diagOne (Matrix.GeneralLinearGroup.det w)) = 1 := by
  have hdet := fst_det_eq_one_of_mem_finiteAdelicGL2Subgroup hw
  apply Units.ext
  ext i j
  rw [NumberField.AdelicLevel.glArch_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp <;> first | exact hdet | rfl

private theorem conj_diagonalOne_det_mem (g₀ : AdelicGL2 (𝓞 F) F) {w : AdelicGL2 (𝓞 F) F}
    (hw : w ∈ finiteAdelicGL2Subgroup F) :
    g₀⁻¹ * diagOne (Matrix.GeneralLinearGroup.det w) * g₀ ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_diagonalOne_det_eq_one hw, mul_one,
    inv_mul_cancel]

private def conjDiagonalOneDet (g₀ : AdelicGL2 (𝓞 F) F) :
    ↥(finiteAdelicGL2Subgroup F) →* ↥(finiteAdelicGL2Subgroup F) where
  toFun w := ⟨g₀⁻¹ * diagOne (Matrix.GeneralLinearGroup.det (w : AdelicGL2 (𝓞 F) F)) * g₀,
    conj_diagonalOne_det_mem g₀ w.2⟩
  map_one' := by
    apply Subtype.ext
    simp only [Subgroup.coe_one, map_one, mul_one, inv_mul_cancel]
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul, mul_assoc, mul_inv_cancel_left]

private theorem continuous_conjDiagonalOneDet (g₀ : AdelicGL2 (𝓞 F) F) : Continuous (conjDiagonalOneDet g₀) := by
  show Continuous fun w : ↥(finiteAdelicGL2Subgroup F) =>
    (⟨g₀⁻¹ * diagOne (Matrix.GeneralLinearGroup.det (w : AdelicGL2 (𝓞 F) F)) * g₀,
      conj_diagonalOne_det_mem g₀ w.2⟩ : ↥(finiteAdelicGL2Subgroup F))
  exact ((continuous_const.mul
    (continuous_diagonalOne.comp (continuous_generalLinearGroup_det.comp continuous_subtype_val))).mul
    continuous_const).subtype_mk _

private theorem eq_one_of_etaFst_eq_one (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    {μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) {s : ℂ} (hs : (s + 1 / 2).re ≠ 0)
    {t : (AdeleRing (𝓞 F) F)ˣ} (h : ((etaFst μ α hα s t : ℂˣ) : ℂ) = 1) : μ t = 1 := by
  rw [etaFst_apply, Units.val_mul, cpowChar_apply_val] at h
  have hn := congrArg norm h
  rw [norm_mul, hμ t, one_mul, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos (hα t)] at hn
  have hαt : ((α t : ℝˣ) : ℝ) = 1 := eq_one_of_rpow_eq_one (hα t) hs hn
  rw [hαt, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  exact Units.val_eq_one.1 h

private theorem isKfSmooth_chiDet_inv_of_isInducedSection (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) {μ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ) {s : ℂ}
    (hs : (s + 1 / 2).re ≠ 0) {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) χ₂ ψ)
    (hsm : IsKfSmooth F ψ) {g₀ : AdelicGL2 (𝓞 F) F} (hg₀ : ψ g₀ ≠ 0) : IsKfSmooth F (chiDet (𝓞 F) F μ⁻¹) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup] at hsm ⊢
  obtain ⟨U, hUo, hU⟩ := hsm
  refine ⟨U.comap (conjDiagonalOneDet g₀), ?_, ?_⟩
  · rw [Subgroup.coe_comap]
    exact (continuous_conjDiagonalOneDet g₀).isOpen_preimage _ hUo
  · intro w hw
    rw [Subgroup.mem_comap] at hw
    have h1 : ψ (g₀ * (g₀⁻¹ * diagOne (Matrix.GeneralLinearGroup.det (w : AdelicGL2 (𝓞 F) F)) * g₀)) = ψ g₀ := by
      have := congrFun (congrArg RightTranslationFn.toFun (hU _ hw)) g₀
      first
        | simpa only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] using this
        | (simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at this
           exact this)
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h1
    have h2 := hψ _ (diagonalOne_mem_adelicBorel (Matrix.GeneralLinearGroup.det (w : AdelicGL2 (𝓞 F) F))) g₀
    rw [borelDiagFst_diagonalOne, borelDiagSnd_diagonalOne, map_one, Units.val_one, mul_one, h1] at h2
    have h3 : ((etaFst μ α hα s (Matrix.GeneralLinearGroup.det (w : AdelicGL2 (𝓞 F) F)) : ℂˣ) : ℂ) = 1 :=
      mul_right_cancel₀ hg₀ (by rw [one_mul]; exact h2.symm)
    have h4 : μ (Matrix.GeneralLinearGroup.det (w : AdelicGL2 (𝓞 F) F)) = 1 := eq_one_of_etaFst_eq_one α hα hμ hs h3
    have h5 : chiDet (𝓞 F) F μ⁻¹ (w : AdelicGL2 (𝓞 F) F) = 1 := by
      show ((μ⁻¹ (Matrix.GeneralLinearGroup.det (w : AdelicGL2 (𝓞 F) F)) : ℂˣ) : ℂ) = 1
      rw [MonoidHom.inv_apply, h4, inv_one, Units.val_one]
    rw [Subgroup.smul_def]
    refine RightTranslationFn.ext fun g => ?_
    simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk]
    rw [AutomorphicForm.chiDet_mul, h5, mul_one]

private theorem isKfSmooth_fnTwist_inv_of_family (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ)
    {ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψf s))
    (hψhol : ∀ g, Differentiable ℂ (fun s => ψf s g)) (hψsm : ∀ s, IsKfSmooth F (ψf s)) :
    ∀ s, IsKfSmooth F (fnTwist F μ⁻¹ (ψf s)) := by
  intro s
  by_cases hz : ∀ g, ψf s g = 0
  · rw [funext hz, fnTwist_zero]
    exact isKfSmooth_zero F
  · obtain ⟨g₀, hg₀⟩ := not_forall.1 hz
    obtain ⟨s₁, hs₁, hne⟩ := exists_re_add_half_ne_zero_and_ne_zero (hψhol g₀).continuous hg₀
    exact isKfSmooth_fnTwist F μ⁻¹ (isKfSmooth_chiDet_inv_of_isInducedSection α hα hμ hs₁ (hψf s₁) (hψsm s₁) hne)
      (hψsm s)

end SmoothnessOfTheTwistedFamily

section LowPartResidue

open Filter

variable {F : Type} [Field F] [NumberField F] {a : ℝ} {G : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {r : ℂ}

private theorem setIntegral_eq_sub_mul_setIntegral_series {ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hGser : ∀ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
      G s x = (s - 1 / 2) * (ψ s x + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)))
    {s : ℂ} (hs : 1 / 2 < s.re) (μ : Measure (AdelicGL2 (𝓞 F) F)) (Ω : Set (AdelicGL2 (𝓞 F) F)) :
    ∫ x in Ω, G s x ∂μ =
      (s - 1 / 2) * ∫ x in Ω, (ψ s x + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)) ∂μ := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => hGser s x hs)

private theorem tendsto_setIntegral_add_ofReal_of_forall_norm_le
    (hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (ha : a < 1 / 2) (hG : ∀ g : AdelicGL2 (𝓞 F) F, G (1 / 2) g = r)
    {μ : Measure (AdelicGL2 (𝓞 F) F)} {Ω : Set (AdelicGL2 (𝓞 F) F)} (hΩm : MeasurableSet Ω) (hΩ : μ Ω ≠ ⊤)
    {δ M : ℝ} (hδ : 0 < δ) (hM : ∀ t ∈ Set.Icc (0 : ℝ) δ, ∀ x ∈ Ω, ‖G ((1 / 2 : ℂ) + (t : ℂ)) x‖ ≤ M) :
    Tendsto (fun t : ℝ => ∫ x in Ω, G ((1 / 2 : ℂ) + (t : ℂ)) x ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (((μ Ω).toReal : ℂ) * r)) := by
  have hare : ∀ t : ℝ, 0 ≤ t → a < ((1 / 2 : ℂ) + (t : ℂ)).re := by
    intro t ht
    have h : a < 1 / 2 + t := by linarith
    simp only [Complex.add_re, Complex.ofReal_re]
    norm_num [h]
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := eventually_nhdsWithin_of_forall fun t ht => ht
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < δ := eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)
  refine tendsto_setIntegral_add_ofReal_of_norm_le_of_tendsto_const (M := M) hΩm hΩ ?_ ?_ ?_ fun x _ => hG x
  · filter_upwards [hpos] with t ht
    exact aestronglyMeasurable_of_continuousOn_lt_re_prod_univ hGc (hare t ht.le) _
  · filter_upwards [hpos, hlt] with t ht htδ
    exact hM t ⟨ht.le, htδ.le⟩
  · exact fun x _ => tendsto_add_ofReal_of_continuousOn_lt_re_prod_univ hGc ha x

private theorem tendsto_sub_mul_setIntegral_series_add_ofReal {ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hGser : ∀ (s : ℂ) (x : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
      G s x = (s - 1 / 2) * (ψ s x + ∑' ξ : F, ψ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)))
    (hGc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2) ({s : ℂ | a < s.re} ×ˢ Set.univ))
    (ha : a < 1 / 2) (hG : ∀ g : AdelicGL2 (𝓞 F) F, G (1 / 2) g = r)
    {μ : Measure (AdelicGL2 (𝓞 F) F)} {Ω : Set (AdelicGL2 (𝓞 F) F)} (hΩm : MeasurableSet Ω) (hΩ : μ Ω ≠ ⊤)
    {δ M : ℝ} (hδ : 0 < δ) (hM : ∀ t ∈ Set.Icc (0 : ℝ) δ, ∀ x ∈ Ω, ‖G ((1 / 2 : ℂ) + (t : ℂ)) x‖ ≤ M) :
    Tendsto (fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) *
        ∫ x in Ω, (ψ ((1 / 2 : ℂ) + (t : ℂ)) x + ∑' ξ : F, ψ ((1 / 2 : ℂ) + (t : ℂ))
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (((μ Ω).toReal : ℂ) * r)) := by
  have hre : ∀ t : ℝ, 0 < t → 1 / 2 < ((1 / 2 : ℂ) + (t : ℂ)).re := by
    intro t ht
    simp only [Complex.add_re, Complex.ofReal_re]
    norm_num [ht]
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := eventually_nhdsWithin_of_forall fun t ht => ht
  have heq : (fun t : ℝ => ∫ x in Ω, G ((1 / 2 : ℂ) + (t : ℂ)) x ∂μ) =ᶠ[𝓝[>] (0 : ℝ)]
      fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) *
        ∫ x in Ω, (ψ ((1 / 2 : ℂ) + (t : ℂ)) x + ∑' ξ : F, ψ ((1 / 2 : ℂ) + (t : ℂ))
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)) ∂μ := by
    filter_upwards [hpos] with t ht
    exact setIntegral_eq_sub_mul_setIntegral_series hGser (hre t ht) μ Ω
  exact (tendsto_setIntegral_add_ofReal_of_forall_norm_le hGc ha hG hΩm hΩ hδ hM).congr' heq

private theorem tendsto_integral_maximalCompact_add_ofReal {ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2)) :
    Tendsto (fun t : ℝ => ∫ k, ψ ((1 / 2 : ℂ) + (t : ℂ)) (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ k, ψ (1 / 2 : ℂ) (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F))) := by
  have hray : Tendsto (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2 : ℂ)) := by
    have h : Continuous (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) := continuous_const.add Complex.continuous_ofReal
    have h0 := h.tendsto (0 : ℝ)
    simp only [Complex.ofReal_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds

  have hK : IsCompact (Metric.closedBall (1 / 2 : ℂ) 1 ×ˢ (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F))) :=
    (isCompact_closedBall _ _).prod (isCompact_adelicMaximalCompact F)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hψjc.continuousOn
  have hcont : ContinuousAt (fun s : ℂ => ∫ k, ψ s (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F))
      (1 / 2 : ℂ) := by
    refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
    · exact Filter.Eventually.of_forall fun s =>
        (hψjc.comp (continuous_const.prodMk continuous_subtype_val)).aestronglyMeasurable
    · refine Filter.eventually_of_mem (Metric.closedBall_mem_nhds (1 / 2 : ℂ) one_pos) fun s hs => ?_
      exact Filter.Eventually.of_forall fun k =>
        hM (s, (k : AdelicGL2 (𝓞 F) F)) ⟨hs, SetLike.mem_coe.2 k.2⟩
    · exact Filter.Eventually.of_forall fun k =>
        (hψjc.comp (continuous_id.prodMk continuous_const)).continuousAt
  have h2 : Tendsto (fun s : ℂ => ∫ k, ψ s (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) (𝓝 (1 / 2 : ℂ))
      (𝓝 (∫ k, ψ (1 / 2 : ℂ) (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F))) := hcont
  exact h2.comp hray

end LowPartResidue

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.AdelicLevel AutomorphicForm.WindowedSiegel"

section LowPartBound

variable {F : Type} [Field F] [NumberField F]

private theorem exists_forall_adelicHeight_mul_le (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (a : AdelicGL2 (𝓞 F) F) :
    ∃ D : ℝ, 0 < D ∧ ∀ y : AdelicGL2 (𝓞 F) F, adelicHeight F (y * a) ≤ D * adelicHeight F y := by
  obtain ⟨D, hD⟩ := (isCompact_adelicMaximalCompact F).bddAbove_image
    (f := fun k : AdelicGL2 (𝓞 F) F => adelicHeight F (k * a))
    ((NumberField.AdelicHeight.continuous_adelicHeight F).comp (continuous_id.mul continuous_const)).continuousOn
  have hD' : ∀ k ∈ adelicMaximalCompact F, adelicHeight F (k * a) ≤ D := fun k hk => hD ⟨k, hk, rfl⟩
  refine ⟨D, lt_of_lt_of_le (adelicHeight_pos (1 * a)) (hD' 1 (one_mem _)), fun y => ?_⟩
  obtain ⟨b, k, hb, hfin, hrow, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F y
  have hk : k ∈ adelicMaximalCompact F := mem_adelicMaximalCompact_iff.mpr ⟨hfin, hrow⟩
  have hmul3 : adelicHeight F (b * k * a) = adelicHeight F (b * k) * adelicHeight F (k * a) := by
    rw [mul_assoc, adelicHeight_borel_mul hα hb (k * a), adelicHeight_borel_mul hα hb k,
      adelicHeight_eq_one_of_mem_adelicMaximalCompact hk, mul_one]
  rw [hmul3, mul_comm D]
  exact mul_le_mul_of_nonneg_left (hD' k hk) (adelicHeight_pos _).le

private theorem exists_forall_norm_le_of_mem_lowPart (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ)) {c u e₁ e₂ : ℝ}
    (hc : 0 ≤ c) {tset : Finset (AdelicGL2 (𝓞 F) F)} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hcov : Φ₀ ⊆ ⋃ t ∈ tset, (· * t) '' centreCutSiegelSet F c u e₁ e₂) {T : ℝ}
    (G : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (C : Set ℂ)
    (hbound : ∀ t : AdelicGL2 (𝓞 F) F, ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C,
      ∀ g ∈ integralWindowedSiegelSet F (c ^ ∑ w : InfinitePlace F, w.mult) u,
        ‖G s (g * t)‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N) :
    ∃ B : ℝ, ∀ s ∈ C, ∀ x ∈ lowPart F T Φ₀, ‖G s x‖ ≤ B := by
  have per : ∀ t : AdelicGL2 (𝓞 F) F, ∃ Bt : ℝ, ∀ s ∈ C, ∀ x ∈ lowPart F T Φ₀,
      ∀ g ∈ centreCutSiegelSet F c u e₁ e₂, x = g * t → ‖G s x‖ ≤ Bt := by
    intro t
    obtain ⟨M, N, hMN⟩ := hbound t
    obtain ⟨D, hD0, hD⟩ := exists_forall_adelicHeight_mul_le hα t⁻¹
    refine ⟨|M| * (1 + D * T) ^ N, fun s hs x hx g hg hxg => ?_⟩
    have hgI := centreCutSiegelSet_subset_integralWindowedSiegelSet hc hg
    have h0 : 0 ≤ archHeight F (glArch (𝓞 F) F g) := (archHeight_pos _ _).le
    have hh : archHeight F (glArch (𝓞 F) F g) ≤ D * T := by
      rw [← adelicHeight_eq_archHeight_of_mem hgI.1]
      have hx0 : adelicHeight F x ≤ T := by
        simpa [bruhatRep] using adelicHeight_bruhatRep_mul_le_of_mem_lowPart hx none
      calc adelicHeight F g = adelicHeight F (x * t⁻¹) := by rw [hxg, mul_inv_cancel_right]
        _ ≤ D * adelicHeight F x := hD x
        _ ≤ D * T := mul_le_mul_of_nonneg_left hx0 hD0.le
    calc ‖G s x‖ = ‖G s (g * t)‖ := by rw [hxg]
      _ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N := hMN s hs g hgI
      _ ≤ |M| * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self M) (pow_nonneg (by linarith) N)
      _ ≤ |M| * (1 + D * T) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) N) (abs_nonneg M)
  choose Bt hBt using per
  refine ⟨∑ t ∈ tset, |Bt t|, fun s hs x hx => ?_⟩
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp (hcov (lowPart_subset T Φ₀ hx))
  obtain ⟨g, hg, hgx⟩ := hxt
  calc ‖G s x‖ ≤ Bt t := hBt t s hs x hx g hg hgx.symm
    _ ≤ |Bt t| := le_abs_self _
    _ ≤ ∑ t' ∈ tset, |Bt t'| := Finset.single_le_sum (f := fun t' => |Bt t'|) (fun _ _ => abs_nonneg _) ht

end LowPartBound

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section PrincipalTiling

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem countable_numberField : Countable F :=
  Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective

private def principalAdeleEquiv : F ≃ AdeleRing.principalSubgroup (𝓞 F) F :=
  Equiv.ofBijective (fun k => ⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩)
    ⟨fun a b h => NumberField.AdeleRing.algebraMap_injective (𝓞 F) F (congrArg Subtype.val h),
     by rintro ⟨_, k, rfl⟩; exact ⟨k, rfl⟩⟩

private theorem tsum_setLIntegral_adelicBox_comp_algebraMap_add (f : AdeleRing (𝓞 F) F → ℝ≥0∞) :
    ∑' ξ : F, ∫⁻ u in adelicBox F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ + u) ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ u, f u ∂(adelicAddHaar (𝓞 F) F) := by
  haveI : Countable F := countable_numberField
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) :=
    (principalAdeleEquiv (F := F)).symm.injective.countable
  have hFD := isAddFundamentalDomain_adelicBox_adelicAddHaar F
  rw [hFD.lintegral_eq_tsum'' f, ← (principalAdeleEquiv (F := F)).tsum_eq]
  exact tsum_congr fun ξ => rfl

private theorem tsum_setLIntegral_adelicBox_enorm_comp_algebraMap_add (G : AdeleRing (𝓞 F) F → ℂ) :
    ∑' ξ : F, ∫⁻ u in adelicBox F, ‖G (algebraMap F (AdeleRing (𝓞 F) F) ξ + u)‖ₑ ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ u, ‖G u‖ₑ ∂(adelicAddHaar (𝓞 F) F) :=
  tsum_setLIntegral_adelicBox_comp_algebraMap_add fun u => ‖G u‖ₑ

private theorem tsum_setLIntegral_adelicBox_enorm_lt_top (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : Integrable G (adelicAddHaar (𝓞 F) F)) :
    ∑' ξ : F, ∫⁻ u in adelicBox F, ‖G (algebraMap F (AdeleRing (𝓞 F) F) ξ + u)‖ₑ ∂(adelicAddHaar (𝓞 F) F) < ∞ := by
  rw [tsum_setLIntegral_adelicBox_enorm_comp_algebraMap_add]
  exact hG.hasFiniteIntegral

end PrincipalTiling

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section BigCellAlgebra

variable {F : Type} [Field F]

private theorem val_zero_zero_ne_zero_of_mem_borelSubgroup {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) :
    γ.val 0 0 ≠ 0 ∧ γ.val 1 1 ≠ 0 := by
  have h10 : γ.val 1 0 = 0 := hγ
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero γ
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

private theorem exists_mem_borelSubgroup_gl2Weyl_mul_unipotentGL2_mul_eq {γ : GL (Fin 2) F}
    (hγ : γ ∈ borelSubgroup F) (ξ : F) :
    ∃ δ ∈ borelSubgroup F, gl2Weyl * unipotentGL2 ξ * γ =
      δ * (gl2Weyl * unipotentGL2 ((γ.val 0 1 + ξ * γ.val 1 1) / γ.val 0 0)) := by
  refine ⟨gl2Weyl * unipotentGL2 ξ * γ * (gl2Weyl * unipotentGL2 ((γ.val 0 1 + ξ * γ.val 1 1) / γ.val 0 0))⁻¹,
    ?_, by rw [inv_mul_cancel_right]⟩
  have h10 : γ.val 1 0 = 0 := hγ
  have h00 := (val_zero_zero_ne_zero_of_mem_borelSubgroup hγ).1
  have hinv : ∀ η : F, (unipotentGL2 η)⁻¹ = unipotentGL2 (-η) := fun η =>
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  rw [mem_borelSubgroup_iff, mul_inv_rev, gl2Weyl_inv, hinv]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [h10]
  field_simp
  ring

private def bigCellReindex (a b d : F) (ha : a ≠ 0) (hd : d ≠ 0) : F ≃ F where
  toFun ξ := (b + ξ * d) / a
  invFun η := (η * a - b) / d
  left_inv ξ := by
    show ((b + ξ * d) / a * a - b) / d = ξ
    rw [div_mul_cancel₀ _ ha, add_sub_cancel_left, mul_div_cancel_right₀ _ hd]
  right_inv η := by
    show (b + (η * a - b) / d * d) / a = η
    rw [div_mul_cancel₀ _ hd, add_comm, sub_add_cancel, mul_div_cancel_right₀ _ ha]

private theorem bigCellReindex_apply (a b d : F) (ha : a ≠ 0) (hd : d ≠ 0) (ξ : F) :
    bigCellReindex a b d ha hd ξ = (b + ξ * d) / a :=
  rfl

end BigCellAlgebra

section BigCellBorel

variable {F : Type} [Field F] [NumberField F]

private theorem globalPoints_unipotentGL2_eq (ξ : F) :
    globalPoints (𝓞 F) F (unipotentGL2 ξ) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply (𝓞 F) F (unipotentGL2 ξ) i j, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem globalPoints_gl2Weyl_mul_unipotentGL2_eq (ξ : F) :
    globalPoints (𝓞 F) F (gl2Weyl * unipotentGL2 ξ) =
      adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  rw [map_mul, globalPoints_unipotentGL2_eq]
  rfl

private theorem tsum_apply_adelicWeyl_mul_unipotentGL2_mul_globalPoints_mul (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ γ ∈ borelSubgroup F, ∀ g, φ (globalPoints (𝓞 F) F γ * g) = φ g)
    {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) *
        (globalPoints (𝓞 F) F γ * g))) =
      ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) := by
  obtain ⟨h00, h11⟩ := val_zero_zero_ne_zero_of_mem_borelSubgroup hγ
  have hsummand : ∀ ξ : F,
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (globalPoints (𝓞 F) F γ * g)) =
        φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F)
          (bigCellReindex (γ.val 0 0) (γ.val 0 1) (γ.val 1 1) h00 h11 ξ)) * g) := by
    intro ξ
    obtain ⟨δ, hδ, hfac⟩ := exists_mem_borelSubgroup_gl2Weyl_mul_unipotentGL2_mul_eq hγ ξ
    have h : adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * globalPoints (𝓞 F) F γ =
        globalPoints (𝓞 F) F δ * (adelicWeyl (𝓞 F) F *
          unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ((γ.val 0 1 + ξ * γ.val 1 1) / γ.val 0 0))) := by
      rw [← globalPoints_gl2Weyl_mul_unipotentGL2_eq, ← globalPoints_gl2Weyl_mul_unipotentGL2_eq, ← map_mul,
        ← map_mul, hfac]
    rw [bigCellReindex_apply, ← mul_assoc, h, mul_assoc]
    exact hφ δ hδ _
  calc (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) *
          (globalPoints (𝓞 F) F γ * g)))
      = ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F)
          (bigCellReindex (γ.val 0 0) (γ.val 0 1) (γ.val 1 1) h00 h11 ξ)) * g) := tsum_congr hsummand
    _ = ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) :=
        (bigCellReindex (γ.val 0 0) (γ.val 0 1) (γ.val 1 1) h00 h11).tsum_eq fun ξ =>
          φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)

private theorem add_tsum_apply_adelicWeyl_mul_unipotentGL2_mul_globalPoints_mul (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ γ ∈ borelSubgroup F, ∀ g, φ (globalPoints (𝓞 F) F γ * g) = φ g)
    {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    φ (globalPoints (𝓞 F) F γ * g) +
        (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) *
          (globalPoints (𝓞 F) F γ * g))) =
      φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) := by
  rw [hφ γ hγ g, tsum_apply_adelicWeyl_mul_unipotentGL2_mul_globalPoints_mul φ hφ hγ g]

end BigCellBorel

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section SheetUnfolding

open scoped Pointwise
variable {G : Type*} [Group G] {H : Subgroup G}

private theorem measurable_tsum_ennreal {α ι : Type*} [MeasurableSpace α] [Countable ι] {f : ι → α → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun t => Finset.measurable_sum t fun i _ => hf i

private theorem measurableMul_subgroup [MeasurableSpace G] [MeasurableMul₂ G] (H : Subgroup G) : MeasurableMul H where
  measurable_const_mul _ := (measurable_const.mul measurable_subtype_coe).subtype_mk
  measurable_mul_const _ := (measurable_subtype_coe.mul measurable_const).subtype_mk

private theorem ae_measure_preimage_mul_out_eq_zero [MeasurableSpace G] [MeasurableMul₂ G] (μ : Measure G)
    (μH : Measure H) [SFinite μH]
    [μH.IsMulRightInvariant] (ν : Measure (MulAction.orbitRel.Quotient H G))
    (hQ : ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μ = ∫⁻ q, ∫⁻ x : H, φ ((x : G) * q.out) ∂μH ∂ν)
    {E : Set G} (hE : MeasurableSet E) (hE0 : μ E = 0) :
    ∀ᵐ q ∂ν, μH {x : H | (x : G) * q.out ∈ E} = 0 := by
  letI : MeasurableMul H := measurableMul_subgroup H
  have hmul : Measurable fun p : G × H => ((p.2 : G) * p.1) :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hK₀_int : ∀ z : G,
      μH {x : H | (x : G) * z ∈ E} = ∫⁻ x : H, E.indicator (1 : G → ℝ≥0∞) ((x : G) * z) ∂μH := by
    intro z
    have hpre : MeasurableSet {x : H | (x : G) * z ∈ E} :=
      hE.preimage (measurable_subtype_coe.mul_const z)
    rw [← lintegral_indicator_one hpre]
    rfl
  have hK₀ : Measurable fun z : G => μH {x : H | (x : G) * z ∈ E} := by
    have hF : Measurable fun p : G × H => E.indicator (1 : G → ℝ≥0∞) ((p.2 : G) * p.1) :=
      (measurable_const.indicator hE).comp hmul
    have hfun : (fun z : G => μH {x : H | (x : G) * z ∈ E})
        = fun z : G => ∫⁻ x : H, E.indicator (1 : G → ℝ≥0∞) ((x : G) * z) ∂μH := funext hK₀_int
    rw [hfun]
    exact hF.lintegral_prod_right' (ν := μH)
  have hK₀_inv : ∀ (h : H) (z : G),
      μH {x : H | (x : G) * ((h : G) * z) ∈ E} = μH {x : H | (x : G) * z ∈ E} := by
    intro h z
    have hset : {x : H | (x : G) * ((h : G) * z) ∈ E}
        = (fun x : H => x * h) ⁻¹' {x : H | (x : G) * z ∈ E} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Subgroup.coe_mul, mul_assoc]
    rw [hset, measure_preimage_mul_right]
  have hK_mk : ∀ z : G,
      μH {x : H | (x : G) * (Quotient.mk'' z : MulAction.orbitRel.Quotient H G).out ∈ E}
        = μH {x : H | (x : G) * z ∈ E} := by
    intro z
    have hz : (Quotient.mk'' z : MulAction.orbitRel.Quotient H G).out ∈ MulAction.orbit H z := by
      rw [← MulAction.orbitRel.Quotient.orbit_mk]
      exact MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' _)
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hz
    rw [← hh, Subgroup.smul_def, smul_eq_mul, hK₀_inv]
  have hK : Measurable fun q : MulAction.orbitRel.Quotient H G => μH {x : H | (x : G) * q.out ∈ E} := by
    rw [measurable_from_quotient]
    have hcomp : ((fun q : MulAction.orbitRel.Quotient H G => μH {x : H | (x : G) * q.out ∈ E})
        ∘ Quotient.mk'') = fun z : G => μH {x : H | (x : G) * z ∈ E} := funext hK_mk
    rw [hcomp]
    exact hK₀
  have hint : ∫⁻ q, μH {x : H | (x : G) * q.out ∈ E} ∂ν = 0 := by
    have h1 := hQ (E.indicator (1 : G → ℝ≥0∞)) (measurable_const.indicator hE)
    rw [lintegral_indicator_one hE, hE0] at h1
    calc ∫⁻ q, μH {x : H | (x : G) * q.out ∈ E} ∂ν
        = ∫⁻ q, ∫⁻ x : H, E.indicator (1 : G → ℝ≥0∞) ((x : G) * q.out) ∂μH ∂ν :=
          lintegral_congr fun q => hK₀_int q.out
      _ = 0 := h1.symm
  have := (lintegral_eq_zero_iff hK).mp hint
  filter_upwards [this] with q hq
  exact hq

private theorem indicator_apply_inv_mul {B : Subgroup G} {𝓕 : Set G} {f : G → ℝ≥0∞}
    (hfB : ∀ (b : B) (g : G), f ((b : G) * g) = f g) (b : B) (z : G) :
    𝓕.indicator f ((b : G)⁻¹ * z) = (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) z * f z := by
  have hiff : (b : G)⁻¹ * z ∈ 𝓕 ↔ z ∈ b • 𝓕 := by
    rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, Subgroup.coe_inv, smul_eq_mul]
  have hfz : f ((b : G)⁻¹ * z) = f z := by
    have := hfB b⁻¹ z
    rwa [Subgroup.coe_inv] at this
  by_cases hz : z ∈ b • 𝓕
  · rw [Set.indicator_of_mem (hiff.mpr hz), Set.indicator_of_mem hz, one_mul, hfz]
  · rw [Set.indicator_of_notMem (fun h => hz (hiff.mp h)), Set.indicator_of_notMem hz, zero_mul]

private theorem tsum_indicator_smul_ae_eq_indicator
    [MeasurableSpace G] (μ : Measure G) [SigmaFinite μ] (B : Subgroup G)
    [Countable B]
    [MeasurableConstSMul B G] {S : Set G} (hS : MeasurableSet S)
    (hSB : ∀ (b : B) (g : G), (b : G) * g ∈ S ↔ g ∈ S) {𝓕 : Set G} (h𝓕m : MeasurableSet 𝓕) (h𝓕S : 𝓕 ⊆ S)
    [SMulInvariantMeasure B G (μ.restrict S)] (h𝓕 : IsFundamentalDomain B 𝓕 (μ.restrict S)) :
    ∀ᵐ z ∂μ, (∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) z) = S.indicator (fun _ => (1 : ℝ≥0∞)) z := by
  have hsm : ∀ b : B, MeasurableSet (b • 𝓕) := fun b => h𝓕m.const_smul b
  have hc : Measurable fun z : G => ∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) z :=
    measurable_tsum_ennreal fun b => measurable_const.indicator (hsm b)
  have hc_off : ∀ z, z ∉ S → (∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) z) = 0 := by
    intro z hz
    refine ENNReal.tsum_eq_zero.mpr fun b => Set.indicator_of_notMem ?_ _
    rintro ⟨w, hw, rfl⟩
    exact hz ((hSB b w).mpr (h𝓕S hw))
  have hc_on : ∀ᵐ z ∂(μ.restrict S), (∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) z) = 1 := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hc measurable_const fun E hE _ => ?_
    rw [setLIntegral_one, lintegral_tsum fun b => (measurable_const.indicator (hsm b)).aemeasurable,
      h𝓕.measure_eq_tsum' E]
    refine tsum_congr fun b => ?_
    rw [lintegral_indicator_const (hsm b), one_mul, Measure.restrict_apply (hsm b), Set.inter_comm]
  have h1 := (ae_restrict_iff' hS).mp hc_on
  filter_upwards [h1] with z hz
  by_cases hzS : z ∈ S
  · rw [Set.indicator_of_mem hzS]
    exact hz hzS
  · rw [Set.indicator_of_notMem hzS]
    exact hc_off z hzS

private theorem lintegral_indicator_mul_eq_indicator_mul_setLIntegral
    [MeasurableSpace G] [MeasurableMul₂ G] (μH : Measure H)
    (B : Subgroup G) (hBH : B ≤ H)
    [Countable B] [MeasurableConstSMul B G] [MeasurableConstSMul (B.subgroupOf H) H]
    [SMulInvariantMeasure (B.subgroupOf H) H μH] {T : Set H} (hT : IsFundamentalDomain (B.subgroupOf H) T μH)
    {S : Set G} (hSH : ∀ (x : H) (g : G), (x : G) * g ∈ S ↔ g ∈ S) {𝓕 : Set G} (h𝓕m : MeasurableSet 𝓕)
    {f : G → ℝ≥0∞} (hf : Measurable f) (hfB : ∀ (b : B) (g : G), f ((b : G) * g) = f g) (y : G)
    (hy : μH {x : H | (x : G) * y ∈
      {z : G | (∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) z) ≠ S.indicator (fun _ => (1 : ℝ≥0∞)) z}} = 0) :
    ∫⁻ x : H, 𝓕.indicator f ((x : G) * y) ∂μH
      = S.indicator (fun _ => (1 : ℝ≥0∞)) y * ∫⁻ x in T, f ((x : G) * y) ∂μH := by
  have hxy : Measurable fun x : H => (x : G) * y := measurable_subtype_coe.mul_const y
  have hsm : ∀ b : B, MeasurableSet (b • 𝓕) := fun b => h𝓕m.const_smul b
  set e := Subgroup.subgroupOfEquivOfLe hBH with he_def
  haveI : Countable (B.subgroupOf H) := e.toEquiv.injective.countable
  have hmeas : ∀ b : B, Measurable fun x : H =>
      (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * y) * f ((x : G) * y) :=
    fun b => ((measurable_const.indicator (hsm b)).comp hxy).mul (hf.comp hxy)
  have hterm : ∀ (k : B.subgroupOf H) (x : H),
      𝓕.indicator f (((k⁻¹ • x : H) : G) * y)
        = ((e k) • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * y) * f ((x : G) * y) := by
    intro k x
    have hk : (((k⁻¹ • x : H)) : G) = ((e k : B) : G)⁻¹ * (x : G) := by
      rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]
      simp [he_def]
    rw [← indicator_apply_inv_mul hfB, hk, mul_assoc]
  calc ∫⁻ x : H, 𝓕.indicator f ((x : G) * y) ∂μH
      = ∑' k : B.subgroupOf H, ∫⁻ x in T, 𝓕.indicator f (((k⁻¹ • x : H) : G) * y) ∂μH :=
        hT.lintegral_eq_tsum' _
    _ = ∑' k : B.subgroupOf H,
          ∫⁻ x in T, ((e k) • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * y) * f ((x : G) * y) ∂μH := by
        refine tsum_congr fun k => lintegral_congr fun x => ?_
        exact hterm k x
    _ = ∑' b : B, ∫⁻ x in T, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * y) * f ((x : G) * y) ∂μH :=
        e.toEquiv.tsum_eq fun b : B =>
          ∫⁻ x in T, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * y) * f ((x : G) * y) ∂μH
    _ = ∫⁻ x in T, (∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * y)) * f ((x : G) * y) ∂μH := by
        rw [← lintegral_tsum fun b => (hmeas b).aemeasurable]
        refine lintegral_congr fun x => ?_
        exact ENNReal.tsum_mul_right
    _ = ∫⁻ x in T, S.indicator (fun _ => (1 : ℝ≥0∞)) y * f ((x : G) * y) ∂μH := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        have hae := compl_mem_ae_iff.mpr hy
        filter_upwards [hae] with x hx
        have hx' : (∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * y))
            = S.indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * y) := not_not.mp hx
        rw [hx']
        congr 1
        by_cases hyS : y ∈ S
        · rw [Set.indicator_of_mem hyS, Set.indicator_of_mem ((hSH x y).mpr hyS)]
        · rw [Set.indicator_of_notMem hyS, Set.indicator_of_notMem (fun h => hyS ((hSH x y).mp h))]
    _ = S.indicator (fun _ => (1 : ℝ≥0∞)) y * ∫⁻ x in T, f ((x : G) * y) ∂μH :=
        lintegral_const_mul _ (hf.comp hxy)

private theorem setLIntegral_eq_lintegral_indicator_mul_setLIntegral_sheet [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SigmaFinite μ]
    (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant] (ν : Measure (MulAction.orbitRel.Quotient H G))
    (hQ : ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μ = ∫⁻ q, ∫⁻ x : H, φ ((x : G) * q.out) ∂μH ∂ν)
    (B : Subgroup G) (hBH : B ≤ H) [Countable B] [MeasurableConstSMul B G]
    [MeasurableConstSMul (B.subgroupOf H) H] [SMulInvariantMeasure (B.subgroupOf H) H μH]
    {T : Set H} (hT : IsFundamentalDomain (B.subgroupOf H) T μH)
    {S : Set G} (hS : MeasurableSet S) (hSH : ∀ (x : H) (g : G), (x : G) * g ∈ S ↔ g ∈ S)
    [SMulInvariantMeasure B G (μ.restrict S)]
    {𝓕 : Set G} (h𝓕m : MeasurableSet 𝓕) (h𝓕S : 𝓕 ⊆ S) (h𝓕 : IsFundamentalDomain B 𝓕 (μ.restrict S))
    {f : G → ℝ≥0∞} (hf : Measurable f) (hfB : ∀ (b : B) (g : G), f ((b : G) * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂μ
      = ∫⁻ q, S.indicator (fun _ => (1 : ℝ≥0∞)) q.out * ∫⁻ x in T, f ((x : G) * q.out) ∂μH ∂ν := by
  have hSB : ∀ (b : B) (g : G), (b : G) * g ∈ S ↔ g ∈ S := fun b g => hSH ⟨b, hBH b.2⟩ g
  have hc_ae := tsum_indicator_smul_ae_eq_indicator μ B hS hSB h𝓕m h𝓕S h𝓕
  have hsm : ∀ b : B, MeasurableSet (b • 𝓕) := fun b => h𝓕m.const_smul b
  have hc : Measurable fun z : G => ∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) z :=
    measurable_tsum_ennreal fun b => measurable_const.indicator (hsm b)
  have hEm : MeasurableSet {z : G |
      (∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) z) ≠ S.indicator (fun _ => (1 : ℝ≥0∞)) z} :=
    (measurableSet_eq_fun hc (measurable_const.indicator hS)).compl
  have hE0 : μ {z : G |
      (∑' b : B, (b • 𝓕).indicator (fun _ => (1 : ℝ≥0∞)) z) ≠ S.indicator (fun _ => (1 : ℝ≥0∞)) z} = 0 :=
    ae_iff.mp hc_ae
  have htr := ae_measure_preimage_mul_out_eq_zero μ μH ν hQ hEm hE0
  calc ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g, 𝓕.indicator f g ∂μ := (lintegral_indicator h𝓕m f).symm
    _ = ∫⁻ q, ∫⁻ x : H, 𝓕.indicator f ((x : G) * q.out) ∂μH ∂ν := hQ _ (hf.indicator h𝓕m)
    _ = ∫⁻ q, S.indicator (fun _ => (1 : ℝ≥0∞)) q.out * ∫⁻ x in T, f ((x : G) * q.out) ∂μH ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [htr] with q hq
        exact lintegral_indicator_mul_eq_indicator_mul_setLIntegral μH B hBH hT hSH h𝓕m hf hfB q.out hq

private theorem setLIntegral_eq_lintegral_indicator_mul_lintegral_comp [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SigmaFinite μ] (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]
    (ν : Measure (MulAction.orbitRel.Quotient H G))
    (hQ : ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μ = ∫⁻ q, ∫⁻ x : H, φ ((x : G) * q.out) ∂μH ∂ν)
    (B : Subgroup G) (hBH : B ≤ H) [Countable B] [MeasurableConstSMul B G]
    [MeasurableConstSMul (B.subgroupOf H) H] [SMulInvariantMeasure (B.subgroupOf H) H μH]
    {T : Set H} (hT : IsFundamentalDomain (B.subgroupOf H) T μH)
    {S : Set G} (hS : MeasurableSet S) (hSH : ∀ (x : H) (g : G), (x : G) * g ∈ S ↔ g ∈ S)
    [SMulInvariantMeasure B G (μ.restrict S)]
    {𝓕 : Set G} (h𝓕m : MeasurableSet 𝓕) (h𝓕S : 𝓕 ⊆ S) (h𝓕 : IsFundamentalDomain B 𝓕 (μ.restrict S))
    {A : Type*} [MeasurableSpace A] (ρ : Measure A) (e : A → H)
    (hρ : ∀ F : H → ℝ≥0∞, Measurable F → ∫⁻ x in T, F x ∂μH = ∫⁻ a, F (e a) ∂ρ)
    {f : G → ℝ≥0∞} (hf : Measurable f) (hfB : ∀ (b : B) (g : G), f ((b : G) * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂μ
      = ∫⁻ q, S.indicator (fun _ => (1 : ℝ≥0∞)) q.out * ∫⁻ a, f ((e a : G) * q.out) ∂ρ ∂ν := by
  rw [setLIntegral_eq_lintegral_indicator_mul_setLIntegral_sheet μ μH ν hQ B hBH hT hS hSH h𝓕m h𝓕S h𝓕 hf hfB]
  refine lintegral_congr fun q => ?_
  rw [show (∫⁻ x in T, f ((x : G) * q.out) ∂μH) = ∫⁻ a, f ((e a : G) * q.out) ∂ρ from
    hρ _ (hf.comp (measurable_subtype_coe.mul_const _))]

private theorem smulInvariantMeasure_restrict
    [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (B : Subgroup G)
    [MeasurableConstSMul B G] {S : Set G} (hSB : ∀ (b : B) (g : G), (b : G) * g ∈ S ↔ g ∈ S) :
    SMulInvariantMeasure B G (μ.restrict S) where
  measure_preimage_smul b {E} hE := by
    have hpre : (fun g : G => b • g) ⁻¹' S = S := by
      ext g
      simp only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul]
      exact hSB b g
    rw [Measure.restrict_apply hE, Measure.restrict_apply (hE.preimage (measurable_const_smul b))]
    calc μ ((fun g : G => b • g) ⁻¹' E ∩ S) = μ ((fun g : G => b • g) ⁻¹' (E ∩ S)) := by
          rw [Set.preimage_inter, hpre]
      _ = μ (E ∩ S) := by
          simpa [Subgroup.smul_def] using measure_preimage_mul μ (b : G) (E ∩ S)

private theorem setIntegral_eq_zero_of_forall_setIntegral_sheet_eq_zero_real [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SigmaFinite μ] (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]
    (ν : Measure (MulAction.orbitRel.Quotient H G))
    (hQ : ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μ = ∫⁻ q, ∫⁻ x : H, φ ((x : G) * q.out) ∂μH ∂ν)
    (B : Subgroup G) (hBH : B ≤ H) [Countable B] [MeasurableConstSMul B G]
    [MeasurableConstSMul (B.subgroupOf H) H] [SMulInvariantMeasure (B.subgroupOf H) H μH]
    {T : Set H} (hT : IsFundamentalDomain (B.subgroupOf H) T μH)
    {S : Set G} (hS : MeasurableSet S) (hSH : ∀ (x : H) (g : G), (x : G) * g ∈ S ↔ g ∈ S)
    [SMulInvariantMeasure B G (μ.restrict S)]
    {𝓕 : Set G} (h𝓕m : MeasurableSet 𝓕) (h𝓕S : 𝓕 ⊆ S) (h𝓕 : IsFundamentalDomain B 𝓕 (μ.restrict S))
    {A : Type*} [MeasurableSpace A] (ρ : Measure A) (e : A → H)
    (hρ : ∀ F : H → ℝ≥0∞, Measurable F → ∫⁻ x in T, F x ∂μH = ∫⁻ a, F (e a) ∂ρ)
    {r : G → ℝ} (hr : Measurable r) (hrB : ∀ (b : B) (g : G), r ((b : G) * g) = r g) (hri : IntegrableOn r 𝓕 μ)
    (hz : ∀ y ∈ S, Integrable (fun a : A => r ((e a : G) * y)) ρ ∧ ∫ a, r ((e a : G) * y) ∂ρ = 0) :
    ∫ g in 𝓕, r g ∂μ = 0 := by
  have hpos := setLIntegral_eq_lintegral_indicator_mul_setLIntegral_sheet μ μH ν hQ B hBH hT hS hSH h𝓕m h𝓕S h𝓕
    (f := fun g => ENNReal.ofReal (r g)) (ENNReal.measurable_ofReal.comp hr) (fun b g => by simp only [hrB])
  have hneg := setLIntegral_eq_lintegral_indicator_mul_setLIntegral_sheet μ μH ν hQ B hBH hT hS hSH h𝓕m h𝓕S h𝓕
    (f := fun g => ENNReal.ofReal (-r g)) (ENNReal.measurable_ofReal.comp hr.neg) (fun b g => by simp only [hrB])
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hri, hpos, hneg, sub_eq_zero]
  congr 1
  refine lintegral_congr fun q => ?_
  by_cases hq : q.out ∈ S
  · rw [Set.indicator_of_mem hq, one_mul, one_mul]
    have hxy : Measurable fun x : H => (x : G) * q.out := measurable_subtype_coe.mul_const _
    rw [show (∫⁻ x in T, ENNReal.ofReal (r ((x : G) * q.out)) ∂μH)
          = ∫⁻ a, ENNReal.ofReal (r ((e a : G) * q.out)) ∂ρ from
        hρ _ (ENNReal.measurable_ofReal.comp (hr.comp hxy)),
      show (∫⁻ x in T, ENNReal.ofReal (-r ((x : G) * q.out)) ∂μH)
          = ∫⁻ a, ENNReal.ofReal (-r ((e a : G) * q.out)) ∂ρ from
        hρ _ (ENNReal.measurable_ofReal.comp (hr.neg.comp hxy))]
    obtain ⟨hint, hval⟩ := hz q.out hq
    have hdiff := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
    rw [hval] at hdiff
    have ha : ∫⁻ a, ENNReal.ofReal (r ((e a : G) * q.out)) ∂ρ ≠ ∞ :=
      ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hint.2).ne
    have hb : ∫⁻ a, ENNReal.ofReal (-r ((e a : G) * q.out)) ∂ρ ≠ ∞ :=
      ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hint.neg.2).ne
    exact (ENNReal.toReal_eq_toReal_iff' ha hb).mp (by linarith)
  · rw [Set.indicator_of_notMem hq, zero_mul, zero_mul]

private theorem setIntegral_eq_zero_of_forall_setIntegral_sheet_eq_zero [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SigmaFinite μ] (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]
    (ν : Measure (MulAction.orbitRel.Quotient H G))
    (hQ : ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μ = ∫⁻ q, ∫⁻ x : H, φ ((x : G) * q.out) ∂μH ∂ν)
    (B : Subgroup G) (hBH : B ≤ H) [Countable B] [MeasurableConstSMul B G]
    [MeasurableConstSMul (B.subgroupOf H) H] [SMulInvariantMeasure (B.subgroupOf H) H μH]
    {T : Set H} (hT : IsFundamentalDomain (B.subgroupOf H) T μH)
    {S : Set G} (hS : MeasurableSet S) (hSH : ∀ (x : H) (g : G), (x : G) * g ∈ S ↔ g ∈ S)
    [SMulInvariantMeasure B G (μ.restrict S)]
    {𝓕 : Set G} (h𝓕m : MeasurableSet 𝓕) (h𝓕S : 𝓕 ⊆ S) (h𝓕 : IsFundamentalDomain B 𝓕 (μ.restrict S))
    {A : Type*} [MeasurableSpace A] (ρ : Measure A) (e : A → H)
    (hρ : ∀ F : H → ℝ≥0∞, Measurable F → ∫⁻ x in T, F x ∂μH = ∫⁻ a, F (e a) ∂ρ)
    {f : G → ℂ} (hf : Measurable f) (hfB : ∀ (b : B) (g : G), f ((b : G) * g) = f g) (hfi : IntegrableOn f 𝓕 μ)
    (hz : ∀ y ∈ S, Integrable (fun a : A => f ((e a : G) * y)) ρ ∧ ∫ a, f ((e a : G) * y) ∂ρ = 0) :
    ∫ g in 𝓕, f g ∂μ = 0 := by
  have hre := setIntegral_eq_zero_of_forall_setIntegral_sheet_eq_zero_real μ μH ν hQ B hBH hT hS hSH h𝓕m h𝓕S h𝓕
    ρ e hρ (r := fun g => RCLike.re (f g)) (RCLike.measurable_re.comp hf) (fun b g => by simp only [hfB]) hfi.re
    (fun y hy => ⟨(hz y hy).1.re, by
      calc ∫ a, RCLike.re (f ((e a : G) * y)) ∂ρ
          = RCLike.re (∫ a, f ((e a : G) * y) ∂ρ) := integral_re (hz y hy).1
        _ = 0 := by rw [(hz y hy).2, map_zero]⟩)
  have him := setIntegral_eq_zero_of_forall_setIntegral_sheet_eq_zero_real μ μH ν hQ B hBH hT hS hSH h𝓕m h𝓕S h𝓕
    ρ e hρ (r := fun g => RCLike.im (f g)) (RCLike.measurable_im.comp hf) (fun b g => by simp only [hfB]) hfi.im
    (fun y hy => ⟨(hz y hy).1.im, by
      calc ∫ a, RCLike.im (f ((e a : G) * y)) ∂ρ
          = RCLike.im (∫ a, f ((e a : G) * y) ∂ρ) := integral_im (hz y hy).1
        _ = 0 := by rw [(hz y hy).2, map_zero]⟩)
  calc ∫ g in 𝓕, f g ∂μ
      = ((∫ g in 𝓕, RCLike.re (f g) ∂μ : ℝ) : ℂ) + ((∫ g in 𝓕, RCLike.im (f g) ∂μ : ℝ) : ℂ) * RCLike.I :=
        (integral_re_add_im hfi).symm
    _ = 0 := by rw [hre, him]; simp

private theorem measurableConstSMul_subgroup [MeasurableSpace G] [MeasurableMul G] (B : Subgroup G) :
    MeasurableConstSMul B G where
  measurable_const_smul b := by
    simpa [Subgroup.smul_def] using measurable_const_mul (b : G)

private theorem smulInvariantMeasure_subgroup [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (B : Subgroup G) : SMulInvariantMeasure B G μ where
  measure_preimage_smul b {E} _ := by
    simp [Subgroup.smul_def]

end SheetUnfolding

section SheetUnfoldingAdelic

variable (F : Type) [Field F] [NumberField F]

private theorem lintegral_adelicGLHaar_eq_lintegral_lintegral_rationalTorusUnipotent
    (φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫⁻ q, ∫⁻ x : AutomorphicForm.rationalTorusUnipotent F, φ ((x : AdelicGL2 (𝓞 F) F) * q.out)
          ∂(AutomorphicForm.rationalTorusUnipotentHaar F)
        ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := (AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).1
  haveI := (AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).2
  exact HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out (adelicGLHaar (Fin 2) (𝓞 F) F)
    (AutomorphicForm.rationalTorusUnipotent F) (AutomorphicForm.isClosed_rationalTorusUnipotent F)
    (AutomorphicForm.rationalTorusUnipotentHaar F) φ hφ

private theorem setLIntegral_eq_lintegral_indicator_mul_setLIntegral_adelicBox
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    (hSH : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    {𝓕 : Set (AdelicGL2 (𝓞 F) F)} (h𝓕m : MeasurableSet 𝓕) (h𝓕S : 𝓕 ⊆ S)
    (h𝓕 : IsFundamentalDomain ((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F)) 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    {f : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hf : Measurable f)
    (hfB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      f (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = f g) :
    ∫⁻ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫⁻ q, S.indicator (fun _ => (1 : ℝ≥0∞)) q.out *
          ∫⁻ u in adelicBox F, f (AutomorphicForm.unipotentGL2 u * q.out)
            ∂((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F)
        ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := (AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).1
  haveI := (AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).2
  haveI : LocallyCompactSpace (AutomorphicForm.rationalTorusUnipotent F) :=
    (AutomorphicForm.isClosed_rationalTorusUnipotent F).locallyCompactSpace
  haveI : SecondCountableTopology (AutomorphicForm.rationalTorusUnipotent F) :=
    TopologicalSpace.Subtype.secondCountableTopology
      (AutomorphicForm.rationalTorusUnipotent F : Set (AdelicGL2 (𝓞 F) F))
  haveI : IsFiniteMeasureOnCompacts (AutomorphicForm.rationalTorusUnipotentHaar F) := inferInstance
  haveI : IsLocallyFiniteMeasure (AutomorphicForm.rationalTorusUnipotentHaar F) :=
    isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (AutomorphicForm.rationalTorusUnipotentHaar F) := sigmaFinite_of_locallyFinite
  have hBS := AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  dsimp only at hBS
  obtain ⟨hBle, hBcount, -, hTfd, hTint⟩ := hBS
  letI := measurableMul_subgroup (AutomorphicForm.rationalTorusUnipotent F)
  letI := measurableConstSMul_subgroup ((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F))
  letI := measurableConstSMul_subgroup
    (((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf
      (AutomorphicForm.rationalTorusUnipotent F))
  letI := smulInvariantMeasure_subgroup (AutomorphicForm.rationalTorusUnipotentHaar F)
    (((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf
      (AutomorphicForm.rationalTorusUnipotent F))
  letI := smulInvariantMeasure_restrict (adelicGLHaar (Fin 2) (𝓞 F) F)
    ((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F))
    (fun b g => hSH (b : AdelicGL2 (𝓞 F) F) (hBle b.2) g)
  have hfB' : ∀ (b : (AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F))
      (g : AdelicGL2 (𝓞 F) F), f ((b : AdelicGL2 (𝓞 F) F) * g) = f g := by
    rintro ⟨_, γ, hγ, rfl⟩ g
    exact hfB γ hγ g
  exact setLIntegral_eq_lintegral_indicator_mul_lintegral_comp (adelicGLHaar (Fin 2) (𝓞 F) F)
    (AutomorphicForm.rationalTorusUnipotentHaar F) (AutomorphicForm.rationalTorusUnipotentQuotientMeasure F)
    (lintegral_adelicGLHaar_eq_lintegral_lintegral_rationalTorusUnipotent F)
    ((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F)) hBle hTfd hS
    (fun x g => hSH x x.2 g) h𝓕m h𝓕S h𝓕
    (((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F).restrict (adelicBox F))
    (fun u => Subgroup.inclusion le_sup_right (AutomorphicForm.toAdelicUnipotent F u)) hTint hf hfB'

private theorem setIntegral_eq_zero_of_forall_setIntegral_adelicBox_eq_zero
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    (hSH : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    {𝓕 : Set (AdelicGL2 (𝓞 F) F)} (h𝓕m : MeasurableSet 𝓕) (h𝓕S : 𝓕 ⊆ S)
    (h𝓕 : IsFundamentalDomain ((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F)) 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : Measurable f)
    (hfB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      f (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = f g)
    (hfi : IntegrableOn f 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hz : ∀ y ∈ S,
      IntegrableOn (fun u => f (AutomorphicForm.unipotentGL2 u * y)) (adelicBox F)
          ((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F) ∧
        ∫ u in adelicBox F, f (AutomorphicForm.unipotentGL2 u * y)
          ∂((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F) = 0) :
    ∫ g in 𝓕, f g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := by
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := (AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).1
  haveI := (AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).2
  haveI : LocallyCompactSpace (AutomorphicForm.rationalTorusUnipotent F) :=
    (AutomorphicForm.isClosed_rationalTorusUnipotent F).locallyCompactSpace
  haveI : SecondCountableTopology (AutomorphicForm.rationalTorusUnipotent F) :=
    TopologicalSpace.Subtype.secondCountableTopology
      (AutomorphicForm.rationalTorusUnipotent F : Set (AdelicGL2 (𝓞 F) F))
  haveI : IsFiniteMeasureOnCompacts (AutomorphicForm.rationalTorusUnipotentHaar F) := inferInstance
  haveI : IsLocallyFiniteMeasure (AutomorphicForm.rationalTorusUnipotentHaar F) :=
    isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (AutomorphicForm.rationalTorusUnipotentHaar F) := sigmaFinite_of_locallyFinite
  have hBS := AutomorphicForm.isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  dsimp only at hBS
  obtain ⟨hBle, hBcount, -, hTfd, hTint⟩ := hBS
  letI := measurableMul_subgroup (AutomorphicForm.rationalTorusUnipotent F)
  letI := measurableConstSMul_subgroup ((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F))
  letI := measurableConstSMul_subgroup
    (((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf
      (AutomorphicForm.rationalTorusUnipotent F))
  letI := smulInvariantMeasure_subgroup (AutomorphicForm.rationalTorusUnipotentHaar F)
    (((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf
      (AutomorphicForm.rationalTorusUnipotent F))
  letI := smulInvariantMeasure_restrict (adelicGLHaar (Fin 2) (𝓞 F) F)
    ((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F))
    (fun b g => hSH (b : AdelicGL2 (𝓞 F) F) (hBle b.2) g)
  have hfB' : ∀ (b : (AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F))
      (g : AdelicGL2 (𝓞 F) F), f ((b : AdelicGL2 (𝓞 F) F) * g) = f g := by
    rintro ⟨_, γ, hγ, rfl⟩ g
    exact hfB γ hγ g
  exact setIntegral_eq_zero_of_forall_setIntegral_sheet_eq_zero (adelicGLHaar (Fin 2) (𝓞 F) F)
    (AutomorphicForm.rationalTorusUnipotentHaar F) (AutomorphicForm.rationalTorusUnipotentQuotientMeasure F)
    (lintegral_adelicGLHaar_eq_lintegral_lintegral_rationalTorusUnipotent F)
    ((AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F)) hBle hTfd hS
    (fun x g => hSH x x.2 g) h𝓕m h𝓕S h𝓕
    (((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F).restrict (adelicBox F))
    (fun u => Subgroup.inclusion le_sup_right (AutomorphicForm.toAdelicUnipotent F u)) hTint hf hfB' hfi hz

end SheetUnfoldingAdelic

end AutomorphicForm.SlabCovolume

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc NumberField.AdelicBox"
open scoped Pointwise ENNReal

section HighPartVanishing

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem weylIntertwiningIntegral_unipotentGL2_mul (φ : AdelicGL2 (𝓞 F) F → ℂ) (u : AdeleRing (𝓞 F) F)
    (y : AdelicGL2 (𝓞 F) F) :
    weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ (unipotentGL2 u * y) =
      weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ y := by
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have h := integral_add_right_eq_self (μ := NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)
    (fun x => φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * y)) u
  simp only [weylIntertwiningIntegral, unipotentGL2_add, mul_assoc] at h ⊢
  exact h

private theorem setIntegral_adelicBox_bigCellSum_sub_eq_zero (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (y : AdelicGL2 (𝓞 F) F) (hφN : ∀ u : AdeleRing (𝓞 F) F, φ (unipotentGL2 u * y) = φ y)
    (hCT : constantTerm
        (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
        (fun g' => φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g'))
        y =
      φ y + (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ y) :
    ∫ u in adelicBox F,
        ((∑' ξ : F,
            φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (unipotentGL2 u * y))) -
          (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ (unipotentGL2 u * y))
      ∂(((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ •
        NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) = 0 := by
  have hne : NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F (adelicBox F) ≠ 0 := (adelicAddHaar_adelicBox_pos F).ne'
  have htop : NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F (adelicBox F) ≠ ∞ := (adelicAddHaar_adelicBox_lt_top F).ne
  haveI := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hne htop
  rw [Measure.restrict_smul]
  show ∫ u, _ ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) = 0

  have hpt : ∀ u : AdeleRing (𝓞 F) F,
      (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (unipotentGL2 u * y))) -
          (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ (unipotentGL2 u * y) =
        (φ (unipotentGL2 u * y) +
            ∑' ξ : F,
              φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (unipotentGL2 u * y))) -
          (φ y + (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ y) := fun u => by
    rw [weylIntertwiningIntegral_unipotentGL2_mul, hφN u]
    ring
  simp_rw [hpt]
  have hCT' : ∫ u, (φ (unipotentGL2 u * y) +
      ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (unipotentGL2 u * y)))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) =
      φ y + (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ y := by
    simpa only [constantTerm, constantTermIntegrand] using hCT
  by_cases hI : Integrable (fun u => φ (unipotentGL2 u * y) +
      ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (unipotentGL2 u * y)))
      (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F))
  · rw [integral_sub hI (integrable_const _), integral_const, probReal_univ, one_smul, hCT', sub_self]
  · refine integral_undef fun h => hI ?_
    have h' : Integrable (fun u => (φ (unipotentGL2 u * y) +
        ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (unipotentGL2 u * y))) -
          (φ y + (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ y) +
          (φ y + (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ y))
        (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) :=
      h.add (integrable_const _)
    simp only [sub_add_cancel] at h'
    exact h'

private theorem setIntegral_highPart_bigCellSum_sub_eq_zero {T d₁ d₂ : ℝ} (hT : 1 ≤ T) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀m : MeasurableSet Φ₀) (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφN : ∀ (u : AdeleRing (𝓞 F) F) (y : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 u * y) = φ y)
    (hCT : ∀ y : AdelicGL2 (𝓞 F) F, constantTerm
        (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
        (fun g' => φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g'))
        y =
      φ y + (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ y)
    (hB : ∀ γ ∈ borelSubgroup F, ∀ g,
      (fun g => (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g)
        (globalPoints (𝓞 F) F γ * g) =
      (fun g => (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g) g)
    (hmeas : Measurable
      (fun g => (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g))
    (hIO : IntegrableOn
      (fun g => (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g)
      (highPart F T Φ₀) (adelicGLHaar (Fin 2) (𝓞 F) F))
    (hIy : ∀ y ∈ highSlab F T d₁ d₂, IntegrableOn
      (fun u => (fun g => (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g) (unipotentGL2 u * y))
      (adelicBox F)
      (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ •
        NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)) :
    ∫ g in highPart F T Φ₀,
        ((∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
          (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g)
      ∂adelicGLHaar (Fin 2) (𝓞 F) F = 0 :=
  setIntegral_eq_zero_of_forall_setIntegral_adelicBox_eq_zero F (measurableSet_highSlab T d₁ d₂)
    (fun _ hx g => mul_mem_highSlab_iff_of_mem_rationalTorusUnipotent hx g) (measurableSet_highPart hΦ₀m)
    (highPart_subset_highSlab hΦ₀s) (isFundamentalDomain_highPart hT hΦ₀m hΦ₀s hΦ₀) hmeas hB hIO
    fun y hy => ⟨hIy y hy, setIntegral_adelicBox_bigCellSum_sub_eq_zero φ y (fun u => hφN u y) (hCT y)⟩

end HighPartVanishing

end AutomorphicForm.SlabCovolume

section BoxIntegrabilityOfUnipotentTranslates

open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

private theorem integrableOn_adelicBox_comp_unipotentGL2_mul_sub_const {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : Continuous f) (y : AdelicGL2 (𝓞 F) F) (c : ℂ) :
    IntegrableOn (fun u => f (unipotentGL2 u * y) - c) (adelicBox F)
      ((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F) := by
  have hbox : adelicAddHaar (𝓞 F) F (adelicBox F) ≠ ⊤ := (adelicAddHaar_adelicBox_lt_top F).ne
  have hinv : (adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (adelicAddHaar_adelicBox_pos F).ne'
  have hg : Continuous (fun u : AdeleRing (𝓞 F) F => f (unipotentGL2 u * y)) :=
    hf.comp ((continuous_unipotentGL2_adeleRing F).mul continuous_const)
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hg.continuousOn
  have h1 : IntegrableOn (fun u => f (unipotentGL2 u * y)) (adelicBox F) (adelicAddHaar (𝓞 F) F) :=
    (integrableOn_const (C := M) hbox).mono' hg.aestronglyMeasurable
      (ae_restrict_of_forall_mem (measurableSet_adelicBox F) fun u hu => hM u (hsub hu))
  have h2 : IntegrableOn (fun u => f (unipotentGL2 u * y) - c) (adelicBox F) (adelicAddHaar (𝓞 F) F) :=
    Integrable.sub h1 (integrableOn_const (C := c) hbox)
  rw [IntegrableOn, Measure.restrict_smul]
  exact Integrable.smul_measure h2 hinv

private theorem integrableOn_adelicBox_comp_unipotentGL2_mul {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : Continuous f)
    (y : AdelicGL2 (𝓞 F) F) :
    IntegrableOn (fun u => f (unipotentGL2 u * y)) (adelicBox F)
      ((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F) := by
  simpa using integrableOn_adelicBox_comp_unipotentGL2_mul_sub_const hf y 0

end BoxIntegrabilityOfUnipotentTranslates

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.AdelicLevel NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc"
open NumberField.AdelicBox
open scoped ENNReal

section HighPartMeasure

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem ideleNorm_pow_eq_pow (x : (AdeleRing (𝓞 F) F)ˣ) (n : ℕ) :
    ideleNorm F (x ^ n) = ideleNorm F x ^ n := by
  induction n with
  | zero => simp [ideleNorm]
  | succ n ih => rw [pow_succ, ideleNorm_mul, ih, pow_succ]

private theorem ideleNorm_inv_eq_inv (x : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F x⁻¹ = (ideleNorm F x)⁻¹ := by
  have h1 : ideleNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by simp [ideleNorm]
  exact eq_inv_of_mul_eq_one_right (by rw [← ideleNorm_mul, mul_inv_cancel, h1])

private theorem ideleNorm_det_eq_one_of_mem_adelicMaximalCompact {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ adelicMaximalCompact F) : ideleNorm F (Matrix.GeneralLinearGroup.det k) = 1 := by
  obtain ⟨B, hB⟩ := (isCompact_adelicMaximalCompact F).bddAbove_image
    (f := fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g))
    (NumberField.TateGlobal.continuous_ideleNorm_det F).continuousOn
  have hB' : ∀ g ∈ adelicMaximalCompact F, ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ B :=
    fun g hg => hB ⟨g, hg, rfl⟩
  have hle : ∀ g ∈ adelicMaximalCompact F, ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ 1 := by
    intro g hg
    by_contra h
    rw [not_le] at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
    rw [← ideleNorm_pow_eq_pow, ← map_pow] at hn
    exact absurd (hB' (g ^ n) (pow_mem hg n)) (not_le.mpr hn)
  have h1 := hle k hk
  have h2 := hle k⁻¹ (inv_mem hk)
  rw [map_inv, ideleNorm_inv_eq_inv, inv_le_one₀ (ideleNorm_pos _)] at h2
  exact le_antisymm h1 h2

private theorem det_diagOne_eq (t : (AdeleRing (𝓞 F) F)ˣ) : Matrix.GeneralLinearGroup.det (diagOne t) = t := by
  ext
  simp [Matrix.det_fin_two, diagOne_coe_apply]

private theorem val_modChar_eq_ideleNorm (t : (AdeleRing (𝓞 F) F)ˣ) : ((modChar F t : ℝˣ) : ℝ) = ideleNorm F t := rfl

private theorem indicator_highSlab_centralScalar_mul_diagOne_mul (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (T d₁ d₂ : ℝ) (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    (highSlab F T d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞))
        (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) =
      (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (ideleNorm F z ^ 2 * ideleNorm F t) *
        (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) (ideleNorm F t) := by
  have hdet :
      ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        ideleNorm F z ^ 2 * ideleNorm F t := by
    rw [map_mul, map_mul, ideleNorm_mul, ideleNorm_mul, det_centralScalar, ideleNorm_pow_eq_pow, det_diagOne_eq,
      ideleNorm_det_eq_one_of_mem_adelicMaximalCompact k.2, mul_one]
  have hh : adelicHeight F (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) = ideleNorm F t := by
    rw [mul_assoc, adelicHeight_centralScalar_mul hα, adelicHeight_diagOne_mul hα,
      adelicHeight_eq_one_of_mem_adelicMaximalCompact k.2, mul_one, val_modChar_eq_ideleNorm]
  have hmem : centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ highSlab F T d₁ d₂ ↔
      ideleNorm F t ∈ Set.Ioi T ∧ ideleNorm F z ^ 2 * ideleNorm F t ∈ Set.Icc d₁ d₂ := by
    simp only [highSlab, Set.mem_inter_iff, Set.mem_setOf_eq, hh, hdet, Set.mem_Ioi]
  by_cases hA : ideleNorm F z ^ 2 * ideleNorm F t ∈ Set.Icc d₁ d₂
  · by_cases hB : ideleNorm F t ∈ Set.Ioi T
    · rw [Set.indicator_of_mem (hmem.mpr ⟨hB, hA⟩), Set.indicator_of_mem hA, Set.indicator_of_mem hB]
      simp
    · rw [Set.indicator_of_notMem (fun h => hB (hmem.mp h).1), Set.indicator_of_notMem hB]
      simp
  · rw [Set.indicator_of_notMem (fun h => hA (hmem.mp h).2), Set.indicator_of_notMem hA]
    simp

private theorem lintegral_lintegral_indicator_sq_mul_eq {T d₁ d₂ : ℝ} (L P : ℝ≥0∞)
    (hlog : ∀ y : ℝ, 0 < y →
      ∫⁻ x in Set.Ioi (0 : ℝ), (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * ENNReal.ofReal x⁻¹ = L)
    (hpow : ∫⁻ y in Set.Ioi (0 : ℝ),
      (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ = P) :
    ∫⁻ x in Set.Ioi (0 : ℝ), (∫⁻ y in Set.Ioi (0 : ℝ),
        (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y *
          ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹) * ENNReal.ofReal x⁻¹ = L * P := by
  have hI : Measurable fun p : ℝ × ℝ => (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (p.1 ^ 2 * p.2) :=
    (measurable_const.indicator measurableSet_Icc).comp ((measurable_fst.pow_const 2).mul measurable_snd)
  have hJ : Measurable fun p : ℝ × ℝ => (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) p.2 :=
    (measurable_const.indicator measurableSet_Ioi).comp measurable_snd
  have hx : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1⁻¹ := measurable_fst.inv.ennreal_ofReal
  have hy : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.2⁻¹ := measurable_snd.inv.ennreal_ofReal
  have hG : Measurable fun p : ℝ × ℝ => (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (p.1 ^ 2 * p.2) *
      (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) p.2 * ENNReal.ofReal p.2⁻¹ * ENNReal.ofReal p.2⁻¹ *
        ENNReal.ofReal p.1⁻¹ := (((hI.mul hJ).mul hy).mul hy).mul hx
  calc ∫⁻ x in Set.Ioi (0 : ℝ), (∫⁻ y in Set.Ioi (0 : ℝ),
          (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y *
            ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹) * ENNReal.ofReal x⁻¹
      = ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
          (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y *
            ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ * ENNReal.ofReal x⁻¹ := by
        refine lintegral_congr fun x => ?_
        have hm : Measurable fun y : ℝ => (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) *
            (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ :=
          ((((measurable_const.indicator measurableSet_Icc).comp (measurable_id.const_mul (x ^ 2))).mul
            (measurable_const.indicator measurableSet_Ioi)).mul measurable_inv.ennreal_ofReal).mul
              measurable_inv.ennreal_ofReal
        exact (lintegral_mul_const _ hm).symm
    _ = ∫⁻ y in Set.Ioi (0 : ℝ), ∫⁻ x in Set.Ioi (0 : ℝ),
          (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y *
            ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ * ENNReal.ofReal x⁻¹ :=
        lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ y in Set.Ioi (0 : ℝ), (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ *
          ENNReal.ofReal y⁻¹ *
            ∫⁻ x in Set.Ioi (0 : ℝ),
              (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * ENNReal.ofReal x⁻¹ := by
        refine lintegral_congr fun y => ?_
        have hc : ∀ x : ℝ, (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) *
            (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ *
              ENNReal.ofReal x⁻¹ =
            (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ *
              ((Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * ENNReal.ofReal x⁻¹) := fun x => by ring
        simp_rw [hc]
        exact lintegral_const_mul _ ((hI.comp measurable_prodMk_right).mul measurable_inv.ennreal_ofReal)
    _ = ∫⁻ y in Set.Ioi (0 : ℝ), (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ *
          ENNReal.ofReal y⁻¹ * L :=
        setLIntegral_congr_fun measurableSet_Ioi fun y hy => by rw [hlog y hy]
    _ = L * P := by
        rw [lintegral_mul_const L, hpow, mul_comm]
        exact ((measurable_const.indicator measurableSet_Ioi).mul
          measurable_inv.ennreal_ofReal).mul measurable_inv.ennreal_ofReal

private theorem measure_highPart_eq (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ)) {T d₁ d₂ : ℝ}
    {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hD1 : ∫⁻ _ in highPart F T Φ₀, (1 : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫⁻ q, (highSlab F T d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) q.out *
          ∫⁻ _ in adelicBox F, (1 : ℝ≥0∞)
            ∂((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ •
              NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)
        ∂(rationalTorusUnipotentQuotientMeasure F))
    (cq : ℝ≥0∞) {D : Set (AdeleRing (𝓞 F) F)ˣ} (V L P : ℝ≥0∞)
    (hlaw : ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
      (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
          cq * ∫⁻ z in D, ∫⁻ t in D, ∫⁻ k,
                f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) * ENNReal.ofReal ((ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi 0, f y * ENNReal.ofReal y⁻¹)
    (hlog : ∀ y : ℝ, 0 < y →
      ∫⁻ x in Set.Ioi (0 : ℝ), (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * ENNReal.ofReal x⁻¹ = L)
    (hpow : ∫⁻ y in Set.Ioi (0 : ℝ),
      (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ = P) :
    adelicGLHaar (Fin 2) (𝓞 F) F (highPart F T Φ₀) = cq * V * V * (L * P) := by
  have hb0 : NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F (adelicBox F) ≠ 0 := (adelicAddHaar_adelicBox_pos F).ne'
  have hbt : NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F (adelicBox F) ≠ ∞ := (adelicAddHaar_adelicBox_lt_top F).ne
  rw [setLIntegral_one, setLIntegral_one, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hb0 hbt] at hD1
  simp_rw [mul_one] at hD1
  rw [hD1, hlaw _ (measurable_const.indicator (measurableSet_highSlab T d₁ d₂)) fun _ hx g => by
    by_cases hg : g ∈ highSlab F T d₁ d₂
    · rw [Set.indicator_of_mem hg,
        Set.indicator_of_mem ((mul_mem_highSlab_iff_of_mem_rationalTorusUnipotent hx g).mpr hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem (fun h => hg ((mul_mem_highSlab_iff_of_mem_rationalTorusUnipotent hx g).mp h))]]
  simp_rw [indicator_highSlab_centralScalar_mul_diagOne_mul hα, lintegral_const, measure_univ, mul_one]
  have hinner : ∀ x : ℝ, ∫⁻ t in D, (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * ideleNorm F t) *
      (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) (ideleNorm F t) * ENNReal.ofReal (ideleNorm F t)⁻¹
        ∂(NumberField.Idele.idelicHaar F) =
      V * ∫⁻ y in Set.Ioi 0, (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) *
        (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ := fun x =>
    hV (fun y => (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) *
        (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹)
      ((((measurable_const.indicator measurableSet_Icc).comp (measurable_id.const_mul (x ^ 2))).mul
        (measurable_const.indicator measurableSet_Ioi)).mul measurable_inv.ennreal_ofReal)
  simp_rw [hinner]
  have hI : Measurable fun p : ℝ × ℝ => (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (p.1 ^ 2 * p.2) :=
    (measurable_const.indicator measurableSet_Icc).comp ((measurable_fst.pow_const 2).mul measurable_snd)
  have hJ : Measurable fun p : ℝ × ℝ => (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) p.2 :=
    (measurable_const.indicator measurableSet_Ioi).comp measurable_snd
  have hy : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.2⁻¹ := measurable_snd.inv.ennreal_ofReal
  have houter := hV (fun x => V * ∫⁻ y in Set.Ioi 0, (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) *
      (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹)
    ((((hI.mul hJ).mul hy).mul hy).lintegral_prod_right'.const_mul V)
  beta_reduce at houter
  rw [houter]
  have hK : Measurable fun x : ℝ => (∫⁻ y in Set.Ioi (0 : ℝ),
      (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * (Set.Ioi T).indicator (fun _ => (1 : ℝ≥0∞)) y *
        ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹) * ENNReal.ofReal x⁻¹ :=
    (((hI.mul hJ).mul hy).mul hy).lintegral_prod_right'.mul measurable_inv.ennreal_ofReal
  simp_rw [mul_assoc V]
  rw [lintegral_const_mul V hK, lintegral_lintegral_indicator_sq_mul_eq L P hlog hpow]
  ring

end HighPartMeasure

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section RepsUnfolding

open Function
open scoped Pointwise
variable {G : Type*} [Group G] {ι : Type*}

private def repsUnion (c : ι → G) (Φ : Set G) : Set G :=
  ⋃ i, (c i * ·) '' Φ

private theorem image_mul_left_eq_preimage (a : G) (Φ : Set G) : (a * ·) '' Φ = (a⁻¹ * ·) ⁻¹' Φ :=
  Set.image_mul_left

private theorem measurableSet_image_mul_left [MeasurableSpace G] [MeasurableMul G] (a : G) {Φ : Set G}
    (hΦ : MeasurableSet Φ) : MeasurableSet ((a * ·) '' Φ) := by
  rw [image_mul_left_eq_preimage]
  exact hΦ.preimage (measurable_const_mul _)

private theorem measurableSet_repsUnion [MeasurableSpace G] [MeasurableMul G] [Countable ι] (c : ι → G) {Φ : Set G}
    (hΦ : MeasurableSet Φ) : MeasurableSet (repsUnion c Φ) :=
  MeasurableSet.iUnion fun i => measurableSet_image_mul_left (c i) hΦ

private theorem repsUnion_subset {Γ : Subgroup G} (c : ι → G) (hc : ∀ i, c i ∈ Γ) {S Φ : Set G}
    (hSΓ : ∀ γ ∈ Γ, ∀ g : G, γ * g ∈ S ↔ g ∈ S) (hΦS : Φ ⊆ S) : repsUnion c Φ ⊆ S := by
  rintro _ hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy, rfl⟩ := hi
  exact (hSΓ (c i) (hc i) y).mpr (hΦS hy)

private theorem smul_image_mul_left {B : Subgroup G} (b : B) (a : G) (Φ : Set G) :
    b • ((a * ·) '' Φ) = (((b : G) * a) * ·) '' Φ := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_image, Subgroup.smul_def, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, mul_assoc _ _ _⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a * y, ⟨y, hy, rfl⟩, (mul_assoc _ _ _).symm⟩

private theorem subgroup_smul_set_eq {Γ : Subgroup G} (γ : Γ) (Φ : Set G) : γ • Φ = (((γ : G)) * ·) '' Φ := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_image, Subgroup.smul_def, smul_eq_mul]

private theorem aedisjoint_image_mul_left {Γ : Subgroup G} [MeasurableSpace G] {ν : Measure G} {Φ : Set G}
    (hΦ : IsFundamentalDomain Γ Φ ν) {a a' : G} (ha : a ∈ Γ) (ha' : a' ∈ Γ) (hne : a ≠ a') :
    AEDisjoint ν ((a * ·) '' Φ) ((a' * ·) '' Φ) := by
  have h := hΦ.aedisjoint (show (⟨a, ha⟩ : Γ) ≠ ⟨a', ha'⟩ from fun h => hne (congrArg Subtype.val h))
  simpa only [Function.onFun, subgroup_smul_set_eq] using h

private theorem isFundamentalDomain_repsUnion [MeasurableSpace G] [MeasurableMul G] [Countable ι] {Γ B : Subgroup G}
    (hBΓ : B ≤ Γ) (c : ι → G) (hc : ∀ i, c i ∈ Γ) (hcover : ∀ γ ∈ Γ, ∃ b ∈ B, ∃ i, γ = b * c i)
    (hdist : ∀ i j, ∀ b ∈ B, b * c i = c j → i = j) {ν : Measure G} {Φ : Set G} (hΦm : MeasurableSet Φ)
    (hΦ : IsFundamentalDomain Γ Φ ν) : IsFundamentalDomain B (repsUnion c Φ) ν where
  nullMeasurableSet := (measurableSet_repsUnion c hΦm).nullMeasurableSet
  ae_covers := by
    filter_upwards [hΦ.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨b, hb, i, hi⟩ := hcover ((γ : G)⁻¹) (inv_mem γ.2)
    refine ⟨⟨b⁻¹, inv_mem hb⟩, Set.mem_iUnion.mpr ⟨i, (γ : G) * x, hγ, ?_⟩⟩
    have hci : c i = b⁻¹ * (γ : G)⁻¹ := by rw [eq_inv_mul_iff_mul_eq, hi]
    simp only [Subgroup.smul_def, smul_eq_mul, hci, mul_assoc, inv_mul_cancel_left]
  aedisjoint := by
    intro b₁ b₂ hne
    simp only [Function.onFun, repsUnion, Set.smul_set_iUnion, smul_image_mul_left]
    refine AEDisjoint.iUnion_left_iff.mpr fun i => AEDisjoint.iUnion_right_iff.mpr fun j => ?_
    refine aedisjoint_image_mul_left hΦ (mul_mem (hBΓ b₁.2) (hc i)) (mul_mem (hBΓ b₂.2) (hc j)) ?_
    intro heq
    have hij : i = j := hdist i j ((b₂ : G)⁻¹ * b₁) (mul_mem (inv_mem b₂.2) b₁.2) (by
      rw [mul_assoc, heq, inv_mul_cancel_left])
    subst hij
    exact hne (Subtype.ext (mul_right_cancel heq))

private theorem pairwise_aedisjoint_image_mul_left [MeasurableSpace G] {Γ : Subgroup G} (μ : Measure G) {S Φ : Set G}
    (hΦ : IsFundamentalDomain Γ Φ (μ.restrict S)) (c : ι → G) (hc : ∀ i, c i ∈ Γ)
    (hinj : Function.Injective c) (hSΓ : ∀ γ ∈ Γ, ∀ g : G, γ * g ∈ S ↔ g ∈ S) (hΦS : Φ ⊆ S) :
    Pairwise (AEDisjoint μ on fun i => (c i * ·) '' Φ) := by
  intro i j hij
  have h := aedisjoint_image_mul_left hΦ (hc i) (hc j) (fun h => hij (hinj h))
  have hsub : (c i * ·) '' Φ ∩ (c j * ·) '' Φ ⊆ S := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hx.1
    exact (hSΓ (c i) (hc i) y).mpr (hΦS hy)
  show μ ((c i * ·) '' Φ ∩ (c j * ·) '' Φ) = 0
  rw [← Measure.restrict_eq_self μ hsub]
  exact h

private theorem setLIntegral_image_mul_left [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (a : G) {Φ : Set G} (hΦm : MeasurableSet Φ) (F : G → ℝ≥0∞) :
    ∫⁻ g in (a * ·) '' Φ, F g ∂μ = ∫⁻ g in Φ, F (a * g) ∂μ := by
  rw [image_mul_left_eq_preimage, ← lintegral_indicator (hΦm.preimage (measurable_const_mul _)),
    ← lintegral_indicator hΦm, ← lintegral_mul_left_eq_self _ a]
  refine lintegral_congr fun g => ?_
  by_cases hg : g ∈ Φ
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem]
    simpa using hg
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem]
    simpa using hg

private theorem setLIntegral_tsum_eq_setLIntegral_repsUnion [MeasurableSpace G] [MeasurableMul G] [Countable ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] (c : ι → G) {Φ : Set G} (hΦm : MeasurableSet Φ)
    (hdisj : Pairwise (AEDisjoint μ on fun i => (c i * ·) '' Φ)) {F : G → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g in Φ, ∑' i, F (c i * g) ∂μ = ∫⁻ g in repsUnion c Φ, F g ∂μ := by
  rw [repsUnion, lintegral_iUnion₀ (fun i => (measurableSet_image_mul_left (c i) hΦm).nullMeasurableSet) hdisj,
    lintegral_tsum (f := fun i g => F (c i * g)) fun i => (hF.comp (measurable_const_mul (c i))).aemeasurable]
  exact tsum_congr fun i => (setLIntegral_image_mul_left μ (c i) hΦm F).symm

end RepsUnfolding

section BruhatUnfoldingAdelic

variable (F : Type) [Field F] [NumberField F]

private theorem map_borelSubgroup_le_range :
    (AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F) ≤
      (AutomorphicForm.globalPoints (𝓞 F) F).range := by
  rintro _ ⟨γ, -, rfl⟩
  exact ⟨γ, rfl⟩

private theorem exists_mem_map_borelSubgroup_eq_mul_bruhatRep (γ : AdelicGL2 (𝓞 F) F)
    (hγ : γ ∈ (AutomorphicForm.globalPoints (𝓞 F) F).range) :
    ∃ b ∈ (AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F),
      ∃ τ : Option F, γ = b * bruhatRep (F := F) τ := by
  obtain ⟨δ, rfl⟩ := hγ
  by_cases hδ : (δ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · exact ⟨AutomorphicForm.globalPoints (𝓞 F) F δ,
      Subgroup.mem_map_of_mem _ ((AutomorphicForm.mem_borelSubgroup_iff _).mpr hδ), none, (mul_one _).symm⟩
  · obtain ⟨β, hβ, ξ, hδβ⟩ := exists_mem_borelSubgroup_eq_mul_gl2Weyl_mul_unipotentGL2 δ hδ
    refine ⟨AutomorphicForm.globalPoints (𝓞 F) F β, Subgroup.mem_map_of_mem _ hβ, some ξ, ?_⟩
    rw [hδβ, map_mul, globalPoints_gl2Weyl_mul_unipotentGL2 (F := F) ξ]
    rfl

private def bruhatRepRational : Option F → GL (Fin 2) F
  | none => 1
  | some ξ => AutomorphicForm.gl2Weyl * AutomorphicForm.unipotentGL2 ξ

private theorem bruhatRep_eq_globalPoints (τ : Option F) :
    bruhatRep (F := F) τ = AutomorphicForm.globalPoints (𝓞 F) F (bruhatRepRational F τ) := by
  cases τ with
  | none => exact (map_one _).symm
  | some ξ => exact (globalPoints_gl2Weyl_mul_unipotentGL2 (F := F) ξ).symm

private theorem entry_eq_of_globalPoints_eq {x y : GL (Fin 2) F}
    (h : AutomorphicForm.globalPoints (𝓞 F) F x = AutomorphicForm.globalPoints (𝓞 F) F y) (i j : Fin 2) :
    (x : Matrix (Fin 2) (Fin 2) F) i j = (y : Matrix (Fin 2) (Fin 2) F) i j := by
  apply NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
  rw [← AutomorphicForm.globalPoints_apply, ← AutomorphicForm.globalPoints_apply, h]

private theorem bruhatRep_injective_mod_borel (τ τ' : Option F) (b : AdelicGL2 (𝓞 F) F)
    (hb : b ∈ (AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F))
    (h : b * bruhatRep (F := F) τ = bruhatRep (F := F) τ') : τ = τ' := by
  obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.mp hb
  rw [bruhatRep_eq_globalPoints F τ, bruhatRep_eq_globalPoints F τ', ← map_mul] at h
  have h10 := entry_eq_of_globalPoints_eq F h 1 0
  have h11 := entry_eq_of_globalPoints_eq F h 1 1
  have hβ10 : (β : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := (AutomorphicForm.mem_borelSubgroup_iff _).mp hβ
  cases τ with
  | none =>
    cases τ' with
    | none => rfl
    | some ξ' =>
      simp [bruhatRepRational, Matrix.mul_apply, Fin.sum_univ_two, hβ10] at h10
  | some ξ =>
    cases τ' with
    | none =>
      exfalso
      have e10 : (β : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
        simpa [bruhatRepRational, Matrix.mul_apply, Fin.sum_univ_two, hβ10] using h10
      have e11 : (β : Matrix (Fin 2) (Fin 2) F) 1 1 * ξ = 1 := by
        simpa [bruhatRepRational, Matrix.mul_apply, Fin.sum_univ_two, hβ10] using h11
      rw [e10, zero_mul] at e11
      exact zero_ne_one e11
    | some ξ' =>
      have e10 : (β : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
        simpa [bruhatRepRational, Matrix.mul_apply, Fin.sum_univ_two, hβ10] using h10
      have e11 : (β : Matrix (Fin 2) (Fin 2) F) 1 1 * ξ = ξ' := by
        simpa [bruhatRepRational, Matrix.mul_apply, Fin.sum_univ_two, hβ10] using h11
      rw [e10, one_mul] at e11
      rw [e11]

private theorem setLIntegral_tsum_bruhatRep_mul_eq_lintegral_indicator_mul_setLIntegral_adelicBox
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    (hSΓ : ∀ γ ∈ (AutomorphicForm.globalPoints (𝓞 F) F).range, ∀ g : AdelicGL2 (𝓞 F) F, γ * g ∈ S ↔ g ∈ S)
    (hSH : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    {Φ : Set (AdelicGL2 (𝓞 F) F)} (hΦm : MeasurableSet Φ) (hΦS : Φ ⊆ S)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    {f : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hf : Measurable f)
    (hfB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      f (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = f g) :
    ∫⁻ g in Φ, ∑' τ : Option F, f (bruhatRep (F := F) τ * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫⁻ q, S.indicator (fun _ => (1 : ℝ≥0∞)) q.out *
          ∫⁻ u in adelicBox F, f (AutomorphicForm.unipotentGL2 u * q.out)
            ∂((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F)
        ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) := by
  haveI : Countable F := countable_field (F := F)
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hreps : ∀ τ : Option F, bruhatRep (F := F) τ ∈ (AutomorphicForm.globalPoints (𝓞 F) F).range :=
    fun τ => bruhatRep_mem_range (F := F) τ
  have hdist : ∀ τ τ' : Option F,
      ∀ b ∈ (AutomorphicForm.borelSubgroup F).map (AutomorphicForm.globalPoints (𝓞 F) F),
        b * bruhatRep (F := F) τ = bruhatRep (F := F) τ' → τ = τ' :=
    fun τ τ' b hb h => bruhatRep_injective_mod_borel F τ τ' b hb h
  have hinj : Function.Injective (bruhatRep (F := F)) := fun τ τ' h =>
    hdist τ τ' 1 (one_mem _) (by rw [one_mul, h])
  rw [setLIntegral_tsum_eq_setLIntegral_repsUnion (adelicGLHaar (Fin 2) (𝓞 F) F) (bruhatRep (F := F)) hΦm
    (pairwise_aedisjoint_image_mul_left (adelicGLHaar (Fin 2) (𝓞 F) F) hΦ (bruhatRep (F := F)) hreps hinj hSΓ
      hΦS) hf]
  exact setLIntegral_eq_lintegral_indicator_mul_setLIntegral_adelicBox F hS hSH
    (measurableSet_repsUnion (bruhatRep (F := F)) hΦm) (repsUnion_subset (bruhatRep (F := F)) hreps hSΓ hΦS)
    (isFundamentalDomain_repsUnion (map_borelSubgroup_le_range F) (bruhatRep (F := F)) hreps
      (fun γ hγ => exists_mem_map_borelSubgroup_eq_mul_bruhatRep F γ hγ) hdist hΦm hΦ) hf hfB

end BruhatUnfoldingAdelic

end AutomorphicForm.SlabCovolume

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

open Filter
open scoped Topology

section ResidueLimitAlgebra

private theorem tendsto_ofReal_nhdsGT_zero : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := Complex.continuous_ofReal.tendsto (0 : ℝ)
  rw [Complex.ofReal_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

private theorem tendsto_const_cpow_ofReal_nhdsGT_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (fun t : ℝ => (T : ℂ) ^ (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have h := tendsto_ofReal_nhdsGT_zero.const_cpow (a := (T : ℂ)) (Or.inl hT0)
  rwa [Complex.cpow_zero] at h

private theorem tendsto_const_cpow_neg_one_sub_div_nhdsGT_zero {T : ℝ} (hT : 0 < T) :
    Tendsto (fun t : ℝ => (T : ℂ) ^ (-1 - (t : ℂ)) / (1 + (t : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (T : ℂ)⁻¹) := by
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have h1 : Tendsto (fun t : ℝ => (T : ℂ) ^ (-1 - (t : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 ((T : ℂ) ^ (-1 : ℂ))) := by
    have h := (tendsto_const_nhds (x := (-1 : ℂ))).sub tendsto_ofReal_nhdsGT_zero
    rw [sub_zero] at h
    exact h.const_cpow (Or.inl hT0)
  have h2 : Tendsto (fun t : ℝ => (1 : ℂ) + (t : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℂ))).add tendsto_ofReal_nhdsGT_zero
    rwa [add_zero] at h
  have h3 := h1.div h2 one_ne_zero
  rw [Complex.cpow_neg_one, div_one] at h3
  exact h3

private theorem mul_eq_of_tendsto_of_forall_sub_mul_eq {E Aψ AM P Q : ℝ → ℂ} {K binv vl r A₀ m₀ q : ℂ} {δ : ℝ}
    (hδ : 0 < δ)
    (hid : ∀ t ∈ Set.Ioo (0 : ℝ) δ, (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * E t =
      K * (Aψ t * P t - binv * ((((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * AM t) * Q t))
    (hlow : Tendsto (fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * E t) (𝓝[>] (0 : ℝ)) (𝓝 (vl * r)))
    (hA : Tendsto Aψ (𝓝[>] (0 : ℝ)) (𝓝 A₀))
    (hM : Tendsto (fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * AM t) (𝓝[>] (0 : ℝ)) (𝓝 m₀))
    (hP : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 1)) (hQ : Tendsto Q (𝓝[>] (0 : ℝ)) (𝓝 q)) :
    vl * r = K * (A₀ - binv * m₀ * q) := by
  have hR : Tendsto (fun t : ℝ => K * (Aψ t * P t - binv * ((((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * AM t) * Q t))
      (𝓝[>] (0 : ℝ)) (𝓝 (K * (A₀ * 1 - binv * m₀ * q))) :=
    ((hA.mul hP).sub ((hM.const_mul binv).mul hQ)).const_mul K
  rw [mul_one] at hR
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := eventually_nhdsWithin_of_forall fun t ht => ht
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < δ := eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)
  have hev : (fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * E t) =ᶠ[𝓝[>] (0 : ℝ)]
      fun t : ℝ => K * (Aψ t * P t - binv * ((((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * AM t) * Q t) := by
    filter_upwards [hpos, hlt] with t h0 h1
    exact hid t ⟨h0, h1⟩
  exact tendsto_nhds_unique (hlow.congr' hev) hR

private theorem mul_eq_of_low_of_high_of_add {K binv vl vh vol r A₀ m₀ q : ℂ}
    (hl : vl * r = K * (A₀ - binv * m₀ * q)) (hm : binv * m₀ = r) (hh : vh = K * q) (hvol : vol = vl + vh) :
    vol * r = K * A₀ := by
  linear_combination r * hvol + hl + r * hh - K * q * hm

private theorem tendsto_sub_mul_one_cpow_div_nhdsGT_zero :
    Tendsto (fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) *
      (((1 : ℝ) : ℂ) ^ (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) / (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  have hne : ((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2 ≠ 0 := by
    rw [add_sub_cancel_left, Ne, Complex.ofReal_eq_zero]
    exact (Set.mem_Ioi.mp ht).ne'
  show (1 : ℂ) = (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) *
    (((1 : ℝ) : ℂ) ^ (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) / (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2))
  rw [Complex.ofReal_one, Complex.one_cpow, mul_one_div, div_self hne]

private theorem tendsto_one_cpow_div_nhdsGT_zero :
    Tendsto (fun t : ℝ => ((1 : ℝ) : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) / (((1 / 2 : ℂ) + (t : ℂ)) + 1 / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => ((1 / 2 : ℂ) + (t : ℂ)) + 1 / 2) (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 2 : ℂ) + 0 + 1 / 2)) :=
    (tendsto_const_nhds.add tendsto_ofReal_nhdsGT_zero).add tendsto_const_nhds
  rw [add_zero, add_halves] at h1
  have h2 := Filter.Tendsto.div (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1)) h1
    one_ne_zero
  rw [div_one] at h2
  refine h2.congr' (eventually_nhdsWithin_of_forall fun t _ => ?_)
  show (1 : ℂ) / (((1 / 2 : ℂ) + (t : ℂ)) + 1 / 2) =
    ((1 : ℝ) : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) / (((1 / 2 : ℂ) + (t : ℂ)) + 1 / 2)
  rw [Complex.ofReal_one, Complex.one_cpow]

end ResidueLimitAlgebra

end AutomorphicForm.SlabCovolume

section SlabPairingGlue

variable (F : Type) [Field F] [NumberField F]

private def detSlab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

variable {F}

private theorem rationalTorusUnipotent_le_leftStabilizer_detSlab (d₁ d₂ : ℝ) :
    rationalTorusUnipotent F ≤ AutomorphicForm.SlabCovolume.leftStabilizer (detSlab F d₁ d₂) := by
  refine sup_le (AutomorphicForm.SlabCovolume.rationalTorus_le_map_borelSubgroup.trans ?_) ?_
  · rintro _ ⟨γ, -, rfl⟩
    show ∀ g : AdelicGL2 (𝓞 F) F, globalPoints (𝓞 F) F γ * g ∈ detSlab F d₁ d₂ ↔ g ∈ detSlab F d₁ d₂
    intro g
    simp only [detSlab, Set.mem_setOf_eq,
      AutomorphicForm.SlabCovolume.ideleNorm_det_globalPoints_mul ⟨globalPoints (𝓞 F) F γ, γ, rfl⟩ g]
  · rintro _ ⟨x, rfl⟩
    show ∀ g : AdelicGL2 (𝓞 F) F, unipotentGL2 x.toAdd * g ∈ detSlab F d₁ d₂ ↔ g ∈ detSlab F d₁ d₂
    intro g
    simp only [detSlab, Set.mem_setOf_eq, map_mul, AutomorphicForm.SlabCovolume.det_unipotentGL2_eq_one, one_mul]

private theorem measurableSet_setOf_ideleNorm_det_out_mem_Icc (d₁ d₂ : ℝ) :
    MeasurableSet {q : RationalTorusUnipotentQuotient F |
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂} := by
  refine measurableSet_quotient.2 ?_
  have hset : (Quotient.mk'' ⁻¹' {q : RationalTorusUnipotentQuotient F |
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det q.out) ∈ Set.Icc d₁ d₂})
      = detSlab F d₁ d₂ := by
    ext g
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1
      (Quotient.mk_out' (s₁ := MulAction.orbitRel (rationalTorusUnipotent F) (AdelicGL2 (𝓞 F) F)) g))
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hx, Subgroup.smul_def, smul_eq_mul]
    exact rationalTorusUnipotent_le_leftStabilizer_detSlab (F := F) d₁ d₂ x.2 g
  rw [hset]
  exact AutomorphicForm.SlabCovolume.measurableSet_setOf_ideleNorm_det_mem_Icc (F := F) d₁ d₂

variable (F)

private abbrev slabPins (Φ : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private theorem setIntegral_pseudoEisenstein_heightBand_eq_integral_indicator_slab_mul_indicator_band_mul :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (a b : ℝ) (_ha : 0 < a) (_hab : a < b)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b})
      (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
            (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}))
      (_hΦfin : adelicGLHaar (Fin 2) (𝓞 F) F Φ < ⊤)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ) (_hφc : Continuous φ)
      (R R' C : ℝ)
      (_hC : ∀ g : AdelicGL2 (𝓞 F) F,
        NumberField.AdelicHeight.adelicHeight F g ∈ Set.Ioc (Real.exp R) (Real.exp R') → ‖φ g‖ ≤ C),
    ∫ g in Φ, pseudoEisenstein F (AutomorphicForm.SlabCovolume.heightBand F (Real.exp R) (Real.exp R') φ) g
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫ q : RationalTorusUnipotentQuotient F,
          {g : AdelicGL2 (𝓞 F) F |
              NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
            (fun _ => (1 : ℂ)) q.out *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
            (NumberField.AdelicHeight.adelicHeight F q.out) *
          φ q.out
        ∂(rationalTorusUnipotentQuotientMeasure F) := by
  intro α hα a b ha hab Φ hΦs hΦ hΦfin s φ hφ hφc R R' C hC
  have hprof := AutomorphicForm.SlabCovolume.isSlabProfile_heightBand_of_isInducedSection_etaFst_etaSnd_one F
    (slabPins F Φ).Z α hα (isPrincipalTrivial_distribHaarChar_adeleRing F) s
    (NumberField.AdelicHeight.continuous_adelicHeight F).measurable
    (fun x g => AutomorphicForm.SlabCovolume.adelicHeight_unipotentGL2_mul hα x g)
    (fun _ hγ g => AutomorphicForm.SlabCovolume.adelicHeight_globalPoints_mul_of_mem_borelSubgroup hγ g)
    (fun z g => AutomorphicForm.SlabCovolume.adelicHeight_centralScalar_mul hα z g)
    hφ hφc.measurable (Real.exp_pos R) hC
  have h := AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab
    F a b ha hab Φ hΦs hΦ 1 (fun _ => (1 : ℂ)) (isAutomorphicFnAt_one_trivial F (slabPins F Φ) hΦfin) _ hprof
  have hL : (∫ g in Φ,
        pseudoEisenstein F (AutomorphicForm.SlabCovolume.heightBand F (Real.exp R) (Real.exp R') φ) g *
          (starRingEnd ℂ) (1 : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F))
      = ∫ g in Φ, pseudoEisenstein F (AutomorphicForm.SlabCovolume.heightBand F (Real.exp R) (Real.exp R') φ) g
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    simp only [map_one, mul_one]
  refine hL.symm.trans (h.trans ?_)
  rw [← integral_indicator (measurableSet_setOf_ideleNorm_det_out_mem_Icc (F := F) a b)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [AutomorphicForm.SlabCovolume.heightBand_apply, Set.indicator_apply, Set.mem_setOf_eq]
  erw [constantTerm_cond_adelicBox_const]
  rw [map_one, mul_one]
  split_ifs <;> simp

end SlabPairingGlue

section SlabShellDoubleIntegral

open Filter Set

private theorem setIntegral_Ioi_const_mul (c : ℂ) (f : ℝ → ℂ) :
    ∫ y in Ioi (0 : ℝ), c * f y = c * ∫ y in Ioi (0 : ℝ), f y :=
  integral_const_mul c f

private theorem setIntegral_Ioi_mul_const (c : ℂ) (f : ℝ → ℂ) :
    ∫ y in Ioi (0 : ℝ), f y * c = (∫ y in Ioi (0 : ℝ), f y) * c :=
  integral_mul_const c f

private theorem measurable_cpow_mul_indicator_slab_mul_indicator_shell_mul_inv {a b x₁ x₂ : ℝ} (e : ℂ) (y : ℝ) :
    Measurable fun u : ℝ => (u : ℂ) ^ e * (Icc a b).indicator (fun _ => (1 : ℂ)) (y ^ 2 * u) *
      (Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) u * ((u⁻¹ : ℝ) : ℂ) :=
  (((Complex.measurable_ofReal.pow_const e).mul
      ((measurable_const.indicator measurableSet_Icc).comp (measurable_id.const_mul (y ^ 2)))).mul
    (measurable_const.indicator measurableSet_Ioc)).mul (Complex.measurable_ofReal.comp measurable_inv)

private theorem measurable_const_mul_integral_inv_mul_cpow_mul_indicator_slab_mul_indicator_shell
    {a b x₁ x₂ : ℝ} (e : ℂ) (W : ℂ) :
    Measurable fun y : ℝ => W * ∫ u in Ioi (0 : ℝ), ((u : ℂ))⁻¹ *
      ((u : ℂ) ^ e * (Icc a b).indicator (fun _ => (1 : ℂ)) (y ^ 2 * u) *
        (Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) u * ((u⁻¹ : ℝ) : ℂ)) := by
  have hj : Measurable fun p : ℝ × ℝ => ((p.2 : ℂ))⁻¹ *
      ((p.2 : ℂ) ^ e * (Icc a b).indicator (fun _ => (1 : ℂ)) (p.1 ^ 2 * p.2) *
        (Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) p.2 * ((p.2⁻¹ : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp measurable_snd).inv.mul
      (((((Complex.measurable_ofReal.comp measurable_snd).pow_const e).mul
          ((measurable_const.indicator measurableSet_Icc).comp ((measurable_fst.pow_const 2).mul measurable_snd))).mul
        ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)).mul
        (Complex.measurable_ofReal.comp measurable_snd.inv))
  exact measurable_const.mul hj.stronglyMeasurable.integral_prod_right'.measurable

private theorem integral_inv_mul_integral_inv_mul_cpow_mul_indicator_slab_mul_indicator_shell
    {a b x₁ x₂ : ℝ} (ha : 0 < a) (hx₁ : 0 < x₁) (hx : x₁ ≤ x₂) (e W : ℂ)
    (hslab : ∀ {c : ℝ}, 0 < c →
      ∫ y in Ioi (0 : ℝ), ((y : ℂ))⁻¹ * (Icc a b).indicator (fun _ => (1 : ℂ)) (y ^ 2 * c)
        = ((Real.log (b / a) / 2 : ℝ) : ℂ))
    (hshell : ∫ y in Ioi (0 : ℝ),
        ((y : ℂ))⁻¹ * ((Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) y * ((y : ℂ) ^ e * ((y⁻¹ : ℝ) : ℂ)))
      = ((x₂ : ℂ) ^ (e - 1) - (x₁ : ℂ) ^ (e - 1)) / (e - 1)) :
    ∫ y in Ioi (0 : ℝ), ((y : ℂ))⁻¹ *
        (W * ∫ u in Ioi (0 : ℝ), ((u : ℂ))⁻¹ *
          ((u : ℂ) ^ e * (Icc a b).indicator (fun _ => (1 : ℂ)) (y ^ 2 * u) *
            (Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) u * ((u⁻¹ : ℝ) : ℂ)))
      = W * (((Real.log (b / a) / 2 : ℝ) : ℂ) * (((x₂ : ℂ) ^ (e - 1) - (x₁ : ℂ) ^ (e - 1)) / (e - 1))) := by

  let H : ℝ × ℝ → ℂ := fun p => ((p.1 : ℂ))⁻¹ * (((p.2 : ℂ))⁻¹ *
    ((p.2 : ℂ) ^ e * (Icc a b).indicator (fun _ => (1 : ℂ)) (p.1 ^ 2 * p.2) *
      (Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) p.2 * ((p.2⁻¹ : ℝ) : ℂ)))

  let B : ℝ × ℝ → ℂ := fun p => ((p.1 : ℂ))⁻¹ * (((p.2 : ℂ))⁻¹ * ((p.2 : ℂ) ^ e * ((p.2⁻¹ : ℝ) : ℂ)))
  let K : Set (ℝ × ℝ) := Icc (Real.sqrt (a / x₂)) (Real.sqrt (b / x₁)) ×ˢ Icc x₁ x₂
  have hx₂ : 0 < x₂ := hx₁.trans_le hx
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc

  have hHB : ∀ p : ℝ × ℝ, 0 < p.1 → H p = 0 ∨ (H p = B p ∧ p ∈ K) := by
    rintro ⟨y, u⟩ (hy : 0 < y)
    by_cases h₁ : y ^ 2 * u ∈ Icc a b
    · by_cases h₂ : u ∈ Ioc x₁ x₂
      · refine Or.inr ⟨?_, ?_⟩
        · simp only [H, B, indicator_of_mem h₁, indicator_of_mem h₂, mul_one]
        · have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
          refine ⟨⟨?_, ?_⟩, h₂.1.le, h₂.2⟩
          · rw [← Real.sqrt_sq hy.le]
            refine Real.sqrt_le_sqrt ((div_le_iff₀ hx₂).2 ?_)
            exact h₁.1.trans (mul_le_mul_of_nonneg_left h₂.2 hy2)
          · rw [← Real.sqrt_sq hy.le]
            refine Real.sqrt_le_sqrt ((le_div_iff₀ hx₁).2 ?_)
            exact (mul_le_mul_of_nonneg_left h₂.1.le hy2).trans h₁.2
      · exact Or.inl (by simp [H, indicator_of_notMem h₂])
    · exact Or.inl (by simp [H, indicator_of_notMem h₁])

  have hBc : ContinuousOn B K := by
    intro p hp
    have hp1 : (0 : ℝ) < p.1 := lt_of_lt_of_le (Real.sqrt_pos.2 (div_pos ha hx₂)) hp.1.1
    have hp2 : (0 : ℝ) < p.2 := lt_of_lt_of_le hx₁ hp.2.1
    apply ContinuousAt.continuousWithinAt
    have h1 : ContinuousAt (fun q : ℝ × ℝ => ((q.1 : ℂ))⁻¹) p :=
      ((Complex.continuous_ofReal.comp continuous_fst).continuousAt).inv₀
        (Complex.ofReal_ne_zero.2 hp1.ne')
    have h2 : ContinuousAt (fun q : ℝ × ℝ => ((q.2 : ℂ))⁻¹) p :=
      ((Complex.continuous_ofReal.comp continuous_snd).continuousAt).inv₀
        (Complex.ofReal_ne_zero.2 hp2.ne')
    have h3 : ContinuousAt (fun q : ℝ × ℝ => (q.2 : ℂ) ^ e) p :=
      (Complex.continuousAt_ofReal_cpow_const p.2 e (Or.inr hp2.ne')).comp continuous_snd.continuousAt
    have h4 : ContinuousAt (fun q : ℝ × ℝ => ((q.2⁻¹ : ℝ) : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp (continuous_snd.continuousAt.inv₀ hp2.ne')
    exact h1.mul (h2.mul (h3.mul h4))
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hBc

  have hHm : Measurable H := by
    have m1 : Measurable fun p : ℝ × ℝ => ((p.1 : ℂ))⁻¹ := (Complex.measurable_ofReal.comp measurable_fst).inv
    have m2 : Measurable fun p : ℝ × ℝ => ((p.2 : ℂ))⁻¹ := (Complex.measurable_ofReal.comp measurable_snd).inv
    have m3 : Measurable fun p : ℝ × ℝ => (p.2 : ℂ) ^ e := (Complex.measurable_ofReal.comp measurable_snd).pow_const e
    have m4 : Measurable fun p : ℝ × ℝ => (Icc a b).indicator (fun _ => (1 : ℂ)) (p.1 ^ 2 * p.2) :=
      (measurable_const.indicator measurableSet_Icc).comp ((measurable_fst.pow_const 2).mul measurable_snd)
    have m5 : Measurable fun p : ℝ × ℝ => (Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) p.2 :=
      (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
    have m6 : Measurable fun p : ℝ × ℝ => ((p.2⁻¹ : ℝ) : ℂ) := Complex.measurable_ofReal.comp measurable_snd.inv
    exact m1.mul (m2.mul (((m3.mul m4).mul m5).mul m6))

  have hHi : Integrable H ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Integrable.mono' (g := K.indicator fun _ => M) ?_ hHm.aestronglyMeasurable ?_
    · rw [integrable_indicator_iff hKm]
      exact integrableOn_const hKc.measure_lt_top.ne
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
      rcases hHB p hp.1 with h0 | ⟨hB, hK⟩
      · rw [h0, norm_zero]
        by_cases hpK : p ∈ K
        · rw [indicator_of_mem hpK]; exact (norm_nonneg _).trans (hM p hpK)
        · rw [indicator_of_notMem hpK]
      · rw [hB, indicator_of_mem hK]; exact hM p hK

  have hswap : (∫ y in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), H (y, u)) = ∫ u in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), H (y, u) :=
    integral_integral_swap (f := fun y u => H (y, u)) hHi

  have hW : ∀ y : ℝ, ((y : ℂ))⁻¹ *
      (W * ∫ u in Ioi (0 : ℝ), ((u : ℂ))⁻¹ *
        ((u : ℂ) ^ e * (Icc a b).indicator (fun _ => (1 : ℂ)) (y ^ 2 * u) *
          (Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) u * ((u⁻¹ : ℝ) : ℂ)))
        = W * ∫ u in Ioi (0 : ℝ), H (y, u) := by
    intro y
    simp only [H]
    rw [setIntegral_Ioi_const_mul ((y : ℂ))⁻¹]
    ring
  simp only [hW]
  rw [setIntegral_Ioi_const_mul W]
  congr 1
  calc
    ∫ y in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), H (y, u)
    _ = ∫ u in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), H (y, u) := hswap
    _ = ∫ u in Ioi (0 : ℝ),
          (((u : ℂ))⁻¹ * ((Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) u * ((u : ℂ) ^ e * ((u⁻¹ : ℝ) : ℂ)))) *
            ((Real.log (b / a) / 2 : ℝ) : ℂ) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
          have hpt : ∀ y : ℝ, H (y, u) =
              (((u : ℂ))⁻¹ * ((Ioc x₁ x₂).indicator (fun _ => (1 : ℂ)) u * ((u : ℂ) ^ e * ((u⁻¹ : ℝ) : ℂ)))) *
                (((y : ℂ))⁻¹ * (Icc a b).indicator (fun _ => (1 : ℂ)) (y ^ 2 * u)) := by
            intro y; simp only [H]; ring
          simp only [hpt]
          rw [setIntegral_Ioi_const_mul, hslab hu]
    _ = ((Real.log (b / a) / 2 : ℝ) : ℂ) * (((x₂ : ℂ) ^ (e - 1) - (x₁ : ℂ) ^ (e - 1)) / (e - 1)) := by
          rw [setIntegral_Ioi_mul_const, hshell, mul_comm]

end SlabShellDoubleIntegral

section BandedSlabShellValue

variable (F : Type) [Field F] [NumberField F]

private theorem isUnitaryChar_one_trivial : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :=
  fun _ => by simp

private theorem etaFst_one_mul_mul_etaSnd_one (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (s : ℂ) (z t : (AdeleRing (𝓞 F) F)ˣ) :
    etaFst 1 α hα s (z * t) * etaSnd 1 α hα s z = etaFst 1 α hα s t := by
  rw [map_mul, mul_right_comm, etaFst_mul_etaSnd]
  simp

private theorem val_etaFst_one_apply (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaFst 1 α hα s t : ℂˣ) : ℂ) = (((α t : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) := by
  rw [etaFst_apply]
  simp

private theorem val_etaFst_one_neg_half (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaFst 1 α hα (-(1 / 2 : ℂ)) t : ℂˣ) : ℂ) = 1 := by
  rw [val_etaFst_one_apply]
  simp

private theorem etaBlock_one_one_eq_cpow (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (s : ℂ) (z t : (AdeleRing (𝓞 F) F)ˣ) :
    ((etaFst 1 α hα s (z * t) : ℂˣ) : ℂ) * ((etaSnd 1 α hα s z : ℂˣ) : ℂ) *
        (starRingEnd ℂ) (((etaFst 1 α hα (-(1 / 2 : ℂ)) (z * t) : ℂˣ) : ℂ) *
          ((etaSnd 1 α hα (-(1 / 2 : ℂ)) z : ℂˣ) : ℂ))
      = (((α t : ℝˣ) : ℝ) : ℂ) ^ (s + 1 / 2) := by
  rw [← Units.val_mul, ← Units.val_mul, etaFst_one_mul_mul_etaSnd_one, etaFst_one_mul_mul_etaSnd_one,
    val_etaFst_one_neg_half, map_one, mul_one, val_etaFst_one_apply]

private theorem val_modulusHom_apply (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits t : ℝˣ) : ℝ)
      = NumberField.TateGlobal.ideleNorm F t :=
  rfl

private theorem integral_indicator_slab_mul_indicator_shell_mul_section_eq_mul_log_mul_cpow_sub_div :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (c : ℝ≥0∞) (_hc_top : c ≠ ∞)
      (_hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
        ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
          (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
          ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
            c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                  f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
                ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
      (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (V : ℝ≥0∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
      (s : ℂ) (_hs : s ≠ (1 / 2 : ℂ))
      (φ : AdelicGL2 (𝓞 F) F → ℂ) (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (_hφc : Continuous φ)
      (a b R R' : ℝ) (_ha : 0 < a) (_hab : a ≤ b) (_hRR' : R ≤ R'),
    ∫ q : RationalTorusUnipotentQuotient F,
        {g : AdelicGL2 (𝓞 F) F |
            NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}.indicator
          (fun _ => (1 : ℂ)) q.out *
        (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ))
          (NumberField.AdelicHeight.adelicHeight F q.out) *
        φ q.out
      ∂(rationalTorusUnipotentQuotientMeasure F)
      = (c.toReal : ℂ) * (∫ k, φ (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) *
        ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (b / a) / 2 : ℝ) : ℂ) *
        (((Real.exp R' : ℝ) : ℂ) ^ (s - 1 / 2) - ((Real.exp R : ℝ) : ℂ) ^ (s - 1 / 2)) / (s - 1 / 2) := by
  intro α hα c hc_top hc D hDm hDF V hV s hs φ hφ hφc a b R R' ha hab hRR'
  have h1u : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := isUnitaryChar_one_trivial F
  have h1F : IsIdeleClassChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) :=
    AutomorphicForm.SlabCovolume.isIdeleClassChar_one F
  obtain ⟨-, heq⟩ :=
    AutomorphicForm.integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa F hα c
      hc_top hc D D hDm hDm hDF hDF 1 1 1 1 h1u h1u h1u h1u h1F h1F h1F h1F s (-(1 / 2 : ℂ)) φ (fun _ => (1 : ℂ))
      hφ (isInducedSection_etaFst_etaSnd_one_neg_half_const_one F α hα) hφc continuous_const a b R R' ha
  simp only [map_one, mul_one] at heq
  refine heq.trans ?_
  simp only [etaBlock_one_one_eq_cpow, val_modulusHom_apply]
  have hN : Measurable (NumberField.TateGlobal.ideleNorm F) :=
    (NumberField.TateGlobal.continuous_ideleNorm F).measurable
  have hin := fun z : (AdeleRing (𝓞 F) F)ˣ =>
    NormDisintegration.setIntegral_comp_eq_toReal_mul (NumberField.Idele.idelicHaar F) D
      (NumberField.TateGlobal.ideleNorm F) hN V hV
      (fun u : ℝ => (u : ℂ) ^ (s + 1 / 2) *
        (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (NumberField.TateGlobal.ideleNorm F z ^ 2 * u) *
        (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) u * ((u⁻¹ : ℝ) : ℂ))
      (measurable_cpow_mul_indicator_slab_mul_indicator_shell_mul_inv (s + 1 / 2) _)
  simp only [hin]
  have hout :=
    NormDisintegration.setIntegral_comp_eq_toReal_mul (NumberField.Idele.idelicHaar F) D
      (NumberField.TateGlobal.ideleNorm F) hN V hV
      (fun y : ℝ => (V.toReal : ℂ) * ∫ u in Set.Ioi (0 : ℝ), ((u : ℂ))⁻¹ *
        ((u : ℂ) ^ (s + 1 / 2) * (Set.Icc a b).indicator (fun _ => (1 : ℂ)) (y ^ 2 * u) *
          (Set.Ioc (Real.exp R) (Real.exp R')).indicator (fun _ => (1 : ℂ)) u * ((u⁻¹ : ℝ) : ℂ)))
      (measurable_const_mul_integral_inv_mul_cpow_mul_indicator_slab_mul_indicator_shell (s + 1 / 2) _)
  rw [hout]
  have he : s + 1 / 2 ≠ 1 := fun h => hs (by linear_combination h)
  rw [integral_inv_mul_integral_inv_mul_cpow_mul_indicator_slab_mul_indicator_shell ha (Real.exp_pos R)
    (Real.exp_le_exp.2 hRR') (s + 1 / 2) (V.toReal : ℂ)
    (fun hu => ShellIntegrals.setIntegral_inv_mul_indicator_slab_sq_mul ha hab hu)
    (ShellIntegrals.setIntegral_inv_mul_indicator_shell_mul_cpow_mul_inv (Real.exp_pos R) (Real.exp_le_exp.2 hRR') he)]
  have hexp : s + 1 / 2 - 1 = s - 1 / 2 := by ring
  rw [hexp]
  ring

end BandedSlabShellValue

section HighShellMajorant

p2m_open "NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc NumberField.AdelicHeight~adelicHeight_diagOne_mul"

variable {F : Type} [Field F] [NumberField F]

private abbrev shellRegion (T d₁ d₂ : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | T < p.2 ∧ p.1 ^ 2 * p.2 ∈ Set.Icc d₁ d₂}

private abbrev shellWeight (e : ℝ) : ℝ × ℝ → ℝ≥0∞ :=
  fun p => ENNReal.ofReal (p.2 ^ e)

private theorem measurable_shellWeight (e : ℝ) : Measurable (shellWeight e) :=
  (measurable_snd.pow_const e).ennreal_ofReal

private theorem measurableSet_shellRegion (T d₁ d₂ : ℝ) :
    MeasurableSet (shellRegion T d₁ d₂) :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (((measurable_fst.pow_const 2).mul measurable_snd) measurableSet_Icc)

private theorem measurable_shellIntegrand (T d₁ d₂ e : ℝ) (M : ℝ≥0∞) :
    Measurable fun p : ℝ × ℝ =>
      (shellRegion T d₁ d₂).indicator (shellWeight e) p *
        ENNReal.ofReal p.2⁻¹ * M * ENNReal.ofReal p.2⁻¹ :=
  ((((measurable_shellWeight e).indicator (measurableSet_shellRegion T d₁ d₂)).mul
    measurable_snd.inv.ennreal_ofReal).mul measurable_const).mul measurable_snd.inv.ennreal_ofReal

private theorem lintegral_indicator_sqrt_shell_le {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) {y : ℝ} (hy : 0 < y) :
    ∫⁻ a in Set.Ioi (0 : ℝ),
        (Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y))).indicator
          (fun _ => ENNReal.ofReal (Real.sqrt (d₁ / y))⁻¹) a
      ≤ ENNReal.ofReal (Real.sqrt (|d₂| / d₁)) := by
  have hα : 0 < Real.sqrt (d₁ / y) := Real.sqrt_pos.2 (div_pos hd₁ hy)
  calc ∫⁻ a in Set.Ioi (0 : ℝ), (Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y))).indicator
          (fun _ => ENNReal.ofReal (Real.sqrt (d₁ / y))⁻¹) a
      ≤ ∫⁻ a, (Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y))).indicator
          (fun _ => ENNReal.ofReal (Real.sqrt (d₁ / y))⁻¹) a :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (Real.sqrt (d₁ / y))⁻¹ * ENNReal.ofReal (Real.sqrt (d₂ / y) - Real.sqrt (d₁ / y)) := by
        rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
    _ ≤ ENNReal.ofReal (Real.sqrt (d₁ / y))⁻¹ * ENNReal.ofReal (Real.sqrt (|d₂| / y)) := by
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
        refine (sub_le_self _ (Real.sqrt_nonneg _)).trans (Real.sqrt_le_sqrt ?_)
        exact div_le_div_of_nonneg_right (le_abs_self d₂) hy.le
    _ = ENNReal.ofReal (Real.sqrt (|d₂| / d₁)) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hα.le), ← div_eq_inv_mul,
          ← Real.sqrt_div (div_nonneg (abs_nonneg d₂) hy.le)]
        congr 2
        field_simp

private theorem lintegral_lintegral_shell_indicator_rpow_lt_top {e T d₁ d₂ : ℝ} (he : e < 1) (hT : 0 < T)
    (hd₁ : 0 < d₁) {M V : ℝ≥0∞} (hM : M ≠ ∞) (hV : V ≠ ∞) :
    ∫⁻ a in Set.Ioi (0 : ℝ),
        (V * ∫⁻ y in Set.Ioi (0 : ℝ),
          (shellRegion T d₁ d₂).indicator (shellWeight e) (a, y) *
              ENNReal.ofReal y⁻¹ * M * ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹
      < ∞ := by

  set φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (y ^ e) * ENNReal.ofReal y⁻¹ * M * ENNReal.ofReal y⁻¹ with hφ
  have hmeas : Measurable fun p : ℝ × ℝ =>
      (shellRegion T d₁ d₂).indicator (shellWeight e) p *
          ENNReal.ofReal p.2⁻¹ * M * ENNReal.ofReal p.2⁻¹ * ENNReal.ofReal p.1⁻¹ :=
    (measurable_shellIntegrand T d₁ d₂ e M).mul measurable_fst.inv.ennreal_ofReal
  have hpt : ∀ a ∈ Set.Ioi (0 : ℝ), ∀ y : ℝ,
      (shellRegion T d₁ d₂).indicator (shellWeight e) (a, y) *
          ENNReal.ofReal y⁻¹ * M * ENNReal.ofReal y⁻¹ * ENNReal.ofReal a⁻¹
        ≤ (Set.Ioi T).indicator φ y *
            (Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y))).indicator
              (fun _ => ENNReal.ofReal (Real.sqrt (d₁ / y))⁻¹) a := by
    intro a ha y
    by_cases hmem : (a, y) ∈ shellRegion T d₁ d₂
    · obtain ⟨hTy, hlo, hhi⟩ := id hmem
      have hy : 0 < y := hT.trans hTy
      have ha0 : (0 : ℝ) < a := ha
      have h₁ : Real.sqrt (d₁ / y) ≤ a := by
        rw [← Real.sqrt_sq ha0.le]
        exact Real.sqrt_le_sqrt ((div_le_iff₀ hy).2 hlo)
      have h₂ : a ≤ Real.sqrt (d₂ / y) := by
        rw [← Real.sqrt_sq ha0.le]
        exact Real.sqrt_le_sqrt ((le_div_iff₀ hy).2 hhi)
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (Set.mem_Ioi.2 hTy),
        Set.indicator_of_mem (Set.mem_Icc.2 ⟨h₁, h₂⟩)]
      exact mul_le_mul_right
        (ENNReal.ofReal_le_ofReal (inv_anti₀ (Real.sqrt_pos.2 (div_pos hd₁ hy)) h₁)) _
    · rw [Set.indicator_of_notMem hmem]
      simp

  have htail : ∫⁻ y in Set.Ioi T, φ y < ∞ := by
    have hcongr : ∀ y ∈ Set.Ioi T, φ y = M * ENNReal.ofReal (y ^ (e - 2)) := by
      intro y hy
      have hy0 : 0 < y := hT.trans hy
      have hsplit : y ^ (e - 2) = y ^ e * y⁻¹ * y⁻¹ := by
        rw [Real.rpow_sub hy0, Real.rpow_two, div_eq_mul_inv, sq, mul_inv, ← mul_assoc]
      rw [hφ, hsplit, ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hy0.le e) (inv_nonneg.2 hy0.le)),
        ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le e)]
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr, lintegral_const_mul' _ _ hM]
    refine ENNReal.mul_lt_top hM.lt_top ?_
    have hfin := (integrableOn_Ioi_rpow_of_lt (by linarith : e - 2 < -1) hT).2
    rwa [HasFiniteIntegral, lintegral_enorm_of_ae_nonneg
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => Real.rpow_nonneg (hT.trans hy).le _)] at hfin

  have hrw : ∀ a : ℝ,
      (V * ∫⁻ y in Set.Ioi (0 : ℝ),
        (shellRegion T d₁ d₂).indicator (shellWeight e) (a, y) *
            ENNReal.ofReal y⁻¹ * M * ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹
      = V * ∫⁻ y in Set.Ioi (0 : ℝ),
          (shellRegion T d₁ d₂).indicator (shellWeight e) (a, y) *
            ENNReal.ofReal y⁻¹ * M * ENNReal.ofReal y⁻¹ * ENNReal.ofReal a⁻¹ := by
    intro a
    rw [mul_assoc, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  simp_rw [hrw]
  rw [lintegral_const_mul' _ _ hV]
  refine ENNReal.mul_lt_top hV.lt_top ?_
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ y in Set.Ioi (0 : ℝ), ∫⁻ a in Set.Ioi (0 : ℝ),
          (shellRegion T d₁ d₂).indicator (shellWeight e) (a, y) *
            ENNReal.ofReal y⁻¹ * M * ENNReal.ofReal y⁻¹ * ENNReal.ofReal a⁻¹
      ≤ ∫⁻ y in Set.Ioi (0 : ℝ), (Set.Ioi T).indicator φ y * ENNReal.ofReal (Real.sqrt (|d₂| / d₁)) := by
        refine lintegral_mono fun y => ?_
        calc ∫⁻ a in Set.Ioi (0 : ℝ),
                (shellRegion T d₁ d₂).indicator (shellWeight e)
                    (a, y) * ENNReal.ofReal y⁻¹ * M * ENNReal.ofReal y⁻¹ * ENNReal.ofReal a⁻¹
            ≤ ∫⁻ a in Set.Ioi (0 : ℝ), (Set.Ioi T).indicator φ y *
                (Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y))).indicator
                  (fun _ => ENNReal.ofReal (Real.sqrt (d₁ / y))⁻¹) a :=
              setLIntegral_mono' measurableSet_Ioi fun a ha => hpt a ha y
          _ = (Set.Ioi T).indicator φ y * ∫⁻ a in Set.Ioi (0 : ℝ),
                (Set.Icc (Real.sqrt (d₁ / y)) (Real.sqrt (d₂ / y))).indicator
                  (fun _ => ENNReal.ofReal (Real.sqrt (d₁ / y))⁻¹) a :=
              lintegral_const_mul'' _ (measurable_const.indicator measurableSet_Icc).aemeasurable
          _ ≤ (Set.Ioi T).indicator φ y * ENNReal.ofReal (Real.sqrt (|d₂| / d₁)) := by
              by_cases hy : y ∈ Set.Ioi T
              · exact mul_le_mul_right (lintegral_indicator_sqrt_shell_le hd₁ (hT.trans hy)) _
              · rw [Set.indicator_of_notMem hy]
                simp
    _ ≤ ∫⁻ y, (Set.Ioi T).indicator φ y * ENNReal.ofReal (Real.sqrt (|d₂| / d₁)) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = (∫⁻ y in Set.Ioi T, φ y) * ENNReal.ofReal (Real.sqrt (|d₂| / d₁)) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioi]
    _ < ∞ := ENNReal.mul_lt_top htail ENNReal.ofReal_lt_top

private theorem lintegral_indicator_sq_mul_mul_ofReal_inv {d₁ d₂ c₀ : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂) (hc₀ : 0 < c₀) :
    ∫⁻ y in Set.Ioi (0 : ℝ), (Set.Icc d₁ d₂).indicator 1 (y ^ 2 * c₀) * ENNReal.ofReal y⁻¹
      = ENNReal.ofReal (Real.log (d₂ / d₁) / 2) := by
  have hl : 0 < Real.sqrt (d₁ / c₀) := Real.sqrt_pos.mpr (div_pos hd₁ hc₀)
  have hu : 0 < Real.sqrt (d₂ / c₀) := Real.sqrt_pos.mpr (div_pos (hd₁.trans_le hd) hc₀)
  have hlu : Real.sqrt (d₁ / c₀) ≤ Real.sqrt (d₂ / c₀) := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hd hc₀.le)
  have hpt : ∀ y ∈ Set.Ioi (0 : ℝ),
      (Set.Icc d₁ d₂).indicator 1 (y ^ 2 * c₀) * ENNReal.ofReal y⁻¹
        = (Set.Icc (Real.sqrt (d₁ / c₀)) (Real.sqrt (d₂ / c₀))).indicator (fun y : ℝ => ENNReal.ofReal y⁻¹) y := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    have hmem : y ^ 2 * c₀ ∈ Set.Icc d₁ d₂ ↔ y ∈ Set.Icc (Real.sqrt (d₁ / c₀)) (Real.sqrt (d₂ / c₀)) := by
      simp only [Set.mem_Icc]
      rw [Real.sqrt_le_left hy'.le, Real.le_sqrt hy'.le (div_pos (hd₁.trans_le hd) hc₀).le, div_le_iff₀ hc₀,
        le_div_iff₀ hc₀]
    by_cases h : y ^ 2 * c₀ ∈ Set.Icc d₁ d₂
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h), Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.mpr h')), zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr (show Set.Icc (Real.sqrt (d₁ / c₀)) (Real.sqrt (d₂ / c₀)) ⊆ Set.Ioi (0 : ℝ) from
      fun y hy => hl.trans_le hy.1),
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlu, integral_inv_of_pos hl hu,
      ← Real.sqrt_div (div_pos (hd₁.trans_le hd) hc₀).le, Real.log_sqrt (div_nonneg (div_pos (hd₁.trans_le hd) hc₀).le
        (div_pos hd₁ hc₀).le)]
    congr 3
    field_simp
  · exact (continuousOn_inv₀.mono fun y hy => (hl.trans_le hy.1).ne').integrableOn_compact isCompact_Icc
  · exact ae_restrict_of_forall_mem measurableSet_Icc fun y hy => inv_nonneg.2 (hl.trans_le hy.1).le

private theorem lintegral_indicator_Ioi_mul_ofReal_rpow {T e : ℝ} (hT : 0 < T) (he : e < 1) :
    ∫⁻ y in Set.Ioi (0 : ℝ), (Set.Ioi T).indicator 1 y * ENNReal.ofReal (y ^ (e - 2))
      = ENNReal.ofReal (T ^ (e - 1) / (1 - e)) := by
  have hpt : ∀ y : ℝ, (Set.Ioi T).indicator 1 y * ENNReal.ofReal (y ^ (e - 2))
      = (Set.Ioi T).indicator (fun y : ℝ => ENNReal.ofReal (y ^ (e - 2))) y := by
    intro y
    by_cases h : y ∈ Set.Ioi T
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  simp_rw [hpt]
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, Set.Ioi_inter_Ioi,
    max_eq_left hT.le, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by linarith) hT)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => Real.rpow_nonneg (hT.trans hy).le _),
    integral_Ioi_rpow_of_lt (by linarith) hT]
  congr 1
  have h21 : e - 2 + 1 = e - 1 := by ring
  rw [h21, neg_div, ← div_neg, neg_sub]

private theorem lintegral_indicator_Ioc_mul_ofReal_rpow {T e : ℝ} (hT : 0 < T) (he : 1 < e) :
    ∫⁻ y in Set.Ioi (0:ℝ), (Set.Ioc 0 T).indicator 1 y * ENNReal.ofReal (y ^ (e - 2))
      = ENNReal.ofReal (T ^ (e - 1) / (e - 1)) := by
  have hpt : ∀ y : ℝ, (Set.Ioc 0 T).indicator 1 y * ENNReal.ofReal (y ^ (e - 2))
      = (Set.Ioc 0 T).indicator (fun y : ℝ => ENNReal.ofReal (y ^ (e - 2))) y := by
    intro y
    by_cases h : y ∈ Set.Ioc 0 T
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
  simp_rw [hpt]
  rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.mpr (show Set.Ioc (0 : ℝ) T ⊆ Set.Ioi 0 from fun _ hy => hy.1),
    ← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1
      (ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => Real.rpow_nonneg hy.1.le _),
    ← intervalIntegral.integral_of_le hT.le, integral_rpow (Or.inl (by linarith))]
  congr 1
  have h21 : e - 2 + 1 = e - 1 := by ring
  rw [h21, Real.zero_rpow (by linarith), sub_zero]

private theorem lintegral_indicator_Ioc_mul_ofReal_rpow_lt_top {T e : ℝ} (hT : 0 < T) (he : 1 < e) :
    ∫⁻ y in Set.Ioi (0:ℝ), (Set.Ioc 0 T).indicator 1 y * ENNReal.ofReal (y ^ (e - 2)) < ⊤ := by
  rw [lintegral_indicator_Ioc_mul_ofReal_rpow hT he]
  exact ENNReal.ofReal_lt_top

private theorem lintegral_indicator_rpow_adelicHeight_out_lt_top (c : ℝ≥0∞) (hcT : c ≠ ∞)
    (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
      ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
          c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (V : ℝ≥0∞) (hVT : V ≠ ∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hHm : Measurable (adelicHeight F))
    (hHinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, adelicHeight F (x * g) = adelicHeight F g)
    (hH : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      adelicHeight F (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) = ideleNorm F t)
    (hN : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        ideleNorm F z ^ 2 * ideleNorm F t)
    {σ T d₁ d₂ : ℝ} (hσ : -(1 / 2) < σ) (hT : 0 < T) (hd₁ : 0 < d₁)
    {Ω : Set (AdelicGL2 (𝓞 F) F)} (hΩm : MeasurableSet Ω)
    (hΩinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ Ω ↔ g ∈ Ω)
    (hΩ : ∀ g ∈ Ω, T < adelicHeight F g ∧ ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂) :
    ∫⁻ q, Ω.indicator (fun g => ENNReal.ofReal (adelicHeight F g ^ (1 / 2 - σ))) q.out
        ∂(rationalTorusUnipotentQuotientMeasure F) < ∞ := by
  have he : (1 / 2 - σ : ℝ) < 1 := by linarith
  have hfm : Measurable (Ω.indicator (fun g => ENNReal.ofReal (adelicHeight F g ^ (1 / 2 - σ)))) :=
    ((hHm.pow_const _).ennreal_ofReal).indicator hΩm
  have hfinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      Ω.indicator (fun g => ENNReal.ofReal (adelicHeight F g ^ (1 / 2 - σ))) (x * g)
        = Ω.indicator (fun g => ENNReal.ofReal (adelicHeight F g ^ (1 / 2 - σ))) g := by
    intro x hx g
    by_cases hg : g ∈ Ω
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hΩinv x hx g).2 hg)]
      simp only [hHinv x hx g]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hΩinv x hx g).1 h))]
  rw [hc D D hDm hDm hDF hDF _ hfm hfinv]
  refine ENNReal.mul_lt_top hcT.lt_top ?_
  have hpt : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      Ω.indicator (fun g => ENNReal.ofReal (adelicHeight F g ^ (1 / 2 - σ)))
            (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          ENNReal.ofReal ((ideleNorm F t)⁻¹)
        ≤ (shellRegion T d₁ d₂).indicator (shellWeight (1 / 2 - σ)) (ideleNorm F z, ideleNorm F t) *
            ENNReal.ofReal ((ideleNorm F t)⁻¹) := by
    intro z t k
    refine mul_le_mul_left ?_ _
    by_cases hg : centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F) ∈ Ω
    · obtain ⟨h₁, h₂⟩ := hΩ _ hg
      rw [hH] at h₁
      rw [hN] at h₂
      rw [Set.indicator_of_mem hg,
        Set.indicator_of_mem (show (ideleNorm F z, ideleNorm F t) ∈ shellRegion T d₁ d₂ from ⟨h₁, h₂⟩)]
      simp only [shellWeight, hH, le_refl]
    · rw [Set.indicator_of_notMem hg]
      simp
  have hf₁ : ∀ a : ℝ, Measurable fun y : ℝ =>
      (shellRegion T d₁ d₂).indicator (shellWeight (1 / 2 - σ)) (a, y) * ENNReal.ofReal y⁻¹ *
        (maximalCompactHaar F) Set.univ := fun a =>
    ((((measurable_shellWeight _).indicator (measurableSet_shellRegion T d₁ d₂)).comp
      (measurable_const.prodMk measurable_id)).mul measurable_inv.ennreal_ofReal).mul measurable_const
  have hf₂ : Measurable fun a : ℝ => V * ∫⁻ y in Set.Ioi (0 : ℝ),
      (shellRegion T d₁ d₂).indicator (shellWeight (1 / 2 - σ)) (a, y) * ENNReal.ofReal y⁻¹ *
        (maximalCompactHaar F) Set.univ * ENNReal.ofReal y⁻¹ :=
    measurable_const.mul (Measurable.lintegral_prod_right'
      (measurable_shellIntegrand T d₁ d₂ (1 / 2 - σ) ((maximalCompactHaar F) Set.univ)))
  calc ∫⁻ z in D, ∫⁻ t in D, ∫⁻ k,
          Ω.indicator (fun g => ENNReal.ofReal (adelicHeight F g ^ (1 / 2 - σ)))
              (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            ENNReal.ofReal ((ideleNorm F t)⁻¹)
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
      ≤ ∫⁻ z in D, ∫⁻ t in D, ∫⁻ _k : ↥(adelicMaximalCompact F),
          (shellRegion T d₁ d₂).indicator (shellWeight (1 / 2 - σ)) (ideleNorm F z, ideleNorm F t) *
            ENNReal.ofReal ((ideleNorm F t)⁻¹)
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) :=
        lintegral_mono fun z => lintegral_mono fun t => lintegral_mono fun k => hpt z t k
    _ = ∫⁻ z in D, ∫⁻ t in D,
          (shellRegion T d₁ d₂).indicator (shellWeight (1 / 2 - σ)) (ideleNorm F z, ideleNorm F t) *
            ENNReal.ofReal ((ideleNorm F t)⁻¹) * (maximalCompactHaar F) Set.univ
          ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
        simp only [lintegral_const]
    _ = ∫⁻ z in D, (V * ∫⁻ y in Set.Ioi (0 : ℝ),
          (shellRegion T d₁ d₂).indicator (shellWeight (1 / 2 - σ)) (ideleNorm F z, y) * ENNReal.ofReal y⁻¹ *
            (maximalCompactHaar F) Set.univ * ENNReal.ofReal y⁻¹)
          ∂(NumberField.Idele.idelicHaar F) :=
        lintegral_congr fun z => hV _ (hf₁ (ideleNorm F z))
    _ = V * ∫⁻ a in Set.Ioi (0 : ℝ),
          (V * ∫⁻ y in Set.Ioi (0 : ℝ),
            (shellRegion T d₁ d₂).indicator (shellWeight (1 / 2 - σ)) (a, y) * ENNReal.ofReal y⁻¹ *
              (maximalCompactHaar F) Set.univ * ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹ :=
        hV _ hf₂
    _ < ∞ := ENNReal.mul_lt_top hVT.lt_top
        (lintegral_lintegral_shell_indicator_rpow_lt_top he hT hd₁ (measure_ne_top _ _) hVT)

end HighShellMajorant

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc NumberField.AdelicBox"

section TruncatedIntegral

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem continuous_of_forall_constantTerm_eq_add {φ m : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hEc : Continuous fun g : AdelicGL2 (𝓞 F) F =>
      φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
    (hCT : ∀ y : AdelicGL2 (𝓞 F) F, constantTerm
        (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
        (fun g => φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
        y = φ y + m y) :
    Continuous m := by
  have h : m = fun y => constantTerm
      (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
      (fun g => φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      y - φ y := by
    funext y
    rw [hCT y]
    ring
  rw [h]
  exact (continuous_constantTerm_cond_adelicBox_of_continuous hEc).sub hφc

private theorem setIntegral_adaptedDomain_pseudoEisenstein_brT_eq (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    {T d₁ d₂ : ℝ} (hT : 1 ≤ T) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀m : MeasurableSet Φ₀)
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    {s : ℂ} (hs : 1 / 2 < s.re) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφs : IsInducedSection (𝓞 F) F (etaFst 1 (modChar F) hα s) (etaSnd 1 (modChar F) hα s) φ)
    (hφc : Continuous φ)
    (hEc : Continuous fun g : AdelicGL2 (𝓞 F) F =>
      φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
    (hφB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, φ (globalPoints (𝓞 F) F γ * g) = φ g)
    {m : AdelicGL2 (𝓞 F) F → ℂ}
    (hm : ∀ g : AdelicGL2 (𝓞 F) F, m g =
      (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g)
    (hmB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F, m (globalPoints (𝓞 F) F γ * g) = m g)
    (hint : IntegrableOn (pseudoEisenstein F (brT T φ m)) (adaptedDomain F T Φ₀) (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    ∫ g in adaptedDomain F T Φ₀, pseudoEisenstein F (brT T φ m) g ∂adelicGLHaar (Fin 2) (𝓞 F) F =
      ∫ g in lowPart F T Φ₀,
        (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
        ∂adelicGLHaar (Fin 2) (𝓞 F) F := by

  have hφN : ∀ (u : AdeleRing (𝓞 F) F) (y : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 u * y) = φ y :=
    fun u y => isInducedSection_unipotent_mul hφs u y
  have hone : IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun _ => by simp
  have hCT : ∀ y : AdelicGL2 (𝓞 F) F, constantTerm
      (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
      (fun g => φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      y = φ y + (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ y := by
    intro y
    have h := constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral F hα 1 1 hone hone s hs φ
      hφs hφc y
    exact h
  have hCTm : ∀ y : AdelicGL2 (𝓞 F) F, constantTerm
      (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)) unipotentGL2
      (fun g => φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))
      y = φ y + m y := fun y => by rw [hCT y, hm y]
  have hmc : Continuous m := continuous_of_forall_constantTerm_eq_add hφc hEc hCTm

  have hrem : ∀ g : AdelicGL2 (𝓞 F) F,
      (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g =
      (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        φ g - m g := fun g => by rw [hm g]; ring
  have hremf : (fun g : AdelicGL2 (𝓞 F) F =>
      (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g) =
      fun g => (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        φ g - m g := funext hrem

  have hB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      (fun g : AdelicGL2 (𝓞 F) F =>
          (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
            (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
              weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g)
        (globalPoints (𝓞 F) F γ * g) =
      (fun g : AdelicGL2 (𝓞 F) F =>
          (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
            (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
              weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g) g := by
    intro γ hγ g
    rw [hremf]
    show (φ (globalPoints (𝓞 F) F γ * g) + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (globalPoints (𝓞 F) F γ * g))) -
        φ (globalPoints (𝓞 F) F γ * g) - m (globalPoints (𝓞 F) F γ * g) =
      (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        φ g - m g
    rw [tsum_apply_adelicWeyl_mul_unipotentGL2_mul_globalPoints_mul φ hφB hγ g, hφB γ hγ g, hmB γ hγ g]

  have hmeas : Measurable (fun g : AdelicGL2 (𝓞 F) F =>
      (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g) := by
    rw [hremf]
    exact ((hEc.sub hφc).sub hmc).measurable

  have hhigh : highPart F T Φ₀ ⊆ adaptedDomain F T Φ₀ := Set.subset_union_right
  have hIO : IntegrableOn (fun g : AdelicGL2 (𝓞 F) F =>
      (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g)
      (highPart F T Φ₀) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    rw [hremf]
    refine (hint.mono_set hhigh).congr_fun (fun g hg => ?_) (measurableSet_highPart hΦ₀m)
    show pseudoEisenstein F (brT T φ m) g =
      (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
        φ g - m g
    rw [pseudoEisenstein_brT_of_mem_highPart hT φ m hg]
    ring

  have hIy : ∀ y ∈ highSlab F T d₁ d₂, IntegrableOn
      (fun u => (fun g : AdelicGL2 (𝓞 F) F =>
        (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) -
          (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ g)
        (unipotentGL2 u * y))
      (adelicBox F)
      (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ •
        NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) := by
    intro y _
    refine (integrableOn_adelicBox_comp_unipotentGL2_mul_sub_const hEc y (φ y + m y)).congr_fun
      (fun u _ => ?_) (measurableSet_adelicBox F)
    show (φ (unipotentGL2 u * y) + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (unipotentGL2 u * y))) - (φ y + m y) =
      (∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) *
        (unipotentGL2 u * y))) -
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) φ (unipotentGL2 u * y)
    rw [weylIntertwiningIntegral_unipotentGL2_mul φ u y, ← hm y, hφN u y]
    ring

  have hzero := setIntegral_highPart_bigCellSum_sub_eq_zero hT hΦ₀m hΦ₀s hΦ₀ φ hφN hCT hB hmeas hIO hIy
  rw [setIntegral_adaptedDomain_eq_add hΦ₀m _ hint,
    setIntegral_congr_fun (measurableSet_lowPart hΦ₀m) fun g hg => pseudoEisenstein_brT_of_mem_lowPart φ m hg,
    setIntegral_congr_fun (measurableSet_highPart hΦ₀m) fun g hg => pseudoEisenstein_brT_of_mem_highPart hT φ m hg]
  have hhigh0 : ∫ g in highPart F T Φ₀,
      ((∑' ξ : F, φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) - m g)
        ∂adelicGLHaar (Fin 2) (𝓞 F) F = 0 := by
    simp_rw [hm]
    exact hzero
  rw [hhigh0, add_zero]

end TruncatedIntegral

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section SeriesIntegrability

open Filter
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ι : Type*} [Countable ι]

private theorem measurable_tsum_enorm {u : ι → X → ℂ} (hu : ∀ i, Measurable (u i)) :
    Measurable fun x => ∑' i, ‖u i x‖ₑ := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun t => Finset.measurable_sum t fun i _ => (hu i).enorm

private theorem ae_summable_of_lintegral_tsum_enorm_ne_top {u : ι → X → ℂ} (hu : ∀ i, Measurable (u i))
    (h : ∫⁻ x, ∑' i, ‖u i x‖ₑ ∂μ ≠ ∞) : ∀ᵐ x ∂μ, Summable fun i => u i x := by
  filter_upwards [ae_lt_top (measurable_tsum_enorm hu) h] with x hx
  have hx' : (∑' i, ((‖u i x‖₊ : ℝ≥0) : ℝ≥0∞)) ≠ ∞ := hx.ne
  exact Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.mp hx')

private theorem integrableOn_tsum_of_lintegral_tsum_enorm_ne_top {u : ι → X → ℂ} {Φ : Set X}
    (hu : ∀ i, Measurable (u i)) (h : ∫⁻ x in Φ, ∑' i, ‖u i x‖ₑ ∂μ ≠ ∞) :
    IntegrableOn (fun x => ∑' i, u i x) Φ μ := by
  refine ⟨?_, ?_⟩
  · refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι)) (f := fun t x => ∑ i ∈ t, u i x)
      (fun t => (Finset.measurable_sum t fun i _ => hu i).aestronglyMeasurable) ?_
    filter_upwards [ae_summable_of_lintegral_tsum_enorm_ne_top (μ := μ.restrict Φ) hu h] with x hx
    exact hx.hasSum
  · exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) h.lt_top

private theorem enorm_setIntegral_tsum_sub_setIntegral_tsum_le {u v : ι → X → ℂ} {Φ : Set X}
    (hu : ∀ i, Measurable (u i)) (hv : ∀ i, Measurable (v i)) (hu' : ∫⁻ x in Φ, ∑' i, ‖u i x‖ₑ ∂μ ≠ ∞)
    (hv' : ∫⁻ x in Φ, ∑' i, ‖v i x‖ₑ ∂μ ≠ ∞) :
    ‖(∫ x in Φ, ∑' i, u i x ∂μ) - ∫ x in Φ, ∑' i, v i x ∂μ‖ₑ ≤ ∫⁻ x in Φ, ∑' i, ‖u i x - v i x‖ₑ ∂μ := by
  rw [← integral_sub (integrableOn_tsum_of_lintegral_tsum_enorm_ne_top hu hu')
    (integrableOn_tsum_of_lintegral_tsum_enorm_ne_top hv hv')]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [ae_summable_of_lintegral_tsum_enorm_ne_top (μ := μ.restrict Φ) hu hu',
    ae_summable_of_lintegral_tsum_enorm_ne_top (μ := μ.restrict Φ) hv hv'] with x hxu hxv
  rw [← hxu.tsum_sub hxv]
  exact enorm_tsum_le_tsum_enorm

private theorem lintegral_lintegral_indicator_sq_mul_mul_eq_mul {d₁ d₂ : ℝ} (L : ℝ≥0∞)
    (hlog : ∀ y : ℝ, 0 < y →
      ∫⁻ a in Set.Ioi (0 : ℝ), (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * ENNReal.ofReal a⁻¹
        = L)
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ a in Set.Ioi (0 : ℝ),
        (∫⁻ y in Set.Ioi (0 : ℝ),
          (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
            ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹
      = L * ∫⁻ y in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ := by
  have hind : Measurable fun p : ℝ × ℝ => (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (p.1 ^ 2 * p.2) :=
    (measurable_const.indicator measurableSet_Icc).comp ((measurable_fst.pow_const 2).mul measurable_snd)
  have hm : Measurable (Function.uncurry fun a y : ℝ =>
      (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
        ENNReal.ofReal y⁻¹ * ENNReal.ofReal a⁻¹) :=
    (((hind.mul (hw.comp measurable_snd)).mul measurable_snd.inv.ennreal_ofReal).mul
      measurable_snd.inv.ennreal_ofReal).mul measurable_fst.inv.ennreal_ofReal
  calc ∫⁻ a in Set.Ioi (0 : ℝ),
          (∫⁻ y in Set.Ioi (0 : ℝ),
            (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
              ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹
        = ∫⁻ a in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
            (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
              ENNReal.ofReal y⁻¹ * ENNReal.ofReal a⁻¹ :=
        lintegral_congr fun a => (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ y in Set.Ioi (0 : ℝ), ∫⁻ a in Set.Ioi (0 : ℝ),
            (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
              ENNReal.ofReal y⁻¹ * ENNReal.ofReal a⁻¹ :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ y in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ * L := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun ⦃y⦄ hy => ?_
        have hy' : (0 : ℝ) < y := hy
        calc ∫⁻ a in Set.Ioi (0 : ℝ),
                (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
                  ENNReal.ofReal y⁻¹ * ENNReal.ofReal a⁻¹
              = ∫⁻ a in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ *
                  ((Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * ENNReal.ofReal a⁻¹) :=
              lintegral_congr fun a => by ring
          _ = w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ * L := by
              have hma : Measurable fun a : ℝ =>
                  (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * ENNReal.ofReal a⁻¹ :=
                ((measurable_const.indicator measurableSet_Icc).comp ((measurable_id.pow_const 2).mul_const y)).mul
                  measurable_inv.ennreal_ofReal
              rw [lintegral_const_mul _ hma, hlog y hy']
    _ = L * ∫⁻ y in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ := by
        rw [lintegral_mul_const L, mul_comm]
        exact (hw.mul measurable_inv.ennreal_ofReal).mul measurable_inv.ennreal_ofReal

private theorem lintegral_const_mul_lintegral_indicator_sq_mul_mul_eq {d₁ d₂ : ℝ} (V L : ℝ≥0∞)
    (hlog : ∀ y : ℝ, 0 < y →
      ∫⁻ a in Set.Ioi (0 : ℝ), (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * ENNReal.ofReal a⁻¹
        = L)
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ a in Set.Ioi (0 : ℝ),
        (V * ∫⁻ y in Set.Ioi (0 : ℝ),
          (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
            ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹
      = V * (L * ∫⁻ y in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹) := by
  have hG : Measurable (Function.uncurry fun a y : ℝ =>
      (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
        ENNReal.ofReal y⁻¹) :=
    ((((measurable_const.indicator measurableSet_Icc).comp ((measurable_fst.pow_const 2).mul measurable_snd)).mul
      (hw.comp measurable_snd)).mul measurable_snd.inv.ennreal_ofReal).mul measurable_snd.inv.ennreal_ofReal
  have hI : Measurable fun a : ℝ =>
      (∫⁻ y in Set.Ioi (0 : ℝ),
        (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
          ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹ :=
    (Measurable.lintegral_prod_right' hG).mul measurable_inv.ennreal_ofReal
  calc ∫⁻ a in Set.Ioi (0 : ℝ),
          (V * ∫⁻ y in Set.Ioi (0 : ℝ),
            (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
              ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹
        = ∫⁻ a in Set.Ioi (0 : ℝ),
            V * ((∫⁻ y in Set.Ioi (0 : ℝ),
              (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
                ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹) :=
        lintegral_congr fun a => mul_assoc _ _ _
    _ = V * ∫⁻ a in Set.Ioi (0 : ℝ),
            (∫⁻ y in Set.Ioi (0 : ℝ),
              (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
                ENNReal.ofReal y⁻¹) * ENNReal.ofReal a⁻¹ :=
        lintegral_const_mul V hI
    _ = V * (L * ∫⁻ y in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹) := by
        rw [lintegral_lintegral_indicator_sq_mul_mul_eq_mul L hlog hw]

end SeriesIntegrability

section BruhatMajorantAdelic

variable (F : Type) [Field F] [NumberField F]

private theorem lintegral_indicator_comp_adelicHeight_out_le (c : ℝ≥0∞)
    (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
      ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
        (∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) =
          c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t *
                    (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (V : ℝ≥0∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hHm : Measurable (NumberField.AdelicHeight.adelicHeight F))
    (hHinv : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.AdelicHeight.adelicHeight F (x * g) = NumberField.AdelicHeight.adelicHeight F g)
    (hH : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      NumberField.AdelicHeight.adelicHeight F
          (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F)) =
        NumberField.TateGlobal.ideleNorm F t)
    (hN : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det
          (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        NumberField.TateGlobal.ideleNorm F z ^ 2 * NumberField.TateGlobal.ideleNorm F t)
    {d₁ d₂ : ℝ} (L : ℝ≥0∞)
    (hlog : ∀ y : ℝ, 0 < y →
      ∫⁻ a in Set.Ioi (0 : ℝ), (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * ENNReal.ofReal a⁻¹
        = L)
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) {Ω : Set (AdelicGL2 (𝓞 F) F)} (hΩm : MeasurableSet Ω)
    (hΩinv : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ Ω ↔ g ∈ Ω)
    (hΩ : ∀ g ∈ Ω, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂) :
    ∫⁻ q, Ω.indicator (fun g => w (NumberField.AdelicHeight.adelicHeight F g)) q.out
        ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F)
      ≤ c * (V * (V * (L * ∫⁻ y in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹))) := by
  set f : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := Ω.indicator fun g => w (NumberField.AdelicHeight.adelicHeight F g) with hf
  have hfm : Measurable f := (hw.comp hHm).indicator hΩm
  have hfinv : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g := by
    intro x hx g
    by_cases hg : g ∈ Ω
    · rw [hf, Set.indicator_of_mem hg, Set.indicator_of_mem ((hΩinv x hx g).2 hg)]
      simp only [hHinv x hx g]
    · rw [hf, Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg ((hΩinv x hx g).1 h))]
  rw [hc D D hDm hDm hDF hDF f hfm hfinv]
  refine mul_le_mul_right ?_ c
  have hpt : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      f (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
        ≤ (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞))
              (NumberField.TateGlobal.ideleNorm F z ^ 2 * NumberField.TateGlobal.ideleNorm F t) *
            w (NumberField.TateGlobal.ideleNorm F t) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) := by
    intro z t k
    refine mul_le_mul_left ?_ _
    by_cases hg : AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t *
        (k : AdelicGL2 (𝓞 F) F) ∈ Ω
    · have hslab := hΩ _ hg
      rw [hN] at hslab
      rw [hf, Set.indicator_of_mem hg, Set.indicator_of_mem hslab]
      simp only [hH, one_mul, le_refl]
    · rw [hf, Set.indicator_of_notMem hg]
      exact zero_le
  have hG : Measurable (Function.uncurry fun x y : ℝ =>
      (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
        ENNReal.ofReal y⁻¹) :=
    ((((measurable_const.indicator measurableSet_Icc).comp ((measurable_fst.pow_const 2).mul measurable_snd)).mul
      (hw.comp measurable_snd)).mul measurable_snd.inv.ennreal_ofReal).mul measurable_snd.inv.ennreal_ofReal
  have hf₁ : ∀ x : ℝ, Measurable fun y : ℝ =>
      (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ := fun x =>
    (((measurable_const.indicator measurableSet_Icc).comp (measurable_id.const_mul (x ^ 2))).mul hw).mul
      measurable_inv.ennreal_ofReal
  have hf₂ : Measurable fun x : ℝ => V * ∫⁻ y in Set.Ioi (0 : ℝ),
      (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ :=
    measurable_const.mul (Measurable.lintegral_prod_right' hG)
  calc ∫⁻ z in D, ∫⁻ t in D, ∫⁻ k,
          f (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
      ≤ ∫⁻ z in D, ∫⁻ t in D, ∫⁻ _k : ↥(adelicMaximalCompact F),
          (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞))
              (NumberField.TateGlobal.ideleNorm F z ^ 2 * NumberField.TateGlobal.ideleNorm F t) *
            w (NumberField.TateGlobal.ideleNorm F t) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) :=
        lintegral_mono fun z => lintegral_mono fun t => lintegral_mono fun k => hpt z t k
    _ = ∫⁻ z in D, ∫⁻ t in D,
          (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞))
              (NumberField.TateGlobal.ideleNorm F z ^ 2 * NumberField.TateGlobal.ideleNorm F t) *
            w (NumberField.TateGlobal.ideleNorm F t) * ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
          ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
        simp only [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ z in D, (V * ∫⁻ y in Set.Ioi (0 : ℝ),
          (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (NumberField.TateGlobal.ideleNorm F z ^ 2 * y) * w y *
            ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹)
          ∂(NumberField.Idele.idelicHaar F) :=
        lintegral_congr fun z => hV _ (hf₁ (NumberField.TateGlobal.ideleNorm F z))
    _ = V * ∫⁻ x in Set.Ioi (0 : ℝ),
          (V * ∫⁻ y in Set.Ioi (0 : ℝ),
            (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * w y * ENNReal.ofReal y⁻¹ *
              ENNReal.ofReal y⁻¹) * ENNReal.ofReal x⁻¹ :=
        hV _ hf₂
    _ = V * (V * (L * ∫⁻ y in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹)) := by
        rw [lintegral_const_mul_lintegral_indicator_sq_mul_mul_eq V L hlog hw]

private theorem setLIntegral_tsum_bruhatRep_mul_le (c : ℝ≥0∞)
    (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
      ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
        (∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) =
          c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t *
                    (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (V : ℝ≥0∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hHm : Measurable (NumberField.AdelicHeight.adelicHeight F))
    (hHinv : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.AdelicHeight.adelicHeight F (x * g) = NumberField.AdelicHeight.adelicHeight F g)
    (hH : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      NumberField.AdelicHeight.adelicHeight F
          (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F)) =
        NumberField.TateGlobal.ideleNorm F t)
    (hN : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det
          (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        NumberField.TateGlobal.ideleNorm F z ^ 2 * NumberField.TateGlobal.ideleNorm F t)
    {d₁ d₂ : ℝ} (L : ℝ≥0∞)
    (hlog : ∀ y : ℝ, 0 < y →
      ∫⁻ a in Set.Ioi (0 : ℝ), (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (a ^ 2 * y) * ENNReal.ofReal a⁻¹
        = L)
    {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    {S : Set (AdelicGL2 (𝓞 F) F)} (hS : MeasurableSet S)
    (hSΓ : ∀ γ ∈ (AutomorphicForm.globalPoints (𝓞 F) F).range, ∀ g : AdelicGL2 (𝓞 F) F, γ * g ∈ S ↔ g ∈ S)
    (hSH : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, x * g ∈ S ↔ g ∈ S)
    (hSd : ∀ g ∈ S, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂)
    {Φ : Set (AdelicGL2 (𝓞 F) F)} (hΦm : MeasurableSet Φ) (hΦS : Φ ⊆ S)
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    {f : AdelicGL2 (𝓞 F) F → ℝ≥0∞} (hf : Measurable f)
    (hfB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      f (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = f g)
    (hfN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), f (AutomorphicForm.unipotentGL2 u * g) = f g)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hfw : ∀ g : AdelicGL2 (𝓞 F) F, f g ≤ C * w (NumberField.AdelicHeight.adelicHeight F g)) :
    ∫⁻ g in Φ, ∑' τ : Option F, f (bruhatRep (F := F) τ * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      ≤ C * (c * (V * (V * (L * ∫⁻ y in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹)))) := by
  rw [setLIntegral_tsum_bruhatRep_mul_eq_lintegral_indicator_mul_setLIntegral_adelicBox F hS hSΓ hSH hΦm hΦS hΦ hf
    hfB]
  have hbox : ∀ q : AutomorphicForm.RationalTorusUnipotentQuotient F,
      ∫⁻ u in adelicBox F, f (AutomorphicForm.unipotentGL2 u * q.out)
          ∂((adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F) = f q.out := by
    intro q
    simp_rw [hfN]
    rw [setLIntegral_const, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne, mul_one]
  simp only [hbox]
  calc ∫⁻ q, S.indicator (fun _ => (1 : ℝ≥0∞)) q.out * f q.out
          ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F)
      ≤ ∫⁻ q, C * S.indicator (fun g => w (NumberField.AdelicHeight.adelicHeight F g)) q.out
          ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) := by
        refine lintegral_mono fun q => ?_
        by_cases hq : q.out ∈ S
        · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, one_mul]
          exact hfw _
        · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, zero_mul, mul_zero]
    _ = C * ∫⁻ q, S.indicator (fun g => w (NumberField.AdelicHeight.adelicHeight F g)) q.out
          ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) :=
        lintegral_const_mul' _ _ hC
    _ ≤ C * (c * (V * (V * (L * ∫⁻ y in Set.Ioi (0 : ℝ), w y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹)))) :=
        mul_le_mul_right (lintegral_indicator_comp_adelicHeight_out_le F c hc D hDm hDF V hV hHm hHinv hH hN L hlog hw
          hS hSH hSd) C

end BruhatMajorantAdelic

end AutomorphicForm.SlabCovolume

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory Filter NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.AdelicLevel NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc"
open NumberField.AdelicBox AutomorphicForm.WindowedSiegel
open scoped ENNReal Topology

section ResidueCore

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem exists_forall_norm_le_lowPart_one (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ)) {c₀ u e₁ e₂ : ℝ}
    (hc₀ : 0 < c₀) {tset : Finset (AdelicGL2 (𝓞 F) F)} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hcov : Φ₀ ⊆ ⋃ t ∈ tset, (· * t) '' centreCutSiegelSet F c₀ u e₁ e₂) {a : ℝ} (ha : a < 1 / 2)
    (G : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hGbd : ∀ (c u : ℝ) (t : AdelicGL2 (𝓞 F) F) (C : Set ℂ), 0 < c → IsCompact C → C ⊆ {s : ℂ | a < s.re} →
      ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ integralWindowedSiegelSet F c u,
        ‖G s (g * t)‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N) :
    ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ lowPart F 1 Φ₀, ‖G ((1 / 2 : ℂ) + (t : ℂ)) x‖ ≤ M := by
  have hCc : IsCompact ((fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image (continuous_const.add Complex.continuous_ofReal)
  have hCsub : (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) '' Set.Icc (0 : ℝ) 1 ⊆ {s : ℂ | a < s.re} := by
    rintro _ ⟨t, ht, rfl⟩
    have h2 : ((1 / 2 : ℂ) + (t : ℂ)).re = 1 / 2 + t := by simp [Complex.add_re]
    rw [Set.mem_setOf_eq, h2]
    linarith [ht.1]
  have hbound : ∀ t' : AdelicGL2 (𝓞 F) F, ∃ (M : ℝ) (N : ℕ),
      ∀ s ∈ (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) '' Set.Icc (0 : ℝ) 1,
        ∀ x ∈ integralWindowedSiegelSet F (c₀ ^ ∑ w : InfinitePlace F, w.mult) u,
          ‖G s (x * t')‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F x)) ^ N :=
    fun t' => hGbd (c₀ ^ ∑ w : InfinitePlace F, w.mult) u t' _ (pow_pos hc₀ _) hCc hCsub
  have hB := exists_forall_norm_le_of_mem_lowPart (T := 1) hα hc₀.le hcov G
    ((fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ)) '' Set.Icc (0 : ℝ) 1) hbound
  obtain ⟨B, hB⟩ := hB
  exact ⟨B, fun t ht x hx => hB _ ⟨t, ht, rfl⟩ x hx⟩

private theorem measure_highPart_one_eq (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ)) {d₁ d₂ : ℝ} (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀m : MeasurableSet Φ₀)
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    {cq : ℝ≥0∞} {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hlaw : ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
      (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
          cq * ∫⁻ z in D, ∫⁻ t in D, ∫⁻ k,
                f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) * ENNReal.ofReal ((ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    {V : ℝ≥0∞}
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi 0, f y * ENNReal.ofReal y⁻¹) :
    adelicGLHaar (Fin 2) (𝓞 F) F (highPart F 1 Φ₀) =
      cq * V * V * (ENNReal.ofReal (Real.log (d₂ / d₁) / 2) * 1) := by
  have h1 : (1 : ℝ) ≤ 1 := le_rfl
  have hD1 := setLIntegral_eq_lintegral_indicator_mul_setLIntegral_adelicBox F (f := fun _ => (1 : ℝ≥0∞))
    (measurableSet_highSlab 1 d₁ d₂) (fun _ hx g => mul_mem_highSlab_iff_of_mem_rationalTorusUnipotent hx g)
    (measurableSet_highPart hΦ₀m) (highPart_subset_highSlab hΦ₀s) (isFundamentalDomain_highPart h1 hΦ₀m hΦ₀s hΦ₀)
    measurable_const fun _ _ _ => rfl
  have hlogv : ∀ y : ℝ, 0 < y → ∫⁻ x in Set.Ioi (0 : ℝ),
      (Set.Icc d₁ d₂).indicator (fun _ => (1 : ℝ≥0∞)) (x ^ 2 * y) * ENNReal.ofReal x⁻¹ =
        ENNReal.ofReal (Real.log (d₂ / d₁) / 2) :=
    fun y hy => lintegral_indicator_sq_mul_mul_ofReal_inv hd₁ hd.le hy
  have hpowv : ∫⁻ y in Set.Ioi (0 : ℝ),
      (Set.Ioi (1 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ = 1 := by
    have h := lintegral_indicator_Ioi_mul_ofReal_rpow (T := 1) (e := 0) one_pos one_pos
    rw [Real.one_rpow, sub_zero, div_one, ENNReal.ofReal_one] at h
    refine Eq.trans (setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_) h
    have hy' : 0 ≤ y := le_of_lt hy
    have hyy : y⁻¹ * y⁻¹ = y ^ ((0 : ℝ) - 2) := by
      rw [zero_sub, Real.rpow_neg hy', Real.rpow_two, ← mul_inv, sq]
    show (Set.Ioi (1 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ =
      (Set.Ioi (1 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal (y ^ ((0 : ℝ) - 2))
    rw [mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hy'), hyy]
  exact measure_highPart_eq hα hD1 cq V (ENNReal.ofReal (Real.log (d₂ / d₁) / 2)) 1 hlaw hV hlogv hpowv

private theorem inv_mul_weylIntertwiningIntegral_globalPoints_mul (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 (modChar F) hα s) (etaSnd 1 (modChar F) hα s) (ψ s))
    (hψK : ∀ s, IsArchKFinite F (ψ s)) (hψsm : ∀ s, IsKfSmooth F (ψ s))
    (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2)) (hψhol : ∀ g, Differentiable ℂ (fun s => ψ s g))
    {s : ℂ} (hs : 1 / 2 < s.re) {γ : GL (Fin 2) F} (hγ : γ ∈ borelSubgroup F) (g : AdelicGL2 (𝓞 F) F) :
    (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (ψ s)
          (globalPoints (𝓞 F) F γ * g) =
      (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (ψ s) g := by
  have hrow :=
    exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family F hα ψ
      hψ hψK hψsm hψjc hψhol
  obtain ⟨a, Mreg, ha, -, hMreg, -, hMsec⟩ := hrow
  have hs0 : s - 1 / 2 ≠ 0 := sub_ne_zero.mpr fun h => by
    rw [h] at hs
    norm_num at hs
  have hsecM : IsInducedSection (𝓞 F) F (etaFst 1 (modChar F) hα (-s)) (etaSnd 1 (modChar F) hα (-s))
      (fun g' => (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (ψ s) g') := by
    intro b' hb' g'
    beta_reduce
    have hb := hMsec s (ha.trans hs) b' hb' g'
    rw [hMreg s (b' * g') hs, hMreg s g' hs] at hb
    apply mul_left_cancel₀ hs0
    linear_combination hb
  exact globalPoints_mul_eq_of_isInducedSection_etaFst_etaSnd_one F (modChar F) hα
    (isPrincipalTrivial_distribHaarChar_adeleRing F) (-s) hsecM hγ g

private theorem toReal_measure_mul_limUnder_eq_of_truncated_identity (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd : d₁ < d₂) {Φ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦs : Φ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    {c₀ u e₁ e₂ : ℝ} (hc₀ : 0 < c₀) {tset : Finset (AdelicGL2 (𝓞 F) F)} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀m : MeasurableSet Φ₀) (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (hcov : Φ₀ ⊆ ⋃ t ∈ tset, (· * t) '' centreCutSiegelSet F c₀ u e₁ e₂)
    {c cq V : ℝ≥0∞} (hcq : cq = c * NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F (adelicBox F))
    {D : Set (AdeleRing (𝓞 F) F)ˣ}
    (hlaw : ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
      (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
          cq * ∫⁻ z in D, ∫⁻ t in D, ∫⁻ k,
                f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) * ENNReal.ofReal ((ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi 0, f y * ENNReal.ofReal y⁻¹)
    (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ) (hμic : IsIdeleClassChar (𝓞 F) F μ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ (modChar F) hα s) (etaSnd μ (modChar F) hα s) (ψf s))
    (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
    (hψhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
    (hψK : ∀ s, IsArchKFinite F (ψf s)) (hψsm : ∀ s, IsKfSmooth F (ψf s))
    (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hMc : ∀ g : AdelicGL2 (𝓞 F) F, MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
      ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
        Mc s g = weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (ψf s) g)
    (P Q : ℂ → ℂ)
    (hP : Tendsto (fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * P ((1 / 2 : ℂ) + (t : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hQ : Tendsto (fun t : ℝ => Q ((1 / 2 : ℂ) + (t : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hL3 : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ x in adaptedDomain F 1 Φ₀, pseudoEisenstein F (brT 1 (fnTwist F μ⁻¹ (ψf s)) (fun g =>
          (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g))
          x ∂adelicGLHaar (Fin 2) (𝓞 F) F =
        (cq.toReal : ℂ) * (∫ k, fnTwist F μ⁻¹ (ψf s) (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) *
            ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ / d₁) / 2 : ℝ) : ℂ) * P s -
          (cq.toReal : ℂ) * (∫ k, (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
              weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s))
                (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) *
            ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ / d₁) / 2 : ℝ) : ℂ) * Q s)
    (hL3int : ∀ s : ℂ, 1 / 2 < s.re →
      IntegrableOn (pseudoEisenstein F (brT 1 (fnTwist F μ⁻¹ (ψf s)) (fun g =>
          (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g)))
        (adaptedDomain F 1 Φ₀) (adelicGLHaar (Fin 2) (𝓞 F) F))
    (g : AdelicGL2 (𝓞 F) F) :
    (((adelicGLHaar (Fin 2) (𝓞 F) F) Φ).toReal : ℂ) *
        Filter.limUnder (𝓝[≠] (1 / 2 : ℂ)) (fun s : ℂ => (s - (1 / 2 : ℂ)) * Mc s g) =
      ((c.toReal * ((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal ^ 2 * V.toReal ^ 2
          * Real.log (d₂ / d₁) / 2 : ℝ) : ℂ) *
      (∫ k, fnTwist F μ⁻¹ (ψf (1 / 2 : ℂ)) (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) *
      ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by

  have hsec0 : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 (modChar F) hα s) (etaSnd 1 (modChar F) hα s)
      (fnTwist F μ⁻¹ (ψf s)) := fun s => isInducedSection_fnTwist_inv (modChar F) hα μ s (hψf s)
  have hK0 : ∀ s, IsArchKFinite F (fnTwist F μ⁻¹ (ψf s)) := fun s => isArchKFinite_fnTwist μ⁻¹ (hψK s)
  have hsm0 : ∀ s, IsKfSmooth F (fnTwist F μ⁻¹ (ψf s)) :=
    isKfSmooth_fnTwist_inv_of_family (modChar F) hα hμ hψf hψhol hψsm
  have hjc0 : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => fnTwist F μ⁻¹ (ψf p.1) p.2) :=
    continuous_uncurry_fnTwist_inv μ hμc hψjc
  have hhol0 : ∀ x : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s => fnTwist F μ⁻¹ (ψf s) x) :=
    differentiable_fnTwist_inv μ hψhol
  have hc0 : ∀ s : ℂ, Continuous (fnTwist F μ⁻¹ (ψf s)) := fun s =>
    Continuous.uncurry_left (f := fun s => fnTwist F μ⁻¹ (ψf s)) s hjc0
  have hrow1 :=
    exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family F hα
      (fun s => fnTwist F μ⁻¹ (ψf s)) hsec0 hK0 hsm0 hjc0 hhol0
  obtain ⟨a, G, ha, -, hGser, hGc, hGbd⟩ := hrow1
  have hrow2 :=
    exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family F hα
      (fun s => fnTwist F μ⁻¹ (ψf s)) hsec0 hK0 hsm0 hjc0 hhol0
  obtain ⟨r, a₂, -, hr, -⟩ := hrow2
  beta_reduce at hGser hr
  have hGhalf : ∀ x : AdelicGL2 (𝓞 F) F, G (1 / 2) x = r :=
    forall_eq_of_series_clauses (ψ := fun s => fnTwist F μ⁻¹ (ψf s)) ha hGser hGc hr

  have hvolΦ : adelicGLHaar (Fin 2) (𝓞 F) F Φ = adelicGLHaar (Fin 2) (𝓞 F) F Φ₀ :=
    measure_eq_of_isFundamentalDomain_slab hΦs hΦ hΦ₀s hΦ₀
  have hfin0 : adelicGLHaar (Fin 2) (𝓞 F) F Φ₀ < ⊤ := by
    have h := adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain F d₁ d₂ hd₁ hd Φ₀ hΦ₀
    rwa [Set.inter_eq_left.mpr hΦ₀s] at h
  have h1 : (1 : ℝ) ≤ 1 := le_rfl
  have hadd := measure_lowPart_add_measure_highPart h1 hΦ₀m hΦ₀s hΦ₀
  have hlowfin : adelicGLHaar (Fin 2) (𝓞 F) F (lowPart F 1 Φ₀) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (lowPart_subset 1 Φ₀)) hfin0).ne
  have hhighfin : adelicGLHaar (Fin 2) (𝓞 F) F (highPart F 1 Φ₀) ≠ ⊤ :=
    (lt_of_le_of_lt (le_add_self.trans hadd.le) hfin0).ne

  have hMaj := exists_forall_norm_le_lowPart_one hα hc₀ hcov ha G hGbd
  obtain ⟨M, hM⟩ := hMaj
  have hlow := tendsto_sub_mul_setIntegral_series_add_ofReal (ψ := fun s => fnTwist F μ⁻¹ (ψf s)) hGser hGc ha hGhalf
    (measurableSet_lowPart hΦ₀m) hlowfin one_pos hM
  have hA := tendsto_integral_maximalCompact_add_ofReal (ψ := fun s => fnTwist F μ⁻¹ (ψf s)) hjc0
  have hBlim := tendsto_sub_mul_integral_weylIntertwiningIntegral_add_ofReal hα (fun s => fnTwist F μ⁻¹ (ψf s))
    hsec0 hjc0 ha hGser hGc hGhalf
  have htok := limUnder_sub_mul_eq_char_det_mul hα μ hμ ψf hψf hψjc Mc hMc (fun s => fnTwist F μ⁻¹ (ψf s)) hjc0
    (eq_char_det_mul_fnTwist_inv μ ψf) (bruhat_series_eq_char_det_mul μ hμic ψf) ha hGser hGc hGhalf g
  beta_reduce at hlow hA hBlim

  have hvh := measure_highPart_one_eq hα hd₁ hd hΦ₀m hΦ₀s hΦ₀ hlaw hV

  have hhalf : ∀ t : ℝ, 0 < t → 1 / 2 < ((1 / 2 : ℂ) + (t : ℂ)).re := fun t ht => by
    have h2 : ((1 / 2 : ℂ) + (t : ℂ)).re = 1 / 2 + t := by simp [Complex.add_re]
    rw [h2]
    linarith
  have hlowI : ∀ s : ℂ, 1 / 2 < s.re →
      ∫ x in adaptedDomain F 1 Φ₀, pseudoEisenstein F (brT 1 (fnTwist F μ⁻¹ (ψf s)) (fun g =>
          (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g))
          x ∂adelicGLHaar (Fin 2) (𝓞 F) F =
        ∫ x in lowPart F 1 Φ₀, (fnTwist F μ⁻¹ (ψf s) x + ∑' ξ : F, fnTwist F μ⁻¹ (ψf s)
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))
          ∂adelicGLHaar (Fin 2) (𝓞 F) F := by
    intro s hs
    have has : a < s.re := ha.trans hs
    have hs0 : s - 1 / 2 ≠ 0 := sub_ne_zero.mpr fun h => by
      rw [h] at hs
      norm_num at hs
    have hEc : Continuous fun x : AdelicGL2 (𝓞 F) F => fnTwist F μ⁻¹ (ψf s) x + ∑' ξ : F, fnTwist F μ⁻¹ (ψf s)
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x) :=
      ((continuous_of_continuousOn_lt_re_prod_univ hGc has).const_mul (s - 1 / 2)⁻¹).congr fun x => by
        rw [hGser s x hs, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
    have hφB : ∀ γ ∈ borelSubgroup F, ∀ x : AdelicGL2 (𝓞 F) F,
        fnTwist F μ⁻¹ (ψf s) (globalPoints (𝓞 F) F γ * x) = fnTwist F μ⁻¹ (ψf s) x :=
      fun γ hγ x => globalPoints_mul_eq_of_isInducedSection_etaFst_etaSnd_one F (modChar F) hα
        (isPrincipalTrivial_distribHaarChar_adeleRing F) s (hsec0 s) hγ x
    have hmB : ∀ γ ∈ borelSubgroup F, ∀ x : AdelicGL2 (𝓞 F) F,
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s))
              (globalPoints (𝓞 F) F γ * x) =
          (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) x :=
      fun γ hγ x => inv_mul_weylIntertwiningIntegral_globalPoints_mul hα (fun s => fnTwist F μ⁻¹ (ψf s)) hsec0 hK0
        hsm0 hjc0 hhol0 hs hγ x
    exact setIntegral_adaptedDomain_pseudoEisenstein_brT_eq (φ := fnTwist F μ⁻¹ (ψf s))
      (m := fun g => (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g)
      hα h1 hΦ₀m hΦ₀s hΦ₀ hs (hsec0 s) (hc0 s) hEc hφB (fun _ => rfl) hmB (hL3int s hs)
  have hb0 := ofReal_toReal_adelicAddHaar_adelicBox_ne_zero F
  have hid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) *
      (∫ x in lowPart F 1 Φ₀, (fnTwist F μ⁻¹ (ψf ((1 / 2 : ℂ) + (t : ℂ))) x +
        ∑' ξ : F, fnTwist F μ⁻¹ (ψf ((1 / 2 : ℂ) + (t : ℂ)))
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))
          ∂adelicGLHaar (Fin 2) (𝓞 F) F) =
      (cq.toReal : ℂ) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ / d₁) / 2 : ℝ) : ℂ) *
        ((∫ k, fnTwist F μ⁻¹ (ψf ((1 / 2 : ℂ) + (t : ℂ))) (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) *
            ((((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * P ((1 / 2 : ℂ) + (t : ℂ))) -
          (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            ((((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) *
              ∫ k, weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)
                (fnTwist F μ⁻¹ (ψf ((1 / 2 : ℂ) + (t : ℂ)))) (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) *
            Q ((1 / 2 : ℂ) + (t : ℂ))) := by
    intro t ht
    rw [← hlowI _ (hhalf t ht.1), hL3 _ (hhalf t ht.1), integral_const_mul]
    ring

  have hl := mul_eq_of_tendsto_of_forall_sub_mul_eq
    (E := fun t : ℝ => ∫ x in lowPart F 1 Φ₀, (fnTwist F μ⁻¹ (ψf ((1 / 2 : ℂ) + (t : ℂ))) x +
        ∑' ξ : F, fnTwist F μ⁻¹ (ψf ((1 / 2 : ℂ) + (t : ℂ)))
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x))
      ∂adelicGLHaar (Fin 2) (𝓞 F) F)
    (Aψ := fun t : ℝ => ∫ k, fnTwist F μ⁻¹ (ψf ((1 / 2 : ℂ) + (t : ℂ))) (k : AdelicGL2 (𝓞 F) F)
      ∂(maximalCompactHaar F))
    (AM := fun t : ℝ => ∫ k, weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F)
      (fnTwist F μ⁻¹ (ψf ((1 / 2 : ℂ) + (t : ℂ)))) (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F))
    (P := fun t : ℝ => (((1 / 2 : ℂ) + (t : ℂ)) - 1 / 2) * P ((1 / 2 : ℂ) + (t : ℂ)))
    (Q := fun t : ℝ => Q ((1 / 2 : ℂ) + (t : ℂ)))
    one_pos hid hlow hA hBlim hP hQ
  have hm : (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
      ((((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) * r) = r :=
    inv_mul_cancel_left₀ hb0 r
  have hlog0 : 0 ≤ Real.log (d₂ / d₁) / 2 :=
    div_nonneg (Real.log_nonneg ((one_le_div hd₁).mpr hd.le)) zero_le_two
  have hh : (((adelicGLHaar (Fin 2) (𝓞 F) F) (highPart F 1 Φ₀)).toReal : ℂ) =
      (cq.toReal : ℂ) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ / d₁) / 2 : ℝ) : ℂ) * 1 := by
    rw [hvh, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hlog0, ENNReal.toReal_one]
    push_cast
    ring
  have hvol : (((adelicGLHaar (Fin 2) (𝓞 F) F) Φ).toReal : ℂ) =
      (((adelicGLHaar (Fin 2) (𝓞 F) F) (lowPart F 1 Φ₀)).toReal : ℂ) +
        (((adelicGLHaar (Fin 2) (𝓞 F) F) (highPart F 1 Φ₀)).toReal : ℂ) := by
    rw [hvolΦ, ← hadd, ENNReal.toReal_add hlowfin hhighfin, Complex.ofReal_add]
  have hfinal := mul_eq_of_low_of_high_of_add hl hm hh hvol

  rw [hcq, ENNReal.toReal_mul] at hfinal
  push_cast at hfinal
  rw [htok]
  push_cast
  linear_combination ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ) * hfinal

end ResidueCore

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section LimitIdentification

open Filter
private theorem eq_of_tendsto_of_enorm_sub_le {α : Type*} {l : Filter α} [l.NeBot] {I : α → ℂ} {I₀ J : ℂ}
    {ε : α → ℝ≥0∞} (hI : Tendsto I l (𝓝 I₀)) (hε : Tendsto ε l (𝓝 0)) (hJ : ∀ a, ‖J - I a‖ₑ ≤ ε a) : J = I₀ := by
  have h1 : Tendsto (fun a => ‖J - I a‖ₑ) l (𝓝 0) :=
    _root_.tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε (fun _ => zero_le ..) hJ
  have h2 : Tendsto (fun a => ‖I a - J‖) l (𝓝 0) := by
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, toReal_enorm', norm_sub_rev] using h3
  exact _root_.tendsto_nhds_unique (_root_.tendsto_iff_norm_sub_tendsto_zero.mpr h2) hI

private theorem tendsto_add_self_nhds_zero {α : Type*} {l : Filter α} {ε : α → ℝ≥0∞} (hε : Tendsto ε l (𝓝 0)) :
    Tendsto (fun a => ε a + ε a) l (𝓝 0) := by
  simpa using hε.add hε

end LimitIdentification

section PseudoEisensteinOfTheBracket

variable (F : Type) [Field F] [NumberField F]

private theorem integrableOn_of_lintegral_tsum_bruhatRep_ne_top {Φ : Set (AdelicGL2 (𝓞 F) F)}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφm : Measurable φ)
    (hmaj : ∫⁻ g in Φ, ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞) :
    IntegrableOn φ Φ (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  refine ⟨hφm.aestronglyMeasurable, lt_of_le_of_lt (lintegral_mono fun g => ?_) hmaj.lt_top⟩
  refine le_of_eq_of_le ?_ (ENNReal.le_tsum (f := fun τ : Option F => ‖φ (bruhatRep (F := F) τ * g)‖ₑ) none)
  beta_reduce
  rw [show bruhatRep (F := F) none = 1 from rfl, one_mul]

private theorem tsum_enorm_weyl_unipotent_mul_le {φ : AdelicGL2 (𝓞 F) F → ℂ} (g : AdelicGL2 (𝓞 F) F) :
    ∑' β : F, ‖φ (adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)‖ₑ
      ≤ ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g)‖ₑ :=
  ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective F)
    fun τ : Option F => ‖φ (bruhatRep (F := F) τ * g)‖ₑ

private theorem integrableOn_tsum_weyl_unipotent_mul_of_lintegral_tsum_bruhatRep_ne_top
    {Φ : Set (AdelicGL2 (𝓞 F) F)} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφm : Measurable φ)
    (hmaj : ∫⁻ g in Φ, ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞) :
    IntegrableOn
      (fun g => ∑' β : F,
        φ (adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g))
      Φ (adelicGLHaar (Fin 2) (𝓞 F) F) :=
  haveI : Countable F := countable_field (F := F)
  integrableOn_tsum_of_lintegral_tsum_enorm_ne_top
    (u := fun β g => φ (adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g))
    (fun _ => hφm.comp (measurable_const_mul _))
    (ne_top_of_le_ne_top hmaj (lintegral_mono fun g => tsum_enorm_weyl_unipotent_mul_le F g))

private theorem integrableOn_pseudoEisenstein_of_lintegral_tsum_bruhatRep_ne_top {Φ : Set (AdelicGL2 (𝓞 F) F)}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφm : Measurable φ)
    (hmaj : ∫⁻ g in Φ, ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞) :
    IntegrableOn (AutomorphicForm.pseudoEisenstein F φ) Φ (adelicGLHaar (Fin 2) (𝓞 F) F) :=
  (integrableOn_of_lintegral_tsum_bruhatRep_ne_top F hφm hmaj).add
    (integrableOn_tsum_weyl_unipotent_mul_of_lintegral_tsum_bruhatRep_ne_top F hφm hmaj)

private theorem setIntegral_pseudoEisenstein_eq_add {Φ : Set (AdelicGL2 (𝓞 F) F)} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφm : Measurable φ)
    (hmaj : ∫⁻ g in Φ, ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞) :
    ∫ g in Φ, AutomorphicForm.pseudoEisenstein F φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = (∫ g in Φ, φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) +
        ∫ g in Φ, ∑' β : F,
            φ (adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
  integral_add (integrableOn_of_lintegral_tsum_bruhatRep_ne_top F hφm hmaj)
    (integrableOn_tsum_weyl_unipotent_mul_of_lintegral_tsum_bruhatRep_ne_top F hφm hmaj)

private theorem enorm_setIntegral_pseudoEisenstein_sub_le {Φ : Set (AdelicGL2 (𝓞 F) F)}
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφ : ∫⁻ g in Φ, ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞)
    (hψ : ∫⁻ g in Φ, ∑' τ : Option F, ‖ψ (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞) :
    ‖(∫ g in Φ, AutomorphicForm.pseudoEisenstein F φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) -
        ∫ g in Φ, AutomorphicForm.pseudoEisenstein F ψ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F)‖ₑ
      ≤ (∫⁻ g in Φ, ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g) - ψ (bruhatRep (F := F) τ * g)‖ₑ
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) +
          ∫⁻ g in Φ, ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g) - ψ (bruhatRep (F := F) τ * g)‖ₑ
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  rw [setIntegral_pseudoEisenstein_eq_add F hφm hφ, setIntegral_pseudoEisenstein_eq_add F hψm hψ, add_sub_add_comm]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← integral_sub (integrableOn_of_lintegral_tsum_bruhatRep_ne_top F hφm hφ)
      (integrableOn_of_lintegral_tsum_bruhatRep_ne_top F hψm hψ)]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun g => ?_)
    refine le_of_eq_of_le ?_
      (ENNReal.le_tsum (f := fun τ : Option F => ‖φ (bruhatRep (F := F) τ * g) - ψ (bruhatRep (F := F) τ * g)‖ₑ) none)
    beta_reduce
    rw [show bruhatRep (F := F) none = 1 from rfl, one_mul]
  · haveI : Countable F := countable_field (F := F)
    refine (enorm_setIntegral_tsum_sub_setIntegral_tsum_le
      (u := fun β g => φ (adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g))
      (v := fun β g => ψ (adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g))
      (fun _ => hφm.comp (measurable_const_mul _)) (fun _ => hψm.comp (measurable_const_mul _))
      (ne_top_of_le_ne_top hφ (lintegral_mono fun g => tsum_enorm_weyl_unipotent_mul_le F g))
      (ne_top_of_le_ne_top hψ (lintegral_mono fun g => tsum_enorm_weyl_unipotent_mul_le F g))).trans
      (lintegral_mono fun g => ?_)
    exact ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective F)
      fun τ : Option F => ‖φ (bruhatRep (F := F) τ * g) - ψ (bruhatRep (F := F) τ * g)‖ₑ

private theorem setIntegral_pseudoEisenstein_eq_of_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    {Φ : Set (AdelicGL2 (𝓞 F) F)} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφm : Measurable φ)
    (hφ : ∫⁻ g in Φ, ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞)
    {ψ : α → AdelicGL2 (𝓞 F) F → ℂ} (hψm : ∀ a, Measurable (ψ a))
    (hψ : ∀ a, ∫⁻ g in Φ, ∑' τ : Option F, ‖ψ a (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞)
    {ε : α → ℝ≥0∞}
    (hdiff : ∀ a, ∫⁻ g in Φ, ∑' τ : Option F, ‖φ (bruhatRep (F := F) τ * g) - ψ a (bruhatRep (F := F) τ * g)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤ ε a)
    (hε : Filter.Tendsto ε l (nhds 0)) {I : α → ℂ}
    (hI : ∀ a, ∫ g in Φ, AutomorphicForm.pseudoEisenstein F (ψ a) g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = I a)
    {I₀ : ℂ} (hI₀ : Filter.Tendsto I l (nhds I₀)) :
    ∫ g in Φ, AutomorphicForm.pseudoEisenstein F φ g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = I₀ := by
  refine eq_of_tendsto_of_enorm_sub_le hI₀ (tendsto_add_self_nhds_zero hε) fun a => ?_
  rw [← hI a]
  exact (enorm_setIntegral_pseudoEisenstein_sub_le F hφm (hψm a) hφ (hψ a)).trans (add_le_add (hdiff a) (hdiff a))

end PseudoEisensteinOfTheBracket

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section ShellTails

open Filter
private theorem setLIntegral_indicator_mul_ofReal_rpow_mul_inv_mul_inv (S : Set ℝ) (e : ℝ) :
    ∫⁻ y in Set.Ioi (0 : ℝ), S.indicator 1 y * ENNReal.ofReal (y ^ e) * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹
      = ∫⁻ y in Set.Ioi (0 : ℝ), S.indicator 1 y * ENNReal.ofReal (y ^ (e - 2)) := by
  refine setLIntegral_congr_fun measurableSet_Ioi fun ⦃y⦄ hy => ?_
  have hy' : (0 : ℝ) < y := hy
  rw [mul_assoc, mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hy'.le),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hy'.le _), ← mul_assoc]
  congr 2
  rw [Real.rpow_sub hy', Real.rpow_two, div_eq_mul_inv]
  ring

private theorem tendsto_ofReal_exp_rpow_div_atBot {e : ℝ} (he : 1 < e) :
    Tendsto (fun R : ℝ => ENNReal.ofReal (Real.exp R ^ (e - 1) / (e - 1))) atBot (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => Real.exp R ^ (e - 1) / (e - 1)) atBot (𝓝 0) := by
    have h2 : Tendsto (fun R : ℝ => Real.exp (R * (e - 1))) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.atBot_mul_const (by linarith))
    have h3 : (fun R : ℝ => Real.exp R ^ (e - 1) / (e - 1)) = fun R : ℝ => Real.exp (R * (e - 1)) / (e - 1) := by
      funext R
      rw [← Real.exp_mul]
    rw [h3]
    simpa using h2.div_const (e - 1)
  simpa using ENNReal.tendsto_ofReal h1

private theorem tendsto_ofReal_exp_rpow_div_atTop {e : ℝ} (he : e < 1) :
    Tendsto (fun R : ℝ => ENNReal.ofReal (Real.exp R ^ (e - 1) / (1 - e))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => Real.exp R ^ (e - 1) / (1 - e)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun R : ℝ => Real.exp (R * (e - 1))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.atTop_mul_const_of_neg (by linarith))
    have h3 : (fun R : ℝ => Real.exp R ^ (e - 1) / (1 - e)) = fun R : ℝ => Real.exp (R * (e - 1)) / (1 - e) := by
      funext R
      rw [← Real.exp_mul]
    rw [h3]
    simpa using h2.div_const (1 - e)
  simpa using ENNReal.tendsto_ofReal h1

private theorem tendsto_const_mul_nhds_zero {α : Type*} {l : Filter α} {c : ℝ≥0∞} (hc : c ≠ ∞) {ε : α → ℝ≥0∞}
    (hε : Tendsto ε l (𝓝 0)) : Tendsto (fun a => c * ε a) l (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul (a := c) hε (Or.inr hc)
  rwa [mul_zero] at h

end ShellTails

section TruncatedBracketValue

variable (F : Type) [Field F] [NumberField F]

private theorem lintegral_tsum_indicator_mul_enorm_le
    (cq : ℝ≥0∞)
    (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
      ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
        (∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) =
          cq * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F)
                    F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (V : ℝ≥0∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hHm : Measurable (NumberField.AdelicHeight.adelicHeight F))
    (hHinv : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
        NumberField.AdelicHeight.adelicHeight F (x * g) = NumberField.AdelicHeight.adelicHeight F g)
    (hH : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.centralScalar (𝓞 F) F z *
          NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F)) = NumberField.TateGlobal.ideleNorm F t)
    (hN : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 F) F z *
          NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        NumberField.TateGlobal.ideleNorm F z ^ 2 * NumberField.TateGlobal.ideleNorm F t)
    (hhB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
        NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g) =
        NumberField.AdelicHeight.adelicHeight F g)
    (hhN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
        NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.unipotentGL2 u * g) =
        NumberField.AdelicHeight.adelicHeight F g)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd : d₁ ≤ d₂)
    (hS : MeasurableSet {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)
        ∈ Set.Icc d₁ d₂})
    (hSΓ : ∀ γ ∈ (AutomorphicForm.globalPoints (𝓞 F) F).range, ∀ g : AdelicGL2 (𝓞 F) F,
        γ * g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc d₁ d₂} ↔ g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hSH : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
        x * g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc d₁ d₂} ↔ g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    {Φ : Set (AdelicGL2 (𝓞 F) F)} (hΦm : MeasurableSet Φ) (hΦS : Φ ⊆ {g : AdelicGL2 (𝓞 F) F |
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁
        d₂}))
    {ψ : AdelicGL2 (𝓞 F) F → ℂ} (hψm : Measurable ψ)
    (hψB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
        ψ (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = ψ g)
    (hψN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), ψ (AutomorphicForm.unipotentGL2 u * g) = ψ g)
    {e C : ℝ} (hbd : ∀ g : AdelicGL2 (𝓞 F) F,
        ‖ψ g‖ ≤ C * NumberField.AdelicHeight.adelicHeight F g ^ e) (W : Set ℝ) (hW : MeasurableSet W) :
    ∫⁻ g in Φ, ∑' τ : Option F,
        W.indicator 1 (NumberField.AdelicHeight.adelicHeight F (bruhatRep (F := F) τ * g)) * ‖ψ (bruhatRep (F := F) τ
        * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      ≤ ENNReal.ofReal (max C 0) * (cq * (V * (V * (ENNReal.ofReal (Real.log (d₂ / d₁) / 2) * ∫⁻ y in Set.Ioi (0 : ℝ),
          (W).indicator 1 y * ENNReal.ofReal (y ^ e) * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹)))) := by
  have hfm : Measurable fun x : AdelicGL2 (𝓞 F) F => W.indicator 1 (NumberField.AdelicHeight.adelicHeight F x) * ‖ψ
      x‖ₑ :=
    ((measurable_one.indicator hW).comp hHm).mul hψm.enorm
  have hfB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      W.indicator 1 (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g)) * ‖ψ
          (AutomorphicForm.globalPoints (𝓞 F) F γ * g)‖ₑ = W.indicator 1 (NumberField.AdelicHeight.adelicHeight F g) *
          ‖ψ g‖ₑ := by
    intro γ hγ g
    rw [hhB γ hγ g, hψB γ hγ g]
  have hfN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      W.indicator 1 (NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.unipotentGL2 u * g)) * ‖ψ
          (AutomorphicForm.unipotentGL2 u * g)‖ₑ = W.indicator 1 (NumberField.AdelicHeight.adelicHeight F g) * ‖ψ g‖ₑ
          := by
    intro u g
    rw [hhN u g, hψN u g]
  have hfw : ∀ g : AdelicGL2 (𝓞 F) F,
      W.indicator 1 (NumberField.AdelicHeight.adelicHeight F g) * ‖ψ g‖ₑ ≤ ENNReal.ofReal (max C 0) * (W.indicator 1
          (NumberField.AdelicHeight.adelicHeight F g) * ENNReal.ofReal (NumberField.AdelicHeight.adelicHeight F g ^
          e)) := by
    intro g
    by_cases hg : NumberField.AdelicHeight.adelicHeight F g ∈ W
    · rw [Set.indicator_of_mem hg, Pi.one_apply, one_mul, one_mul, ← ENNReal.ofReal_mul (le_max_right _ _),
        ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hbd g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (NumberField.AdelicHeight.adelicHeight_pos g).le _)))
    · rw [Set.indicator_of_notMem hg, zero_mul, zero_mul, mul_zero]
  exact setLIntegral_tsum_bruhatRep_mul_le F cq hc D hDm hDF V hV hHm hHinv hH hN (ENNReal.ofReal (Real.log (d₂ / d₁)
      / 2))
    (fun y hy => lintegral_indicator_sq_mul_mul_ofReal_inv hd₁ hd hy)
    ((measurable_one.indicator hW).mul (measurable_id.pow_const e).ennreal_ofReal) hS hSΓ hSH (fun _ hg => hg) hΦm hΦS
        hΦ
    hfm hfB hfN (ENNReal.ofReal (max C 0)) ENNReal.ofReal_ne_top hfw

private theorem ofReal_mul_shell_Ioc_ne_top {cq V : ℝ≥0∞} (hcT : cq ≠ ∞) (hVT : V ≠ ∞) (c₀ : ℝ) {d₁ d₂ T e : ℝ}
    (hT : 0 < T) (he : 1 < e) :
    ENNReal.ofReal c₀ * (cq * (V * (V * (ENNReal.ofReal (Real.log (d₂ / d₁) / 2) * ∫⁻ y in Set.Ioi (0 : ℝ),
        (Set.Ioc 0 T).indicator 1 y * ENNReal.ofReal (y ^ e) * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹)))) ≠ ∞ := by
  rw [setLIntegral_indicator_mul_ofReal_rpow_mul_inv_mul_inv, lintegral_indicator_Ioc_mul_ofReal_rpow hT he]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hcT (ENNReal.mul_ne_top hVT (ENNReal.mul_ne_top
      hVT
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))))

private theorem ofReal_mul_shell_Ioi_ne_top {cq V : ℝ≥0∞} (hcT : cq ≠ ∞) (hVT : V ≠ ∞) (c₀ : ℝ) {d₁ d₂ T e : ℝ}
    (hT : 0 < T) (he : e < 1) :
    ENNReal.ofReal c₀ * (cq * (V * (V * (ENNReal.ofReal (Real.log (d₂ / d₁) / 2) * ∫⁻ y in Set.Ioi (0 : ℝ),
        (Set.Ioi T).indicator 1 y * ENNReal.ofReal (y ^ e) * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹)))) ≠ ∞ := by
  rw [setLIntegral_indicator_mul_ofReal_rpow_mul_inv_mul_inv, lintegral_indicator_Ioi_mul_ofReal_rpow hT he]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hcT (ENNReal.mul_ne_top hVT (ENNReal.mul_ne_top
      hVT
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))))

private theorem tendsto_ofReal_mul_shell_Ioc_exp {cq V : ℝ≥0∞} (hcT : cq ≠ ∞) (hVT : V ≠ ∞) (c₀ : ℝ) {d₁ d₂ e : ℝ}
    (he : 1 < e) {ρ : ℝ → ℝ} (hρ : Filter.Tendsto ρ Filter.atBot Filter.atBot) :
    Filter.Tendsto (fun R : ℝ => ENNReal.ofReal c₀ * (cq * (V * (V * (ENNReal.ofReal (Real.log (d₂ / d₁) / 2) *
      ∫⁻ y in Set.Ioi (0 : ℝ),
          (Set.Ioc 0 (Real.exp (ρ R))).indicator 1 y * ENNReal.ofReal (y ^ e) * ENNReal.ofReal y⁻¹ * ENNReal.ofReal
          y⁻¹))))) Filter.atBot (nhds 0) := by
  have hsh : ∀ R : ℝ, ∫⁻ y in Set.Ioi (0 : ℝ),
      (Set.Ioc 0 (Real.exp (ρ R))).indicator 1 y * ENNReal.ofReal (y ^ e) * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ =
      ENNReal.ofReal (Real.exp (ρ R) ^ (e - 1) / (e - 1)) := fun R => by
    rw [setLIntegral_indicator_mul_ofReal_rpow_mul_inv_mul_inv,
        lintegral_indicator_Ioc_mul_ofReal_rpow (Real.exp_pos _) he]
  simp_rw [hsh]
  exact tendsto_const_mul_nhds_zero ENNReal.ofReal_ne_top (tendsto_const_mul_nhds_zero hcT
      (tendsto_const_mul_nhds_zero hVT
    (tendsto_const_mul_nhds_zero hVT (tendsto_const_mul_nhds_zero ENNReal.ofReal_ne_top
      ((tendsto_ofReal_exp_rpow_div_atBot he).comp hρ)))))

private theorem tendsto_ofReal_mul_shell_Ioi_exp {cq V : ℝ≥0∞} (hcT : cq ≠ ∞) (hVT : V ≠ ∞) (c₀ : ℝ) {d₁ d₂ e : ℝ}
    (he : e < 1) {ρ : ℝ → ℝ} (hρ : Filter.Tendsto ρ Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun R : ℝ => ENNReal.ofReal c₀ * (cq * (V * (V * (ENNReal.ofReal (Real.log (d₂ / d₁) / 2) *
      ∫⁻ y in Set.Ioi (0 : ℝ),
          (Set.Ioi (Real.exp (ρ R))).indicator 1 y * ENNReal.ofReal (y ^ e) * ENNReal.ofReal y⁻¹ * ENNReal.ofReal
          y⁻¹))))) Filter.atTop (nhds 0) := by
  have hsh : ∀ R : ℝ, ∫⁻ y in Set.Ioi (0 : ℝ),
      (Set.Ioi (Real.exp (ρ R))).indicator 1 y * ENNReal.ofReal (y ^ e) * ENNReal.ofReal y⁻¹ * ENNReal.ofReal y⁻¹ =
      ENNReal.ofReal (Real.exp (ρ R) ^ (e - 1) / (1 - e)) := fun R => by
    rw [setLIntegral_indicator_mul_ofReal_rpow_mul_inv_mul_inv,
        lintegral_indicator_Ioi_mul_ofReal_rpow (Real.exp_pos _) he]
  simp_rw [hsh]
  exact tendsto_const_mul_nhds_zero ENNReal.ofReal_ne_top (tendsto_const_mul_nhds_zero hcT
      (tendsto_const_mul_nhds_zero hVT
    (tendsto_const_mul_nhds_zero hVT (tendsto_const_mul_nhds_zero ENNReal.ofReal_ne_top
      ((tendsto_ofReal_exp_rpow_div_atTop he).comp hρ)))))

private theorem enorm_indicator_Ioc_mul_le (T : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    ‖(Set.Ioc 0 T).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * φ x‖ₑ ≤ (Set.Ioc 0
        T).indicator 1 (NumberField.AdelicHeight.adelicHeight F x) * ‖φ x‖ₑ := by
  by_cases hx : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc 0 T
  · simp only [Set.indicator_of_mem hx, Pi.one_apply, one_mul, le_refl]
  · simp only [Set.indicator_of_notMem hx, zero_mul, enorm_zero, zero_le]

private theorem enorm_indicator_Ioi_mul_le (T : ℝ) (m : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    ‖(Set.Ioi T).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * m x‖ₑ ≤ (Set.Ioi
        T).indicator 1 (NumberField.AdelicHeight.adelicHeight F x) * ‖m x‖ₑ := by
  by_cases hx : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioi T
  · simp only [Set.indicator_of_mem hx, Pi.one_apply, one_mul, le_refl]
  · simp only [Set.indicator_of_notMem hx, zero_mul, enorm_zero, zero_le]

private theorem enorm_brT_le (T : ℝ) (φ m : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    ‖brT T φ m x‖ₑ ≤ (Set.Ioc 0 T).indicator 1 (NumberField.AdelicHeight.adelicHeight F x) * ‖φ x‖ₑ + (Set.Ioi
        T).indicator 1 (NumberField.AdelicHeight.adelicHeight F x) * ‖m x‖ₑ :=
  (enorm_sub_le ..).trans (add_le_add (enorm_indicator_Ioc_mul_le F T φ x) (enorm_indicator_Ioi_mul_le F T m x))

private theorem enorm_heightBand_low_le {r : ℝ} (hr : 0 < r) (T : ℝ) (φ : AdelicGL2 (𝓞 F) F →
    ℂ) (x : AdelicGL2 (𝓞 F) F) :
    ‖heightBand F r T φ x‖ₑ ≤ (Set.Ioc 0 T).indicator 1 (NumberField.AdelicHeight.adelicHeight F x) * ‖φ x‖ₑ := by
  rw [heightBand_apply]
  by_cases hx : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc r T
  · have hx' : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc 0 T := ⟨hr.trans hx.1, hx.2⟩
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Pi.one_apply, one_mul, le_refl]
  · simp only [Set.indicator_of_notMem hx, zero_mul, enorm_zero, zero_le]

private theorem enorm_heightBand_high_le (T r : ℝ) (m : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    ‖heightBand F T r m x‖ₑ ≤ (Set.Ioi T).indicator 1 (NumberField.AdelicHeight.adelicHeight F x) * ‖m x‖ₑ := by
  rw [heightBand_apply]
  by_cases hx : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc T r
  · have hx' : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioi T := hx.1
    simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hx', Pi.one_apply, one_mul, le_refl]
  · simp only [Set.indicator_of_notMem hx, zero_mul, enorm_zero, zero_le]

private theorem enorm_indicator_Ioc_mul_sub_heightBand_le {r : ℝ} (_hr : 0 < r) (T : ℝ) (φ : AdelicGL2 (𝓞 F) F →
    ℂ) (x : AdelicGL2 (𝓞 F) F) :
    ‖(Set.Ioc 0 T).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * φ x - heightBand F r T φ
        x‖ₑ
      ≤ (Set.Ioc 0 r).indicator 1 (NumberField.AdelicHeight.adelicHeight F x) * ‖φ x‖ₑ := by
  rw [heightBand_apply]
  by_cases h1 : NumberField.AdelicHeight.adelicHeight F x ≤ r
  · have hnot : NumberField.AdelicHeight.adelicHeight F x ∉ Set.Ioc r T := fun hx => absurd hx.1 (not_lt.mpr h1)
    have hin : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc 0 r := ⟨NumberField.AdelicHeight.adelicHeight_pos
        x, h1⟩
    rw [Set.indicator_of_notMem hnot, zero_mul, sub_zero, Set.indicator_of_mem hin, Pi.one_apply, one_mul]
    by_cases h2 : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc 0 T
    · simp only [Set.indicator_of_mem h2, one_mul, le_refl]
    · simp only [Set.indicator_of_notMem h2, zero_mul, enorm_zero, zero_le]
  · rw [not_le] at h1
    by_cases h2 : NumberField.AdelicHeight.adelicHeight F x ≤ T
    · have hA : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc 0 T := ⟨NumberField.AdelicHeight.adelicHeight_pos
        x, h2⟩
      have hB : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc r T := ⟨h1, h2⟩
      simp only [Set.indicator_of_mem hA, Set.indicator_of_mem hB, one_mul, sub_self, enorm_zero, zero_le]
    · rw [not_le] at h2
      have hA : NumberField.AdelicHeight.adelicHeight F x ∉ Set.Ioc 0 T := fun hx => absurd hx.2 (not_le.mpr h2)
      have hB : NumberField.AdelicHeight.adelicHeight F x ∉ Set.Ioc r T := fun hx => absurd hx.2 (not_le.mpr h2)
      simp only [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB, zero_mul, sub_self, enorm_zero, zero_le]

private theorem enorm_indicator_Ioi_mul_sub_heightBand_le (T r : ℝ) (m : AdelicGL2 (𝓞 F) F →
    ℂ) (x : AdelicGL2 (𝓞 F) F) :
    ‖(Set.Ioi T).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * m x - heightBand F T r m
        x‖ₑ
      ≤ (Set.Ioi r).indicator 1 (NumberField.AdelicHeight.adelicHeight F x) * ‖m x‖ₑ := by
  rw [heightBand_apply]
  by_cases h1 : T < NumberField.AdelicHeight.adelicHeight F x
  · by_cases h2 : NumberField.AdelicHeight.adelicHeight F x ≤ r
    · have hA : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioi T := h1
      have hB : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc T r := ⟨h1, h2⟩
      simp only [Set.indicator_of_mem hA, Set.indicator_of_mem hB, one_mul, sub_self, enorm_zero, zero_le]
    · rw [not_le] at h2
      have hA : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioi T := h1
      have hB : NumberField.AdelicHeight.adelicHeight F x ∉ Set.Ioc T r := fun hx => absurd hx.2 (not_le.mpr h2)
      have hC : NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioi r := h2
      simp only [Set.indicator_of_mem hA, Set.indicator_of_notMem hB, Set.indicator_of_mem hC, Pi.one_apply, one_mul,
        zero_mul, sub_zero, le_refl]
  · have hA : NumberField.AdelicHeight.adelicHeight F x ∉ Set.Ioi T := h1
    have hB : NumberField.AdelicHeight.adelicHeight F x ∉ Set.Ioc T r := fun hx => absurd hx.1 h1
    simp only [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB, zero_mul, sub_self, enorm_zero, zero_le]

private theorem isInducedSection_const_mul {η₁ η₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (b : ℂ) {m : AdelicGL2 (𝓞 F) F → ℂ}
    (hm : IsInducedSection (𝓞 F) F η₁ η₂ m) : IsInducedSection (𝓞 F) F η₁ η₂ (fun g => b * m g) := by
  intro x hx g
  simp only
  rw [hm x hx g]
  ring

private theorem lintegral_tsum_enorm_le_of_forall {Φ : Set (AdelicGL2 (𝓞 F) F)} {ψ : AdelicGL2 (𝓞 F) F →
    ℂ} {M : AdelicGL2 (𝓞 F) F → ℝ≥0∞}
    (hle : ∀ x, ‖ψ x‖ₑ ≤ M x) :
    ∫⁻ g in Φ, ∑' τ : Option F, ‖ψ (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤ ∫⁻ g in Φ,
        ∑' τ : Option F, M (bruhatRep (F := F) τ * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
  lintegral_mono fun g => ENNReal.tsum_le_tsum fun τ => hle (bruhatRep (F := F) τ * g)

private theorem integrableOn_pseudoEisenstein_brT_adaptedDomain
    (cq : ℝ≥0∞) (hcT : cq ≠ ∞)
    (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
      ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
        (∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) =
          cq * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F)
                    F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (V : ℝ≥0∞) (hVT : V ≠ ∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (hHm : Measurable (NumberField.AdelicHeight.adelicHeight F))
    (hHinv : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
        NumberField.AdelicHeight.adelicHeight F (x * g) = NumberField.AdelicHeight.adelicHeight F g)
    (hH : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.centralScalar (𝓞 F) F z *
          NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F)) = NumberField.TateGlobal.ideleNorm F t)
    (hN : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 F) F z *
          NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
        NumberField.TateGlobal.ideleNorm F z ^ 2 * NumberField.TateGlobal.ideleNorm F t)
    (hhB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
        NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g) =
        NumberField.AdelicHeight.adelicHeight F g)
    (hhN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
        NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.unipotentGL2 u * g) =
        NumberField.AdelicHeight.adelicHeight F g)
    (d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hS : MeasurableSet {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g)
        ∈ Set.Icc d₁ d₂})
    (hSΓ : ∀ γ ∈ (AutomorphicForm.globalPoints (𝓞 F) F).range, ∀ g : AdelicGL2 (𝓞 F) F,
        γ * g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc d₁ d₂} ↔ g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hSH : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
        x * g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc d₁ d₂} ↔ g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (T : ℝ) (hT : 1 ≤ T) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (hΦ₀m : MeasurableSet Φ₀) (hΦ₀s : Φ₀ ⊆ {g : AdelicGL2 (𝓞 F) F
        | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F)
        F).restrict {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc d₁ d₂}))
    (s : ℂ) (hs : 1 / 2 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    (hφB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
        φ (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = φ g)
    (hφN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), φ (AutomorphicForm.unipotentGL2 u * g) = φ g)
    (Cφ : ℝ) (hφbd : ∀ g : AdelicGL2 (𝓞 F) F, ‖φ g‖ ≤ Cφ * NumberField.AdelicHeight.adelicHeight F g ^ (s.re + 1 / 2))
    (m : AdelicGL2 (𝓞 F) F → ℂ) (hmc : Continuous m)
    (hmB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
        m (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = m g)
    (hmN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), m (AutomorphicForm.unipotentGL2 u * g) = m g)
    (Cm : ℝ) (hmbd : ∀ g : AdelicGL2 (𝓞 F) F,
        ‖m g‖ ≤ Cm * NumberField.AdelicHeight.adelicHeight F g ^ ((-s).re + 1 / 2)) :
    IntegrableOn (AutomorphicForm.pseudoEisenstein F (brT T φ m)) (adaptedDomain F T Φ₀) (adelicGLHaar (Fin 2) (𝓞 F)
        F) := by
  haveI : Countable F := countable_field (F := F)
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT
  have heφ : (1 : ℝ) < s.re + 1 / 2 := by linarith
  have hem : (-s).re + 1 / 2 < (1 : ℝ) := by rw [Complex.neg_re]; linarith
  have hΦm := measurableSet_adaptedDomain (F := F) (T := T) hΦ₀m
  have hΦS := adaptedDomain_subset (F := F) (T := T) hΦ₀s
  have hΦ := isFundamentalDomain_adaptedDomain (F := F) hT hΦ₀m hΦ₀
  have hMφ := lintegral_tsum_indicator_mul_enorm_le F cq hc D hDm hDF V hV hHm hHinv hH hN hhB hhN hd₁ hd.le hS hSΓ
      hSH hΦm hΦS hΦ hφc.measurable hφB
    hφN hφbd (Set.Ioc 0 T) measurableSet_Ioc
  have hMm := lintegral_tsum_indicator_mul_enorm_le F cq hc D hDm hDF V hV hHm hHinv hH hN hhB hhN hd₁ hd.le hS hSΓ
      hSH hΦm hΦS hΦ hmc.measurable hmB
    hmN hmbd (Set.Ioi T) measurableSet_Ioi
  have hmeas : Measurable fun g : AdelicGL2 (𝓞 F) F =>
      ∑' τ : Option F, (Set.Ioc 0 T).indicator 1 (NumberField.AdelicHeight.adelicHeight F (bruhatRep (F := F) τ * g))
          * ‖φ (bruhatRep (F := F) τ * g)‖ₑ :=
    measurable_tsum_ennreal fun τ => ((measurable_one.indicator measurableSet_Ioc).comp (hHm.comp
        (measurable_const_mul _))).mul
      (hφc.measurable.comp (measurable_const_mul _)).enorm
  have hbrTm : Measurable (brT T φ m) :=
    (((measurable_const.indicator measurableSet_Ioc).comp hHm).mul hφc.measurable).sub
      (((measurable_const.indicator measurableSet_Ioi).comp hHm).mul hmc.measurable)
  refine integrableOn_pseudoEisenstein_of_lintegral_tsum_bruhatRep_ne_top F hbrTm (ne_top_of_le_ne_top ?_
    (lintegral_tsum_enorm_le_of_forall F (enorm_brT_le F T φ m)))
  calc ∫⁻ g in adaptedDomain F T Φ₀, ∑' τ : Option F,
          ((Set.Ioc 0 T).indicator 1 (NumberField.AdelicHeight.adelicHeight F (bruhatRep (F := F) τ * g)) * ‖φ
              (bruhatRep (F := F) τ * g)‖ₑ +
            (Set.Ioi T).indicator 1 (NumberField.AdelicHeight.adelicHeight F (bruhatRep (F := F) τ * g)) * ‖m
                (bruhatRep (F := F) τ * g)‖ₑ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        = (∫⁻ g in adaptedDomain F T Φ₀, ∑' τ : Option F,
              (Set.Ioc 0 T).indicator 1 (NumberField.AdelicHeight.adelicHeight F (bruhatRep (F := F) τ * g)) * ‖φ
                  (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) +
            ∫⁻ g in adaptedDomain F T Φ₀, ∑' τ : Option F,
              (Set.Ioi T).indicator 1 (NumberField.AdelicHeight.adelicHeight F (bruhatRep (F := F) τ * g)) * ‖m
                  (bruhatRep (F := F) τ * g)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
          simp_rw [ENNReal.tsum_add]
          exact lintegral_add_left hmeas _
    _ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top (ofReal_mul_shell_Ioc_ne_top hcT hVT _ hT0 heφ) hMφ,
          ne_top_of_le_ne_top (ofReal_mul_shell_Ioi_ne_top hcT hVT _ hT0 hem) hMm⟩

end TruncatedBracketValue

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section IwasawaAlgebra

variable {A : Type*} [CommRing A]

private theorem diagOne_mul_unipotentGL2 (t : Aˣ) (x : A) :
    diagOne t * unipotentGL2 x = unipotentGL2 ((t : A) * x) * diagOne t := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [diagOne_coe_apply, unipotentGL2_coe]

private theorem det_diagOne (t : Aˣ) : Matrix.GeneralLinearGroup.det (diagOne t) = t := by
  apply Units.ext
  show (Matrix.diagonal ![(t : A), 1]).det = (t : A)
  simp [Matrix.det_diagonal, Fin.prod_univ_two]

end IwasawaAlgebra

section QuotientConstant

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
  NumberField.Idele.isHaarMeasure_idelicHaar

private theorem globalPoints_unitsMap_scalar (γ : Fˣ) :
    globalPoints (𝓞 F) F
        (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom γ) =
      centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply (𝓞 F) F _ i j]
  fin_cases i <;> fin_cases j <;>
    simp [centralScalar, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]

private theorem globalPoints_diagOne (δ : Fˣ) :
    globalPoints (𝓞 F) F (diagOne δ) =
      diagOne (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply (𝓞 F) F _ i j]
  fin_cases i <;> fin_cases j <;> simp [diagOne_coe_apply]

private theorem centralScalar_mul_comm (u : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F u * g = g * centralScalar (𝓞 F) F u := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 F) F)
  exact (Matrix.scalar_commute (u : AdeleRing (𝓞 F) F) (fun r => Commute.all _ r) _).eq

private theorem centralScalar_mul_diagOne_mul_unipotentGL2_mul (γ δ z t : (AdeleRing (𝓞 F) F)ˣ) (x : AdeleRing (𝓞 F) F)
    (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F γ * diagOne δ * unipotentGL2 x * (centralScalar (𝓞 F) F z * diagOne t * g) =
      unipotentGL2 ((δ : AdeleRing (𝓞 F) F) * x) * centralScalar (𝓞 F) F (γ * z) * diagOne (δ * t) * g := by
  rw [map_mul, map_mul,
    show centralScalar (𝓞 F) F γ * diagOne δ * unipotentGL2 x =
        unipotentGL2 ((δ : AdeleRing (𝓞 F) F) * x) * centralScalar (𝓞 F) F γ * diagOne δ by
      rw [mul_assoc, diagOne_mul_unipotentGL2, ← mul_assoc, centralScalar_mul_comm],
    show unipotentGL2 ((δ : AdeleRing (𝓞 F) F) * x) * centralScalar (𝓞 F) F γ * diagOne δ *
          (centralScalar (𝓞 F) F z * diagOne t * g) =
        unipotentGL2 ((δ : AdeleRing (𝓞 F) F) * x) * centralScalar (𝓞 F) F γ *
          (diagOne δ * centralScalar (𝓞 F) F z) * diagOne t * g by
      simp only [mul_assoc],
    ← centralScalar_mul_comm z (diagOne δ)]
  simp only [mul_assoc]

private theorem coe_toAdelicUnipotent (x : AdeleRing (𝓞 F) F) :
    ((toAdelicUnipotent F x : adelicUnipotent F) : AdelicGL2 (𝓞 F) F) = unipotentGL2 x :=
  rfl

private theorem ideleNorm_unitsMap_algebraMap (δ : Fˣ) :
    NumberField.TateGlobal.ideleNorm F
        (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ) = 1 := by
  have h := AutomorphicForm.ideleNorm_det_globalPoints (F := F) (diagOne δ)
  rwa [globalPoints_diagOne, det_diagOne] at h

private theorem distribHaarChar_unitsMap_algebraMap (δ : Fˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F)
        (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ) = 1 := by
  have h := ideleNorm_unitsMap_algebraMap δ
  rw [NumberField.TateGlobal.ideleNorm] at h
  exact_mod_cast h

private theorem regular_adelicAddHaar : (adelicAddHaar (𝓞 F) F).Regular :=
  Measure.regular_addHaarMeasure

private theorem lintegral_comp_algebraMap_mul (δ : Fˣ) (f : AdeleRing (𝓞 F) F → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f (algebraMap F (AdeleRing (𝓞 F) F) δ * x) ∂(adelicAddHaar (𝓞 F) F) =
      ∫⁻ x, f x ∂(adelicAddHaar (𝓞 F) F) := by
  haveI := regular_adelicAddHaar (F := F)
  have hmap : Measure.map (fun x => algebraMap F (AdeleRing (𝓞 F) F) δ * x) (adelicAddHaar (𝓞 F) F) =
      adelicAddHaar (𝓞 F) F := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (measurable_const_mul _) hs]
    show adelicAddHaar (𝓞 F) F
        ((fun x => (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ) • x) ⁻¹' s) = _
    rw [Set.preimage_smul, ← distribHaarChar_mul (adelicAddHaar (𝓞 F) F) _ s, map_inv,
      distribHaarChar_unitsMap_algebraMap, inv_one, ENNReal.coe_one, one_mul]
  rw [← lintegral_map hf (measurable_const_mul _), hmap]

private theorem continuous_adeleRing_unipotentGL2 :
    Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ x : AdeleRing (𝓞 F) F,
        (((unipotentGL2 x)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, -x; 0, 1] :=
      fun _ => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

private theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  have hv : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      ((centralScalar (𝓞 F) F u : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
        Matrix.diagonal fun _ => (u : AdeleRing (𝓞 F) F) := fun _ => rfl
  have hi : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (((centralScalar (𝓞 F) F u)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
        Matrix.diagonal fun _ => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := fun u => by
    rw [← map_inv]
    rfl
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, hv]
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact Units.continuous_val
  · simp_rw [hi]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact Units.continuous_coe_inv

private theorem continuous_diagOne : Continuous (diagOne : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  have hv : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
        Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1] := fun _ => rfl
  have hi : ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      (((diagOne t)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
        Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1] := fun t => by
    rw [← map_inv]
    rfl
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, hv]
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact Units.continuous_val
  · simp_rw [hi]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact Units.continuous_coe_inv

private theorem lintegral_rationalTorusUnipotentHaar_comp_mul (H : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hH : Measurable H)
    (g : AdelicGL2 (𝓞 F) F) :
    ∫⁻ y, H ((y : AdelicGL2 (𝓞 F) F) * g) ∂(rationalTorusUnipotentHaar F) =
      ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ *
        ∑' za : Fˣ × Fˣ, ∫⁻ x,
          H (centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1) *
            diagOne (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2) * unipotentGL2 x * g)
          ∂(adelicAddHaar (𝓞 F) F) := by
  have hf : Measurable fun y : rationalTorusUnipotent F => H ((y : AdelicGL2 (𝓞 F) F) * g) :=
    hH.comp (continuous_subtype_val.mul continuous_const).measurable
  have hu : Measurable (toAdelicUnipotent F) :=
    (continuous_induced_rng.2 continuous_adeleRing_unipotentGL2).measurable
  simp only [rationalTorusUnipotentHaar, unipotentHaar, lintegral_sum_measure]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun za => ?_
  have hT : Measurable fun n : adelicUnipotent F =>
      (⟨globalPoints (𝓞 F) F
            (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom za.1) *
          globalPoints (𝓞 F) F (diagOne za.2) * (n : AdelicGL2 (𝓞 F) F),
        Subgroup.mul_mem_sup (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩) n.2⟩ : rationalTorusUnipotent F) :=
    (Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _).measurable
  rw [lintegral_map hf hT,
    lintegral_map (show Measurable fun n : adelicUnipotent F => H (((⟨globalPoints (𝓞 F) F
            (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom za.1) *
          globalPoints (𝓞 F) F (diagOne za.2) * (n : AdelicGL2 (𝓞 F) F),
        Subgroup.mul_mem_sup (Subgroup.mul_mem_sup ⟨za.1, rfl⟩ ⟨za.2, rfl⟩) n.2⟩ : rationalTorusUnipotent F) :
          AdelicGL2 (𝓞 F) F) * g) from hf.comp hT) hu,
    lintegral_smul_measure, smul_eq_mul]
  refine congrArg (fun I => ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * I) (lintegral_congr fun x => ?_)
  rw [← globalPoints_unitsMap_scalar, ← globalPoints_diagOne, ← coe_toAdelicUnipotent (F := F) x]

private theorem countable_units : Countable Fˣ :=
  haveI : Countable F := Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  Units.val_injective.countable

private def principalIdeleEquiv : Fˣ ≃ M4aHerbrand.principalIdeles (𝓞 F) F :=
  Equiv.ofBijective
    (fun γ => ⟨Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ, γ, rfl⟩)
    ⟨fun a b h => by
      have h' := congrArg (fun u : (AdeleRing (𝓞 F) F)ˣ => (u : AdeleRing (𝓞 F) F)) (congrArg Subtype.val h)
      simp only [Units.coe_map, MonoidHom.coe_coe] at h'
      exact Units.val_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F h'),
     by rintro ⟨_, γ, rfl⟩; exact ⟨γ, rfl⟩⟩

private theorem lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_measure_adelicBox_mul
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (_hcT : c ≠ ∞)
    (hc : ∀ H : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable H →
      ∫⁻ g, H g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
              H (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
            ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(adelicAddHaar (𝓞 F) F)) :
    ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
      ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure F) =
          c * adelicAddHaar (𝓞 F) F (adelicBox F) * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := by
  intro D D' hD hD' hDF hD'F
  obtain ⟨c', -, -, hlaw⟩ :=
    AutomorphicForm.exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa F
  suffices hcc : c' = c * adelicAddHaar (𝓞 F) F (adelicBox F) by
    intro f hf hinv
    rw [← hcc]
    exact hlaw D D' hD hD' hDF hD'F f hf hinv

  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := Units.isInducing_embedProduct.secondCountableTopology
  haveI : T2Space (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.t2Space_adeleRing (𝓞 F) F
  haveI : LocallyCompactSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.locallyCompactSpace_adeleRing (𝓞 F) F
  haveI : LocallyCompactSpace (AdeleRing (𝓞 F) F)ᵐᵒᵖ := MulOpposite.instLocallyCompactSpace
  haveI : LocallyCompactSpace (AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ᵐᵒᵖ) := Prod.locallyCompactSpace _ _
  haveI : LocallyCompactSpace (AdeleRing (𝓞 F) F)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SigmaCompactSpace (AdeleRing (𝓞 F) F)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : (NumberField.Idele.idelicHaar F).IsHaarMeasure := NumberField.Idele.isHaarMeasure_idelicHaar F
  haveI : SigmaFinite (NumberField.Idele.idelicHaar F) := Measure.IsHaarMeasure.sigmaFinite _
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨hHM, hRI⟩ := AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F
  haveI := hHM
  haveI := hRI
  have hcl := AutomorphicForm.isClosed_rationalTorusUnipotent F
  haveI : SigmaCompactSpace (rationalTorusUnipotent F) := hcl.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  haveI : Countable Fˣ := countable_units
  haveI : Countable (M4aHerbrand.principalIdeles (𝓞 F) F) :=
    (principalIdeleEquiv (F := F)).symm.injective.countable
  have hb0 : (adelicAddHaar (𝓞 F) F) (adelicBox F) ≠ 0 := (adelicAddHaar_adelicBox_pos F).ne'
  have hbT : (adelicAddHaar (𝓞 F) F) (adelicBox F) ≠ ∞ := (adelicAddHaar_adelicBox_lt_top F).ne
  have hbi : ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hb0

  obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 F) F)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hH₀ : Measurable (C.indicator (1 : AdelicGL2 (𝓞 F) F → ℝ≥0∞)) := measurable_one.indicator hCm
  have hCpos : adelicGLHaar (Fin 2) (𝓞 F) F C ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.2 hC1⟩).ne'
  have hCfin : adelicGLHaar (Fin 2) (𝓞 F) F C ≠ ∞ := hCc.measure_lt_top.ne
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ≥0∞, J = ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
      C.indicator 1 (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
        ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
      ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
      ∂(adelicAddHaar (𝓞 F) F) := ⟨_, rfl⟩
  have hJ := hc _ hH₀
  rw [lintegral_indicator_one hCm, ← hJdef] at hJ
  have hJ0 : J ≠ 0 := fun h => hCpos (by rw [hJ, h, mul_zero])
  have hJT : J ≠ ∞ := fun h => hCfin (by rw [hJ, h, ENNReal.mul_top hc0])

  obtain ⟨w, hw⟩ : ∃ w : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞,
      ∀ t, w t = ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) := ⟨_, fun _ => rfl⟩
  have hwm : Measurable w := by
    rw [show w = fun t => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) from funext hw]
    exact ENNReal.measurable_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F).measurable.inv
  have hwδ : ∀ (δ : Fˣ) (t : (AdeleRing (𝓞 F) F)ˣ),
      w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) = w t := fun δ t => by
    rw [hw, hw, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_unitsMap_algebraMap, one_mul]
  have hM : Measurable fun p :
      ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) × AdeleRing (𝓞 F) F =>
      C.indicator 1
        (unipotentGL2 p.2 * centralScalar (𝓞 F) F p.1.1 * diagOne p.1.2.1 * (p.1.2.2 : AdelicGL2 (𝓞 F) F)) :=
    hH₀.comp ((((continuous_adeleRing_unipotentGL2.measurable.comp measurable_snd).mul
      (continuous_centralScalar.measurable.comp measurable_fst.fst)).mul
      (continuous_diagOne.measurable.comp measurable_fst.snd.fst)).mul
      (measurable_subtype_coe.comp measurable_fst.snd.snd))
  obtain ⟨K, hK⟩ : ∃ K : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → ℝ≥0∞,
      ∀ z t k, K z t k = ∫⁻ x, C.indicator 1 (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t *
        (k : AdelicGL2 (𝓞 F) F)) ∂(adelicAddHaar (𝓞 F) F) := ⟨_, fun _ _ _ => rfl⟩
  have hKm : Measurable fun p : (AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F =>
      K p.1 p.2.1 p.2.2 := by
    simp_rw [hK]
    refine Measurable.lintegral_prod_right ?_
    exact hM
  obtain ⟨P, hP⟩ :
      ∃ P : (AdeleRing (𝓞 F) F)ˣ → (AdeleRing (𝓞 F) F)ˣ → adelicMaximalCompact F → AdeleRing (𝓞 F) F → ℝ≥0∞,
      ∀ z t k x, P z t k x = C.indicator 1 (unipotentGL2 x * centralScalar (𝓞 F) F z * diagOne t *
        (k : AdelicGL2 (𝓞 F) F)) * w t := ⟨_, fun _ _ _ _ => rfl⟩
  have hPm : Measurable fun q :
      ((AdeleRing (𝓞 F) F)ˣ × (AdeleRing (𝓞 F) F)ˣ × adelicMaximalCompact F) × AdeleRing (𝓞 F) F =>
      P q.1.1 q.1.2.1 q.1.2.2 q.2 := by
    simp_rw [hP]
    exact hM.mul (hwm.comp measurable_fst.snd.fst)
  have hm1 : ∀ z' t' : (AdeleRing (𝓞 F) F)ˣ, Measurable fun k : adelicMaximalCompact F => K z' t' k * w t' :=
    fun z' t' => (hKm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).mul
      measurable_const
  have hm2 : ∀ z' δ' : (AdeleRing (𝓞 F) F)ˣ, Measurable fun t : (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ k, K z' (δ' * t) k * w (δ' * t) ∂(maximalCompactHaar F) := fun z' δ' => by
    refine Measurable.lintegral_prod_right ?_
    exact (hKm.comp (measurable_const.prodMk ((measurable_fst.const_mul δ').prodMk measurable_snd))).mul
      (hwm.comp (measurable_fst.const_mul δ'))
  have hm3 : ∀ γ' δ' : (AdeleRing (𝓞 F) F)ˣ, Measurable fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ t in D', ∫⁻ k, K (γ' * z) (δ' * t) k * w (δ' * t) ∂(maximalCompactHaar F)
        ∂(NumberField.Idele.idelicHaar F) := fun γ' δ' => by
    refine Measurable.lintegral_prod_right ?_
    refine Measurable.lintegral_prod_right ?_
    exact (hKm.comp ((measurable_fst.fst.const_mul γ').prodMk
        ((measurable_fst.snd.const_mul δ').prodMk measurable_snd))).mul
      (hwm.comp (measurable_fst.snd.const_mul δ'))
  have hm3' : ∀ δ' : (AdeleRing (𝓞 F) F)ˣ, Measurable fun z : (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ t in D', ∫⁻ k, K z (δ' * t) k * w (δ' * t) ∂(maximalCompactHaar F)
        ∂(NumberField.Idele.idelicHaar F) := fun δ' => by
    simpa only [one_mul] using hm3 1 δ'

  have hΦm : Measurable fun g : AdelicGL2 (𝓞 F) F =>
      ∫⁻ y, C.indicator 1 ((y : AdelicGL2 (𝓞 F) F) * g) ∂(rationalTorusUnipotentHaar F) := by
    refine Measurable.lintegral_prod_right ?_
    exact hH₀.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)
  have hΦinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      (∫⁻ y, C.indicator 1 ((y : AdelicGL2 (𝓞 F) F) * (x * g)) ∂(rationalTorusUnipotentHaar F)) =
        ∫⁻ y, C.indicator 1 ((y : AdelicGL2 (𝓞 F) F) * g) ∂(rationalTorusUnipotentHaar F) := by
    intro x hx g
    have h : ∀ y : rationalTorusUnipotent F, (y : AdelicGL2 (𝓞 F) F) * (x * g) = (y : AdelicGL2 (𝓞 F) F) * x * g :=
      fun y => (mul_assoc _ _ _).symm
    simp_rw [h]
    exact lintegral_mul_right_eq_self
      (fun y : rationalTorusUnipotent F => C.indicator 1 ((y : AdelicGL2 (𝓞 F) F) * g)) ⟨x, hx⟩
  have hlawΦ := hlaw D D' hD hD' hDF hD'F _ hΦm hΦinv
  have hW := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out (adelicGLHaar (Fin 2) (𝓞 F) F)
    (rationalTorusUnipotent F) hcl (rationalTorusUnipotentHaar F) _ hH₀
  rw [lintegral_indicator_one hCm] at hW
  have hB := hW.trans hlawΦ

  have hΦpt : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
      (∫⁻ y, C.indicator 1 ((y : AdelicGL2 (𝓞 F) F) * (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)))
          ∂(rationalTorusUnipotentHaar F)) =
        ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ,
          K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k := by
    intro z t k
    rw [lintegral_rationalTorusUnipotentHaar_comp_mul _ hH₀]
    refine congrArg (fun S => ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * S) (tsum_congr fun za => ?_)
    rw [hK]
    simp_rw [centralScalar_mul_diagOne_mul_unipotentGL2_mul]
    exact lintegral_comp_algebraMap_mul za.2 (fun x => C.indicator 1 (unipotentGL2 x *
        centralScalar (𝓞 F) F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z) *
        diagOne (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) *
        (k : AdelicGL2 (𝓞 F) F)))
      (hH₀.comp (((continuous_adeleRing_unipotentGL2.mul continuous_const).mul continuous_const).mul
        continuous_const).measurable)

  have pull : ∀ {α : Type} [MeasurableSpace α] (μ' : Measure α) (G : Fˣ × Fˣ → α → ℝ≥0∞),
      (∀ za, Measurable (G za)) →
      ∫⁻ a, ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ, G za a ∂μ' =
        ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ, ∫⁻ a, G za a ∂μ' := by
    intro α _ μ' G hG
    rw [lintegral_const_mul' _ _ hbi, lintegral_tsum fun za => (hG za).aemeasurable]
  have lvl1 : ∀ z t : (AdeleRing (𝓞 F) F)ˣ,
      (∫⁻ k, ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ,
          K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k *
          w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) ∂(maximalCompactHaar F)) =
        ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ, ∫⁻ k,
          K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k *
          w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) ∂(maximalCompactHaar F) :=
    fun z t => pull _ _ fun za => hm1 _ _
  have lvl2 : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      (∫⁻ t in D', ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ, ∫⁻ k,
          K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k *
          w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) ∂(maximalCompactHaar F)
          ∂(NumberField.Idele.idelicHaar F)) =
        ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ, ∫⁻ t in D', ∫⁻ k,
          K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k *
          w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) ∂(maximalCompactHaar F)
          ∂(NumberField.Idele.idelicHaar F) :=
    fun z => pull _ _ fun za => hm2 _ _
  have lvl3 :
      (∫⁻ z in D, ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ, ∫⁻ t in D', ∫⁻ k,
          K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k *
          w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) ∂(maximalCompactHaar F)
          ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)) =
        ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ, ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
          K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k *
          w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) ∂(maximalCompactHaar F)
          ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) :=
    pull _ _ fun za => hm3 _ _

  have hfoldD : ∀ Gf : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞,
      ∑' γ : Fˣ, ∫⁻ z in D, Gf (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ * z)
          ∂(NumberField.Idele.idelicHaar F) =
        ∫⁻ z, Gf z ∂(NumberField.Idele.idelicHaar F) := fun Gf => by
    rw [hDF.lintegral_eq_tsum'' Gf, ← (principalIdeleEquiv (F := F)).tsum_eq]
    exact tsum_congr fun γ => rfl
  have hfoldD' : ∀ Gf : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞,
      ∑' δ : Fˣ, ∫⁻ t in D', Gf (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t)
          ∂(NumberField.Idele.idelicHaar F) =
        ∫⁻ t, Gf t ∂(NumberField.Idele.idelicHaar F) := fun Gf => by
    rw [hD'F.lintegral_eq_tsum'' Gf, ← (principalIdeleEquiv (F := F)).tsum_eq]
    exact tsum_congr fun δ => rfl
  have hE2 :
      (∑' za : Fˣ × Fˣ, ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
          K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k *
          w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) ∂(maximalCompactHaar F)
          ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)) =
        ∫⁻ z, ∫⁻ t, ∫⁻ k, K z t k * w t ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(NumberField.Idele.idelicHaar F) :=
    calc (∑' za : Fˣ × Fˣ, ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
            K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
              (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k *
            w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) ∂(maximalCompactHaar F)
            ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
        = ∑' γ : Fˣ, ∑' δ : Fˣ, ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
            K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ * z)
              (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) k *
            w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) ∂(maximalCompactHaar F)
            ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := ENNReal.tsum_prod'
      _ = ∑' δ : Fˣ, ∑' γ : Fˣ, ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
            K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) γ * z)
              (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) k *
            w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) ∂(maximalCompactHaar F)
            ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) := ENNReal.tsum_comm
      _ = ∑' δ : Fˣ, ∫⁻ z, ∫⁻ t in D', ∫⁻ k,
            K z (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) k *
            w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) ∂(maximalCompactHaar F)
            ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) :=
          tsum_congr fun δ => hfoldD fun z => ∫⁻ t in D', ∫⁻ k,
            K z (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) k *
            w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) ∂(maximalCompactHaar F)
            ∂(NumberField.Idele.idelicHaar F)
      _ = ∫⁻ z, ∑' δ : Fˣ, ∫⁻ t in D', ∫⁻ k,
            K z (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) k *
            w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) δ * t) ∂(maximalCompactHaar F)
            ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F) :=
          (lintegral_tsum fun δ => (hm3' _).aemeasurable).symm
      _ = ∫⁻ z, ∫⁻ t, ∫⁻ k, K z t k * w t ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(NumberField.Idele.idelicHaar F) :=
          lintegral_congr fun z => hfoldD' fun t => ∫⁻ k, K z t k * w t ∂(maximalCompactHaar F)

  have hE3 :
      (∫⁻ z, ∫⁻ t, ∫⁻ k, K z t k * w t ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(NumberField.Idele.idelicHaar F)) =
        ∫⁻ x, ∫⁻ z, ∫⁻ t, ∫⁻ k, P z t k x ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F) := by
    have hx : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
        K z t k * w t = ∫⁻ x, P z t k x ∂(adelicAddHaar (𝓞 F) F) := fun z t k => by
      rw [hK]
      simp_rw [hP]
      exact (lintegral_mul_const (w t)
        (hM.comp ((measurable_const.prodMk (measurable_const.prodMk measurable_const)).prodMk
          measurable_id))).symm
    simp_rw [hx]
    have hS1 : ∀ z t : (AdeleRing (𝓞 F) F)ˣ,
        (∫⁻ k, ∫⁻ x, P z t k x ∂(adelicAddHaar (𝓞 F) F) ∂(maximalCompactHaar F)) =
          ∫⁻ x, ∫⁻ k, P z t k x ∂(maximalCompactHaar F) ∂(adelicAddHaar (𝓞 F) F) := fun z t => by
      apply lintegral_lintegral_swap
      exact (hPm.comp ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
        measurable_snd)).aemeasurable
    simp_rw [hS1]
    have hS2 : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
        (∫⁻ t, ∫⁻ x, ∫⁻ k, P z t k x ∂(maximalCompactHaar F) ∂(adelicAddHaar (𝓞 F) F)
            ∂(NumberField.Idele.idelicHaar F)) =
          ∫⁻ x, ∫⁻ t, ∫⁻ k, P z t k x ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F) := fun z => by
      apply lintegral_lintegral_swap
      refine (Measurable.lintegral_prod_right ?_).aemeasurable
      exact hPm.comp ((measurable_const.prodMk (measurable_fst.fst.prodMk measurable_snd)).prodMk
        measurable_fst.snd)
    simp_rw [hS2]
    apply lintegral_lintegral_swap
    refine (Measurable.lintegral_prod_right ?_).aemeasurable
    refine Measurable.lintegral_prod_right ?_
    exact hPm.comp ((measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)).prodMk
      measurable_fst.fst.snd)

  have hI :
      (∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
          (∫⁻ y, C.indicator 1
              ((y : AdelicGL2 (𝓞 F) F) * (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)))
              ∂(rationalTorusUnipotentHaar F)) *
            ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)) =
        ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∫⁻ x, ∫⁻ z, ∫⁻ t, ∫⁻ k, P z t k x
          ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
          ∂(adelicAddHaar (𝓞 F) F) := by
    have h1 : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F),
        (∫⁻ y, C.indicator 1
            ((y : AdelicGL2 (𝓞 F) F) * (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)))
            ∂(rationalTorusUnipotentHaar F)) *
          ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹) =
        ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∑' za : Fˣ × Fˣ,
          K (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.1 * z)
            (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) k *
          w (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) za.2 * t) := fun z t k => by
      rw [hΦpt, ← hw, mul_assoc, ← ENNReal.tsum_mul_right]
      congr 1
      exact tsum_congr fun za => by rw [hwδ]
    simp_rw [h1, lvl1, lvl2]
    rw [lvl3, hE2, hE3]
  have hfin : adelicGLHaar (Fin 2) (𝓞 F) F C =
      c' * (((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * ∫⁻ x, ∫⁻ z, ∫⁻ t, ∫⁻ k, P z t k x
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
        ∂(adelicAddHaar (𝓞 F) F)) := hB.trans (congrArg (fun I => c' * I) hI)
  simp only [hP, hw] at hfin
  have hfin' : adelicGLHaar (Fin 2) (𝓞 F) F C = c' * (((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ * J) := by
    rw [hJdef]
    exact hfin
  rw [← mul_assoc] at hfin'
  have hcq : c = c' * ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ :=
    (ENNReal.mul_left_inj hJ0 hJT).1 (hJ.symm.trans hfin')
  rw [hcq, mul_assoc, ENNReal.inv_mul_cancel hb0 hbT, mul_one]

end QuotientConstant

end AutomorphicForm.SlabCovolume

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

section TruncatedBracketResidue

variable (F : Type) [Field F] [NumberField F]

private theorem setIntegral_pseudoEisenstein_brT_eq_sub {Φ : Set (AdelicGL2 (𝓞 F) F)} (T : ℝ) {φ m : AdelicGL2 (𝓞 F) F
    → ℂ}
    (hφm : Measurable φ) (hmm : Measurable m) (hHm : Measurable (NumberField.AdelicHeight.adelicHeight F))
    (hA : ∫⁻ x in Φ, ∑' τ : Option F,
        ‖(fun x => (Set.Ioc 0 T).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * φ x)
        (bruhatRep (F := F) τ * x)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞)
    (hB : ∫⁻ x in Φ, ∑' τ : Option F,
        ‖(fun x => (Set.Ioi T).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * m x)
        (bruhatRep (F := F) τ * x)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞) :
    ∫ x in Φ, AutomorphicForm.pseudoEisenstein F (brT T φ m) x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = (∫ x in Φ, AutomorphicForm.pseudoEisenstein F (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioc 0 T).indicator (fun _ =>
          (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * φ x) x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) - ∫ x in Φ,
          AutomorphicForm.pseudoEisenstein F (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioi T).indicator (fun _ => (1 : ℂ))
          (NumberField.AdelicHeight.adelicHeight F x) * m x) x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : Countable F := countable_field (F := F)
  have hAm : Measurable (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioc 0 T).indicator (fun _ => (1 : ℂ))
      (NumberField.AdelicHeight.adelicHeight F x) * φ x) := ((measurable_const.indicator measurableSet_Ioc).comp
      hHm).mul hφm
  have hBm : Measurable (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioi T).indicator (fun _ => (1 : ℂ))
      (NumberField.AdelicHeight.adelicHeight F x) * m x) := ((measurable_const.indicator measurableSet_Ioi).comp
      hHm).mul hmm
  have hsA := ae_summable_of_lintegral_tsum_enorm_ne_top
    (u := fun (β : F) (x : AdelicGL2 (𝓞 F) F) => (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioc 0 T).indicator (fun _ => (1 :
        ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * φ x) (adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2
        (algebraMap F (AdeleRing (𝓞 F) F) β) * x))
    (fun β => hAm.comp (measurable_const_mul _))
    (ne_top_of_le_ne_top hA (lintegral_mono fun x => tsum_enorm_weyl_unipotent_mul_le F
      (φ := fun x : AdelicGL2 (𝓞 F) F => (Set.Ioc 0 T).indicator (fun _ => (1 : ℂ))
        (NumberField.AdelicHeight.adelicHeight F x) * φ x) x))
  have hsB := ae_summable_of_lintegral_tsum_enorm_ne_top
    (u := fun (β : F) (x : AdelicGL2 (𝓞 F) F) => (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioi T).indicator (fun _ => (1 :
        ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * m x) (adelicWeyl (𝓞 F) F * AutomorphicForm.unipotentGL2
        (algebraMap F (AdeleRing (𝓞 F) F) β) * x))
    (fun β => hBm.comp (measurable_const_mul _))
    (ne_top_of_le_ne_top hB (lintegral_mono fun x => tsum_enorm_weyl_unipotent_mul_le F
      (φ := fun x : AdelicGL2 (𝓞 F) F => (Set.Ioi T).indicator (fun _ => (1 : ℂ))
        (NumberField.AdelicHeight.adelicHeight F x) * m x) x))
  rw [← integral_sub (integrableOn_pseudoEisenstein_of_lintegral_tsum_bruhatRep_ne_top F hAm hA)
    (integrableOn_pseudoEisenstein_of_lintegral_tsum_bruhatRep_ne_top F hBm hB)]
  refine integral_congr_ae ?_
  filter_upwards [hsA, hsB] with x hxA hxB
  simp only [AutomorphicForm.pseudoEisenstein, brT]
  rw [hxA.tsum_sub hxB]
  ring

private theorem setIntegral_adaptedDomain_pseudoEisenstein_brT_eq_mul_cpow_div_sub :
    ∀ (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
      (cq : ℝ≥0∞) (_hcT : cq ≠ ∞)
      (_hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
          IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
        ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
          (∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
          ∫⁻ q, f q.out ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) =
            cq * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                  f (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞
                      F) F)) *
                    ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
                ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
      (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (V : ℝ≥0∞) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
      (_hHm : Measurable (NumberField.AdelicHeight.adelicHeight F))
      (_hHinv : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
          NumberField.AdelicHeight.adelicHeight F (x * g) = NumberField.AdelicHeight.adelicHeight F g)
      (_hH : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
        NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.centralScalar (𝓞 F) F z *
            NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F)) = NumberField.TateGlobal.ideleNorm F t)
      (_hN : ∀ (z t : (AdeleRing (𝓞 F) F)ˣ) (k : ↥(adelicMaximalCompact F)),
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (AutomorphicForm.centralScalar (𝓞 F) F z *
            NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
          NumberField.TateGlobal.ideleNorm F z ^ 2 * NumberField.TateGlobal.ideleNorm F t)
      (_hhB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
          NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g) =
          NumberField.AdelicHeight.adelicHeight F g)
      (_hhN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
          NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.unipotentGL2 u * g) =
          NumberField.AdelicHeight.adelicHeight F g)
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (_hS : MeasurableSet {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det
          g) ∈ Set.Icc d₁ d₂})
      (_hSΓ : ∀ γ ∈ (AutomorphicForm.globalPoints (𝓞 F) F).range, ∀ g : AdelicGL2 (𝓞 F) F,
          γ * g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
          Set.Icc d₁ d₂} ↔ g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_hSH : ∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
          x * g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
          Set.Icc d₁ d₂} ↔ g ∈ {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (T : ℝ) (_hT : 1 ≤ T) (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (_hΦ₀m : MeasurableSet Φ₀) (_hΦ₀s : Φ₀ ⊆ {g : AdelicGL2 (𝓞
          F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F)
          F).restrict {g : AdelicGL2 (𝓞 F) F | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
          Set.Icc d₁ d₂}))
      (s : ℂ) (_hs : 1 / 2 < s.re)
      (_hΦ₁fin : adelicGLHaar (Fin 2) (𝓞 F) F (adaptedDomain F T Φ₀) < ⊤)
      (φ : AdelicGL2 (𝓞 F) F →
          ℂ) (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 (modChar F) hα s) (etaSnd 1 (modChar F) hα s) φ) (_hφc :
          Continuous φ)
      (_hφB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
          φ (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = φ g)
      (_hφN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), φ (AutomorphicForm.unipotentGL2 u * g) = φ g)
      (Cφ : ℝ) (_hφbd : ∀ g : AdelicGL2 (𝓞 F) F,
          ‖φ g‖ ≤ Cφ * NumberField.AdelicHeight.adelicHeight F g ^ (s.re + 1 / 2))
      (m : AdelicGL2 (𝓞 F) F →
          ℂ) (_hm : IsInducedSection (𝓞 F) F (etaFst 1 (modChar F) hα (-s)) (etaSnd 1 (modChar F) hα (-s)) m) (_hmc :
          Continuous m)
      (_hmB : ∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
          m (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = m g)
      (_hmN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), m (AutomorphicForm.unipotentGL2 u * g) = m g)
      (Cm : ℝ) (_hmbd : ∀ g : AdelicGL2 (𝓞 F) F,
          ‖m g‖ ≤ Cm * NumberField.AdelicHeight.adelicHeight F g ^ ((-s).re + 1 / 2)),
    ∫ x in adaptedDomain F T Φ₀, AutomorphicForm.pseudoEisenstein F (brT T φ m) x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = (cq.toReal : ℂ) * (∫ k,
          φ (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ /
          d₁) / 2 : ℝ) : ℂ) * (((T : ℝ) : ℂ) ^ (s - 1 / 2) / (s - 1 / 2))
        - (cq.toReal : ℂ) * (∫ k,
            m (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ /
            d₁) / 2 : ℝ) : ℂ) * (((T : ℝ) : ℂ) ^ (-s - 1 / 2) / (s + 1 / 2)) := by
  intro hα cq hcT hc D hDm hDF V hVT hV hHm hHinv hH hN hhB hhN d₁ d₂ hd₁ hd hS hSΓ hSH T hT Φ₀ hΦ₀m hΦ₀s hΦ₀ s hs
      hΦ₁fin
    φ hφ hφc hφB hφN Cφ hφbd m hm hmc hmB hmN Cm hmbd
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le one_pos hT
  have heφ : (1 : ℝ) < s.re + 1 / 2 := by linarith
  have hem : (-s).re + 1 / 2 < (1 : ℝ) := by rw [Complex.neg_re]; linarith
  have hem0 : (-s).re + 1 / 2 ≤ (0 : ℝ) := by rw [Complex.neg_re]; linarith
  have hsneg : (-s).re < 1 / 2 := by rw [Complex.neg_re]; linarith
  have hs1 : s ≠ (1 / 2 : ℂ) := by
    rintro rfl
    norm_num at hs
  have hs2 : -s ≠ (1 / 2 : ℂ) := by
    intro h
    have h' : s = -(1 / 2 : ℂ) := by rw [← h, neg_neg]
    rw [h'] at hs
    norm_num at hs
  have hΦm := measurableSet_adaptedDomain (F := F) (T := T) hΦ₀m
  have hΦS := adaptedDomain_subset (F := F) (T := T) hΦ₀s
  have hΦ := isFundamentalDomain_adaptedDomain (F := F) hT hΦ₀m hΦ₀

  have hMφ : ∀ W : Set ℝ, MeasurableSet W → ∫⁻ x in adaptedDomain F T Φ₀, ∑' τ : Option F,
      W.indicator 1 (NumberField.AdelicHeight.adelicHeight F (bruhatRep (F := F) τ * x)) * ‖φ (bruhatRep (F := F) τ *
          x)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤ _ := fun W hW =>
    lintegral_tsum_indicator_mul_enorm_le F cq hc D hDm hDF V hV hHm hHinv hH hN hhB hhN hd₁ hd.le hS hSΓ hSH hΦm hΦS
        hΦ hφc.measurable hφB hφN hφbd W hW
  have hMm : ∀ W : Set ℝ, MeasurableSet W → ∫⁻ x in adaptedDomain F T Φ₀, ∑' τ : Option F,
      W.indicator 1 (NumberField.AdelicHeight.adelicHeight F (bruhatRep (F := F) τ * x)) * ‖m (bruhatRep (F := F) τ *
          x)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤ _ := fun W hW =>
    lintegral_tsum_indicator_mul_enorm_le F cq hc D hDm hDF V hV hHm hHinv hH hN hhB hhN hd₁ hd.le hS hSΓ hSH hΦm hΦS
        hΦ hmc.measurable hmB hmN hmbd W hW
  have hAm' : Measurable (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioc 0 T).indicator (fun _ => (1 : ℂ))
      (NumberField.AdelicHeight.adelicHeight F x) * φ x) := ((measurable_const.indicator measurableSet_Ioc).comp
      hHm).mul hφc.measurable
  have hBm' : Measurable (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioi T).indicator (fun _ => (1 : ℂ))
      (NumberField.AdelicHeight.adelicHeight F x) * m x) := ((measurable_const.indicator measurableSet_Ioi).comp
      hHm).mul hmc.measurable
  have hA : ∫⁻ x in adaptedDomain F T Φ₀, ∑' τ : Option F,
      ‖(fun x => (Set.Ioc 0 T).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * φ x)
      (bruhatRep (F := F) τ * x)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top (ofReal_mul_shell_Ioc_ne_top hcT hVT _ hT0 heφ) (hMφ _ measurableSet_Ioc))
      (lintegral_tsum_enorm_le_of_forall F (enorm_indicator_Ioc_mul_le F T φ))
  have hB : ∫⁻ x in adaptedDomain F T Φ₀, ∑' τ : Option F,
      ‖(fun x => (Set.Ioi T).indicator (fun _ => (1 : ℂ)) (NumberField.AdelicHeight.adelicHeight F x) * m x)
      (bruhatRep (F := F) τ * x)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≠ ∞ :=
    ne_top_of_le_ne_top (ne_top_of_le_ne_top (ofReal_mul_shell_Ioi_ne_top hcT hVT _ hT0 hem) (hMm _ measurableSet_Ioi))
      (lintegral_tsum_enorm_le_of_forall F (enorm_indicator_Ioi_mul_le F T m))
  rw [setIntegral_pseudoEisenstein_brT_eq_sub F T hφc.measurable hmc.measurable hHm hA hB]

  have hmin : Filter.Tendsto (fun R : ℝ => min R (Real.log T)) Filter.atBot Filter.atBot :=
    Filter.tendsto_atBot_mono (fun R => min_le_left R (Real.log T)) Filter.tendsto_id
  have hmax : Filter.Tendsto (fun R : ℝ => max R (Real.log T)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun R => le_max_left R (Real.log T)) Filter.tendsto_id

  have hlow : ∫ x in adaptedDomain F T Φ₀,
      AutomorphicForm.pseudoEisenstein F (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioc 0 T).indicator (fun _ => (1 : ℂ))
      (NumberField.AdelicHeight.adelicHeight F x) * φ x) x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = (cq.toReal : ℂ) * (∫ k,
          φ (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ /
          d₁) / 2 : ℝ) : ℂ) * (((T : ℝ) : ℂ) ^ (s - 1 / 2) / (s - 1 / 2)) := by
    have hband : ∀ R : ℝ, ∫ x in adaptedDomain F T Φ₀,
        AutomorphicForm.pseudoEisenstein F (heightBand F (Real.exp (min R (Real.log T))) T φ) x ∂(adelicGLHaar (Fin 2)
        (𝓞 F) F)
        = (cq.toReal : ℂ) * (∫ k,
            φ (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ /
            d₁) / 2 : ℝ) : ℂ) * (((T : ℝ) : ℂ) ^ (s - 1 / 2) - ((Real.exp (min R (Real.log T)) : ℝ) : ℂ) ^ (s - 1 /
            2)) /
          (s - 1 / 2) := by
      intro R
      have hC : ∀ x : AdelicGL2 (𝓞 F) F,
          NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc (Real.exp (min R (Real.log T))) (Real.exp (Real.log T)) →
          ‖φ x‖ ≤ max Cφ 0 * T ^ (s.re + 1 / 2) := by
        intro x hx
        rw [Real.exp_log hT0] at hx
        exact (hφbd x).trans (mul_le_mul (le_max_left _ _)
          (Real.rpow_le_rpow (NumberField.AdelicHeight.adelicHeight_pos x).le hx.2 (by linarith))
          (Real.rpow_nonneg (NumberField.AdelicHeight.adelicHeight_pos x).le _) (le_max_right _ _))
      have h := (setIntegral_pseudoEisenstein_heightBand_eq_integral_indicator_slab_mul_indicator_band_mul (F := F) hα
          d₁ d₂
          hd₁ hd (adaptedDomain F T Φ₀) hΦS hΦ hΦ₁fin s φ hφ hφc (min R (Real.log T)) (Real.log T) _ hC).trans
        (integral_indicator_slab_mul_indicator_shell_mul_section_eq_mul_log_mul_cpow_sub_div (F := F) hα cq hcT hc D
            hDm hDF
          V hV s hs1 φ hφ hφc d₁ d₂ (min R (Real.log T)) (Real.log T) hd₁ hd.le (min_le_right _ _))
      rw [Real.exp_log hT0] at h
      exact h
    have hlim := tendsto_exp_cpow_sub_exp_cpow_div_atBot_of_half_lt_re (Real.log T) hs
    rw [Real.exp_log hT0] at hlim
    refine setIntegral_pseudoEisenstein_eq_of_tendsto F (l := Filter.atBot) hAm' hA ?_ ?_ ?_
      (tendsto_ofReal_mul_shell_Ioc_exp hcT hVT (max Cφ 0) (d₁ := d₁) (d₂ := d₂) heφ hmin) hband ?_
    · intro R
      exact hφc.measurable.indicator (hHm measurableSet_Ioc)
    · intro R
      exact ne_top_of_le_ne_top (ne_top_of_le_ne_top (ofReal_mul_shell_Ioc_ne_top hcT hVT _ hT0 heφ) (hMφ _
          measurableSet_Ioc))
        (lintegral_tsum_enorm_le_of_forall F (enorm_heightBand_low_le F (Real.exp_pos _) T φ))
    · intro R
      exact (lintegral_tsum_enorm_le_of_forall F
        (enorm_indicator_Ioc_mul_sub_heightBand_le F (Real.exp_pos (min R (Real.log T))) T φ)).trans (hMφ _
            measurableSet_Ioc)
    · exact Filter.Tendsto.congr (fun R => by simp only [Function.comp_apply, mul_div_assoc])
        (Filter.Tendsto.const_mul ((cq.toReal : ℂ) * (∫ k,
            φ (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ /
            d₁) / 2 : ℝ) : ℂ)) (hlim.comp hmin))

  have hhigh : ∫ x in adaptedDomain F T Φ₀,
      AutomorphicForm.pseudoEisenstein F (fun x : AdelicGL2 (𝓞 F) F => (Set.Ioi T).indicator (fun _ => (1 : ℂ))
      (NumberField.AdelicHeight.adelicHeight F x) * m x) x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = (cq.toReal : ℂ) * (∫ k,
          m (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ /
          d₁) / 2 : ℝ) : ℂ) * (((T : ℝ) : ℂ) ^ (-s - 1 / 2) / (s + 1 / 2)) := by
    have hband : ∀ R : ℝ, ∫ x in adaptedDomain F T Φ₀,
        AutomorphicForm.pseudoEisenstein F (heightBand F T (Real.exp (max R (Real.log T))) m) x ∂(adelicGLHaar (Fin 2)
        (𝓞 F) F)
        = (cq.toReal : ℂ) * (∫ k,
            m (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ /
            d₁) / 2 : ℝ) : ℂ) * (((Real.exp (max R (Real.log T)) : ℝ) : ℂ) ^ (-s - 1 / 2) - ((T : ℝ) : ℂ) ^ (-s - 1 /
            2)) /
          (-s - 1 / 2) := by
      intro R
      have hC : ∀ x : AdelicGL2 (𝓞 F) F,
          NumberField.AdelicHeight.adelicHeight F x ∈ Set.Ioc (Real.exp (Real.log T)) (Real.exp (max R (Real.log T))) →
          ‖m x‖ ≤ max Cm 0 * T ^ ((-s).re + 1 / 2) := by
        intro x hx
        rw [Real.exp_log hT0] at hx
        exact (hmbd x).trans (mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_nonpos hT0 hx.1.le hem0)
          (Real.rpow_nonneg (NumberField.AdelicHeight.adelicHeight_pos x).le _) (le_max_right _ _))
      have h := (setIntegral_pseudoEisenstein_heightBand_eq_integral_indicator_slab_mul_indicator_band_mul (F := F) hα
          d₁ d₂
          hd₁ hd (adaptedDomain F T Φ₀) hΦS hΦ hΦ₁fin (-s) m hm hmc (Real.log T) (max R (Real.log T)) _ hC).trans
        (integral_indicator_slab_mul_indicator_shell_mul_section_eq_mul_log_mul_cpow_sub_div (F := F) hα cq hcT hc D
            hDm hDF
          V hV (-s) hs2 m hm hmc d₁ d₂ (Real.log T) (max R (Real.log T)) hd₁ hd.le (le_max_right _ _))
      rw [Real.exp_log hT0] at h
      exact h
    have hlim := tendsto_exp_cpow_sub_exp_cpow_div_atTop_of_re_lt_half (Real.log T) hsneg
    rw [Real.exp_log hT0] at hlim
    have hq : ∀ x : ℂ, -x / (-s - 1 / 2) = x / (s + 1 / 2) := fun x => by
      rw [show (-s - 1 / 2 : ℂ) = -(s + 1 / 2) by ring, neg_div_neg_eq]
    rw [← hq]
    refine setIntegral_pseudoEisenstein_eq_of_tendsto F (l := Filter.atTop) hBm' hB ?_ ?_ ?_
      (tendsto_ofReal_mul_shell_Ioi_exp hcT hVT (max Cm 0) (d₁ := d₁) (d₂ := d₂) hem hmax) hband ?_
    · intro R
      exact hmc.measurable.indicator (hHm measurableSet_Ioc)
    · intro R
      exact ne_top_of_le_ne_top (ne_top_of_le_ne_top (ofReal_mul_shell_Ioi_ne_top hcT hVT _ hT0 hem) (hMm _
          measurableSet_Ioi))
        (lintegral_tsum_enorm_le_of_forall F (enorm_heightBand_high_le F T (Real.exp (max R (Real.log T))) m))
    · intro R
      exact (lintegral_tsum_enorm_le_of_forall F
        (enorm_indicator_Ioi_mul_sub_heightBand_le F T (Real.exp (max R (Real.log T))) m)).trans (hMm _
            measurableSet_Ioi)
    · exact Filter.Tendsto.congr (fun R => by simp only [Function.comp_apply, mul_div_assoc])
        (Filter.Tendsto.const_mul ((cq.toReal : ℂ) * (∫ k,
            m (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) * ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ /
            d₁) / 2 : ℝ) : ℂ)) (hlim.comp hmax))
  rw [hlow, hhigh]

end TruncatedBracketResidue

end AutomorphicForm.SlabCovolume

set_option autoImplicit false

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsInducedSection chiDet_mul isInducedSection_unipotent_mul isInducedSection_centralScalar_mul borelSubgroup mem_borelSubgroup_iff borelDiagFst borelDiagSnd unipotentGL2_mem_borelSubgroup borelDiagFst_unipotentGL2 borelDiagSnd_unipotentGL2 adelicBorel globalPoints_apply globalPoints_mem_adelicBorel borelDiagFst_globalPoints borelDiagSnd_globalPoints centralScalar_mem_adelicBorel borelDiagFst_centralScalar borelDiagSnd_centralScalar AdelicGL2 globalPoints centralScalar IsIdeleClassChar IsUnitaryChar chiDet unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add constantTermIntegrand constantTerm constantTerm_const cpowChar_apply_val IsPrincipalTrivial etaFst etaSnd etaFst_apply etaSnd_apply etaFst_isIdeleClassChar etaSnd_isIdeleClassChar etaFst_mul_etaSnd gl2Weyl gl2Weyl_inv adelicWeyl weylIntertwiningIntegral finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff isKfSmooth_zero isAutomorphicFnAt_one_trivial CarrierPins productionPinsOf RightTranslatesSpanFinite archRowIsometrySubgroup IsArchKFinite adelicMaximalCompact mem_adelicMaximalCompact_iff glFin_mem_finiteIntegralGL2 isRowIsometry_archComponent isCompact_adelicMaximalCompact maximalCompactHaar ideleNorm_det_globalPoints isInducedSection_adelicHeight_cpow SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre IsSlabProfile pseudoEisenstein pseudoEisenstein_apply constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral rationalTorus rationalTorusUnipotent RationalTorusUnipotentQuotient rationalTorusUnipotentHaar rationalTorusUnipotentQuotientMeasure adelicUnipotent toAdelicUnipotent unipotentHaar fnTwist fnTwist_apply fnTwist_zero det_centralScalar chiDet_globalPoints_mul isKfSmooth_fnTwist isIdeleClassChar_one exists_mem_adelicBorel_mul_eq isFundamentalDomain_boxSheet_rationalTorusUnipotent isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent setIntegral_pseudoEisenstein_mul_conj_eq_setIntegral_rationalTorusUnipotentQuotient_slab integral_rationalTorusUnipotentQuotient_section_mul_conj_eq_mul_setIntegral_iwasawa exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection"
namespace SlabCovolume
p2m_open "AutomorphicForm"

p2m_open "MeasureTheory NumberField NumberField.AdelicHeight~adelicHeight_diagOne_mul NumberField.AdelicLevel NumberField.TateGlobal~measurableSet_setOf_ideleNorm_det_mem_Icc"
open NumberField.AdelicBox
open scoped NNReal ENNReal Topology

section TruncatedIntegralUntwisted

variable {F : Type} [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private def heightStabilizer : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {x | ∀ g, adelicHeight F (x * g) = adelicHeight F g}
  mul_mem' := by
    intro x y hx hy g
    rw [mul_assoc, hx (y * g), hy g]
  one_mem' := by
    intro g
    rw [one_mul]
  inv_mem' := by
    intro x hx g
    rw [← hx (x⁻¹ * g), mul_inv_cancel_left]

private theorem rationalTorusUnipotent_le_heightStabilizer (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ)) :
    rationalTorusUnipotent F ≤ heightStabilizer := by
  refine sup_le (rationalTorus_le_map_borelSubgroup.trans ?_) ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    show ∀ g : AdelicGL2 (𝓞 F) F, adelicHeight F (globalPoints (𝓞 F) F γ * g) = adelicHeight F g
    exact fun g => adelicHeight_globalPoints_mul_of_mem_borelSubgroup hγ g
  · rintro _ ⟨x, rfl⟩
    show ∀ g : AdelicGL2 (𝓞 F) F, adelicHeight F (unipotentGL2 x.toAdd * g) = adelicHeight F g
    exact fun g => adelicHeight_unipotentGL2_mul hα x.toAdd g

private theorem adelicHeight_centralScalar_mul_diagOne_mul (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (z t : (AdeleRing (𝓞 F) F)ˣ) (k : adelicMaximalCompact F) :
    adelicHeight F (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F)) = ideleNorm F t := by
  rw [mul_assoc, adelicHeight_centralScalar_mul hα, adelicHeight_diagOne_mul hα,
    adelicHeight_eq_one_of_mem_adelicMaximalCompact k.2, mul_one, val_modChar_eq_ideleNorm]

private theorem ideleNorm_det_centralScalar_mul_diagOne_mul (z t : (AdeleRing (𝓞 F) F)ˣ)
    (k : adelicMaximalCompact F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z * diagOne t * (k : AdelicGL2 (𝓞 F) F))) =
      ideleNorm F z ^ 2 * ideleNorm F t := by
  rw [map_mul, map_mul, ideleNorm_mul, ideleNorm_mul, det_centralScalar, ideleNorm_pow_eq_pow, det_diagOne_eq,
    ideleNorm_det_eq_one_of_mem_adelicMaximalCompact k.2, mul_one]

private theorem globalPoints_mul_mem_setOf_ideleNorm_det_iff (γ : (globalPoints (𝓞 F) F).range) (d₁ d₂ : ℝ)
    (g : AdelicGL2 (𝓞 F) F) :
    (γ : AdelicGL2 (𝓞 F) F) * g ∈ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} ↔
      g ∈ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} := by
  simp only [Set.mem_setOf_eq, ideleNorm_det_globalPoints_mul]

private theorem isInducedSection_inv_mul_weylIntertwiningIntegral (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 (modChar F) hα s) (etaSnd 1 (modChar F) hα s) (ψ s))
    (hψK : ∀ s, IsArchKFinite F (ψ s)) (hψsm : ∀ s, IsKfSmooth F (ψ s))
    (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2)) (hψhol : ∀ g, Differentiable ℂ (fun s => ψ s g))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IsInducedSection (𝓞 F) F (etaFst 1 (modChar F) hα (-s)) (etaSnd 1 (modChar F) hα (-s))
        (fun g => (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (ψ s) g) ∧
      Continuous (fun g => (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
        weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (ψ s) g) := by
  have hrow :=
    exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_isInducedSection_of_isArchKFinite_family F hα ψ
      hψ hψK hψsm hψjc hψhol
  obtain ⟨a, Mreg, ha, -, hMreg, hMc, hMsec⟩ := hrow
  have has : a < s.re := ha.trans hs
  have hs0 : s - 1 / 2 ≠ 0 := sub_ne_zero.mpr fun h => by
    rw [h] at hs
    norm_num at hs
  refine ⟨?_, ?_⟩
  · intro b' hb' g'
    beta_reduce
    have hb := hMsec s has b' hb' g'
    rw [hMreg s (b' * g') hs, hMreg s g' hs] at hb
    apply mul_left_cancel₀ hs0
    linear_combination hb
  · have hc : Continuous fun g : AdelicGL2 (𝓞 F) F => Mreg s g :=
      hMc.comp_continuous (continuous_const.prodMk continuous_id) fun g => ⟨has, Set.mem_univ _⟩
    refine (hc.const_mul (s - 1 / 2)⁻¹).congr fun g => ?_
    rw [hMreg s g hs, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

private theorem integrableOn_and_setIntegral_pseudoEisenstein_brT_one (hα : ∀ x, 0 < ((modChar F x : ℝˣ) : ℝ))
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd : d₁ < d₂) {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀m : MeasurableSet Φ₀)
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    {cq : ℝ≥0∞} (hcT : cq ≠ ∞)
    (hc : ∀ (D D' : Set (AdeleRing (𝓞 F) F)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D' (NumberField.Idele.idelicHaar F) →
      ∀ f : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable f →
        (∀ x ∈ AutomorphicForm.rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(AutomorphicForm.rationalTorusUnipotentQuotientMeasure F) =
          cq * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (AutomorphicForm.centralScalar (𝓞 F) F z * NumberField.AdelicLevel.diagOne t * (k : AdelicGL2 (𝓞 F)
                    F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F))
    {D : Set (AdeleRing (𝓞 F) F)ˣ} (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    {V : ℝ≥0∞} (hVT : V ≠ ∞)
    (hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ z in D, f (ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
        V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
    (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 F) F μ)
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ (modChar F) hα s) (etaSnd μ (modChar F) hα s) (ψf s))
    (hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
    (hψhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
    (hψK : ∀ s, IsArchKFinite F (ψf s)) (hψsm : ∀ s, IsKfSmooth F (ψf s))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    IntegrableOn (pseudoEisenstein F (brT 1 (fnTwist F μ⁻¹ (ψf s)) (fun g =>
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g)))
      (adaptedDomain F 1 Φ₀) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    ∫ x in adaptedDomain F 1 Φ₀, pseudoEisenstein F (brT 1 (fnTwist F μ⁻¹ (ψf s)) (fun g =>
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g))
        x ∂adelicGLHaar (Fin 2) (𝓞 F) F =
      (cq.toReal : ℂ) * (∫ k, fnTwist F μ⁻¹ (ψf s) (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) *
          ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ / d₁) / 2 : ℝ) : ℂ) *
          (((1 : ℝ) : ℂ) ^ (s - 1 / 2) / (s - 1 / 2)) -
        (cq.toReal : ℂ) * (∫ k, (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s))
              (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) *
          ((V.toReal : ℂ) * (V.toReal : ℂ)) * ((Real.log (d₂ / d₁) / 2 : ℝ) : ℂ) *
          (((1 : ℝ) : ℂ) ^ (-s - 1 / 2) / (s + 1 / 2)) := by
  have hsec0 : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 (modChar F) hα s) (etaSnd 1 (modChar F) hα s)
      (fnTwist F μ⁻¹ (ψf s)) := fun s => isInducedSection_fnTwist_inv (modChar F) hα μ s (hψf s)
  have hK0 : ∀ s, IsArchKFinite F (fnTwist F μ⁻¹ (ψf s)) := fun s => isArchKFinite_fnTwist μ⁻¹ (hψK s)
  have hsm0 : ∀ s, IsKfSmooth F (fnTwist F μ⁻¹ (ψf s)) :=
    isKfSmooth_fnTwist_inv_of_family (modChar F) hα hμ hψf hψhol hψsm
  have hjc0 : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => fnTwist F μ⁻¹ (ψf p.1) p.2) :=
    continuous_uncurry_fnTwist_inv μ hμc hψjc
  have hhol0 : ∀ x : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s => fnTwist F μ⁻¹ (ψf s) x) :=
    differentiable_fnTwist_inv μ hψhol
  have hc0 : ∀ s : ℂ, Continuous (fnTwist F μ⁻¹ (ψf s)) := fun s =>
    Continuous.uncurry_left (f := fun s => fnTwist F μ⁻¹ (ψf s)) s hjc0
  have hm := isInducedSection_inv_mul_weylIntertwiningIntegral hα (fun s => fnTwist F μ⁻¹ (ψf s)) hsec0 hK0
    hsm0 hjc0 hhol0 hs
  obtain ⟨hsecM, hmc⟩ := hm
  beta_reduce at hsecM hmc
  have h1u : IsUnitaryChar (𝓞 F) F 1 := fun x => by simp
  have hbφ := exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection F hα 1 1 h1u h1u s
    (fnTwist F μ⁻¹ (ψf s)) (hsec0 s) (hc0 s)
  obtain ⟨Cφ, hCφ⟩ := hbφ
  have hbm := exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection F hα 1 1 h1u h1u (-s)
    (fun g => (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
      weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g)
    hsecM hmc
  obtain ⟨Cm, hCm⟩ := hbm
  have hfin0 : adelicGLHaar (Fin 2) (𝓞 F) F Φ₀ < ⊤ := by
    have h := adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain F d₁ d₂ hd₁ hd Φ₀ hΦ₀
    rwa [Set.inter_eq_left.mpr hΦ₀s] at h
  have h1 : (1 : ℝ) ≤ 1 := le_rfl
  have hΦ₁fin : adelicGLHaar (Fin 2) (𝓞 F) F (adaptedDomain F 1 Φ₀) < ⊤ := by
    rw [measure_adaptedDomain_eq h1 hΦ₀m hΦ₀s hΦ₀]
    exact hfin0
  have hHm : Measurable (adelicHeight F) := (continuous_adelicHeight F).measurable
  have hHinv : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      adelicHeight F (x * g) = adelicHeight F g :=
    fun x hx g => rationalTorusUnipotent_le_heightStabilizer hα hx g
  have hSΓ : ∀ γ ∈ (globalPoints (𝓞 F) F).range, ∀ g : AdelicGL2 (𝓞 F) F,
      γ * g ∈ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} ↔
        g ∈ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} :=
    fun γ hγ g => globalPoints_mul_mem_setOf_ideleNorm_det_iff ⟨γ, hγ⟩ d₁ d₂ g
  have hSH : ∀ x ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F,
      x * g ∈ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} ↔
        g ∈ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} :=
    fun x hx g => rationalTorusUnipotent_le_leftStabilizer_detSlab d₁ d₂ hx g
  have hφB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      fnTwist F μ⁻¹ (ψf s) (globalPoints (𝓞 F) F γ * g) = fnTwist F μ⁻¹ (ψf s) g :=
    fun γ hγ g => globalPoints_mul_eq_of_isInducedSection_etaFst_etaSnd_one F (modChar F) hα
      (isPrincipalTrivial_distribHaarChar_adeleRing F) s (hsec0 s) hγ g
  have hmB : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s))
            (globalPoints (𝓞 F) F γ * g) =
        (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g :=
    fun γ hγ g => globalPoints_mul_eq_of_isInducedSection_etaFst_etaSnd_one F (modChar F) hα
      (isPrincipalTrivial_distribHaarChar_adeleRing F) (-s) hsecM hγ g
  refine ⟨integrableOn_pseudoEisenstein_brT_adaptedDomain F cq hcT hc D hDm hDF V hVT hV hHm hHinv
    (adelicHeight_centralScalar_mul_diagOne_mul hα) ideleNorm_det_centralScalar_mul_diagOne_mul
    (fun γ hγ g => adelicHeight_globalPoints_mul_of_mem_borelSubgroup hγ g) (adelicHeight_unipotentGL2_mul hα)
    d₁ d₂ hd₁ hd (measurableSet_setOf_ideleNorm_det_mem_Icc d₁ d₂) hSΓ hSH 1 h1 Φ₀ hΦ₀m hΦ₀s hΦ₀ s hs
    (fnTwist F μ⁻¹ (ψf s)) (hc0 s) hφB (fun u g => isInducedSection_unipotent_mul (hsec0 s) u g) Cφ hCφ
    (fun g => (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
      weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g) hmc hmB
    (fun u g => isInducedSection_unipotent_mul hsecM u g) Cm hCm, ?_⟩
  have h := setIntegral_adaptedDomain_pseudoEisenstein_brT_eq_mul_cpow_div_sub F hα cq hcT hc D hDm hDF V hVT hV
    hHm hHinv (adelicHeight_centralScalar_mul_diagOne_mul hα) ideleNorm_det_centralScalar_mul_diagOne_mul
    (fun γ hγ g => adelicHeight_globalPoints_mul_of_mem_borelSubgroup hγ g) (adelicHeight_unipotentGL2_mul hα)
    d₁ d₂ hd₁ hd (measurableSet_setOf_ideleNorm_det_mem_Icc d₁ d₂) hSΓ hSH 1 h1 Φ₀ hΦ₀m hΦ₀s hΦ₀ s hs hΦ₁fin
    (fnTwist F μ⁻¹ (ψf s)) (hsec0 s) (hc0 s) hφB (fun u g => isInducedSection_unipotent_mul (hsec0 s) u g) Cφ
    hCφ (fun g => (((NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
      weylIntertwiningIntegral (𝓞 F) F (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (fnTwist F μ⁻¹ (ψf s)) g)
    hsecM hmc hmB
    (fun u g => isInducedSection_unipotent_mul hsecM u g) Cm hCm
  beta_reduce at h
  exact h

end TruncatedIntegralUntwisted

end AutomorphicForm.SlabCovolume

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_residue_weylIntertwining_continuation_self_dual_eq_div_measure_slab_mul_maximalCompact_pairing_mul_det.AutomorphicForm"
open scoped NNReal ENNReal Topology
open AutomorphicForm.SlabCovolume

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
            (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (c : ℝ≥0∞) (_hc0 : c ≠ 0) (_hcT : c ≠ ∞)
      (_hc : ∀ H : AdelicGL2 (𝓞 F) F → ℝ≥0∞, Measurable H →
        ∫⁻ g, H g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t, ∫⁻ k,
                H (unipotentGL2 x * centralScalar (𝓞 F) F u * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹)
              ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(NumberField.Idele.idelicHaar F)
            ∂(adelicAddHaar (𝓞 F) F))
      (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (V : ℝ≥0∞) (_hV0 : V ≠ 0) (_hVT : V ≠ ∞)
      (_hV : ∀ f : ℝ → ℝ≥0∞, Measurable f →
        ∫⁻ z in D, f (NumberField.TateGlobal.ideleNorm F z) ∂(NumberField.Idele.idelicHaar F) =
          V * ∫⁻ y in Set.Ioi (0 : ℝ), f y * ENNReal.ofReal y⁻¹)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hself : μ = ν)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψf s))
      (_hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψK : ∀ s, IsArchKFinite F (ψf s)) (_hψsm : ∀ s, IsKfSmooth F (ψf s))
      (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ g : AdelicGL2 (𝓞 F) F, MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g),
    ∀ g : AdelicGL2 (𝓞 F) F,
      (((adelicGLHaar (Fin 2) (𝓞 F) F) Φ).toReal : ℂ) *
          Filter.limUnder (𝓝[≠] (1 / 2 : ℂ)) (fun s : ℂ => (s - (1 / 2 : ℂ)) * Mc s g) =
        ((c.toReal * ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal ^ 2 * V.toReal ^ 2
            * Real.log (d₂ / d₁) / 2 : ℝ) : ℂ) *
        (∫ k, ψf (1 / 2 : ℂ) (k : AdelicGL2 (𝓞 F) F)
            * starRingEnd ℂ ((μ (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 F) F)) : ℂˣ) : ℂ)
          ∂(maximalCompactHaar F)) *
        ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  intro α hα d₁ d₂ hd₁ hd Φ hΦs hΦ c hc0 hcT hc D hDm hDF V _hV0 hVT hV μ ν hμ _hν hμic _hνic hμc _hνc hself ψf hψf
    hψjc hψhol hψK hψsm Mc hMc g
  subst hself
  obtain ⟨c₀, u, e₁, e₂, tset, Φ₀, hc₀, -, hΦ₀m, hΦ₀s, hΦ₀, hcov⟩ :=
    exists_isFundamentalDomain_slab_subset_iUnion_centreCutSiegelSet (F := F) hd₁ hd
  have hc2 := lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_measure_adelicBox_mul c hc0 hcT hc
  have hcqT : c * adelicAddHaar (𝓞 F) F (adelicBox F) ≠ ∞ :=
    ENNReal.mul_ne_top hcT (adelicAddHaar_adelicBox_lt_top F).ne
  have hX := fun (s : ℂ) (hs : 1 / 2 < s.re) =>
    integrableOn_and_setIntegral_pseudoEisenstein_brT_one hα hd₁ hd hΦ₀m hΦ₀s hΦ₀ hcqT hc2 hDm hDF hVT hV μ hμ
      hμc ψf hψf hψjc hψhol hψK hψsm hs
  rw [integral_mul_conj_char_det_eq_integral_fnTwist_inv μ hμ (ψf (1 / 2 : ℂ))]
  exact toReal_measure_mul_limUnder_eq_of_truncated_identity hα hd₁ hd hΦs hΦ hc₀ hΦ₀m hΦ₀s hΦ₀ hcov rfl
    (fun f hf hfH => hc2 D D hDm hDm hDF hDF f hf hfH) hV μ hμ hμic hμc ψf hψf hψjc hψhol hψK hψsm Mc hMc
    (fun s => ((1 : ℝ) : ℂ) ^ (s - 1 / 2) / (s - 1 / 2)) (fun s => ((1 : ℝ) : ℂ) ^ (-s - 1 / 2) / (s + 1 / 2))
    tendsto_sub_mul_one_cpow_div_nhdsGT_zero tendsto_one_cpow_div_nhdsGT_zero (fun s hs => (hX s hs).2)
    (fun s hs => (hX s hs).1) g

end

end

end S_AutomorphicForm_residue_weylIntertwining_continuation_self_dual_eq_div_measure_slab_mul_maximalCompact_pairing_mul_det
end P2MW
export P2MW.S_AutomorphicForm_residue_weylIntertwining_continuation_self_dual_eq_div_measure_slab_mul_maximalCompact_pairing_mul_det (solution)
