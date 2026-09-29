-- Prove2me | solution 1 for AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7b63350b-c693-5f97-8893-cd4ad32285ae

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
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Analytic.IsolatedZeros
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab
import Theorems.Thm_AutomorphicForm_exists_polynomial_bound_intertwining_continuation_of_isInducedSection
import Theorems.Thm_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection
import Theorems.Thm_AutomorphicForm_setIntegral_residualProj_mul_conj_eq_sum_integral_maximalCompact_residue_pairing_slab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass"
p2m_attr_erase "instance" "instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LocalGL2.swapUnit_val AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one"
p2m_attr_erase "simp" "LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq"
p2m_attr_erase "simp" "SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace AxisShift

open Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Real ComplexConjugate

private theorem integral_vertical_eq_of_differentiableOn (R : ℂ → ℂ) (a b : ℝ)
    (hR : DifferentiableOn ℂ R {s : ℂ | s.re ∈ uIcc a b})
    (hint_a : Integrable fun t : ℝ => R ((a : ℂ) + (t : ℂ) * I))
    (hint_b : Integrable fun t : ℝ => R ((b : ℂ) + (t : ℂ) * I))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ |T| →
      ∀ σ : ℝ, σ ∈ uIcc a b → ‖R ((σ : ℂ) + (T : ℂ) * I)‖ ≤ ε) :
    ∫ t : ℝ, R ((b : ℂ) + (t : ℂ) * I) = ∫ t : ℝ, R ((a : ℂ) + (t : ℂ) * I) := by

  set H : ℝ → ℂ := fun T => ∫ x : ℝ in a..b, R ((x : ℂ) + (T : ℂ) * I) with hH

  set Va : ℝ → ℂ := fun T => ∫ y : ℝ in -T..T, R ((a : ℂ) + (y : ℂ) * I) with hVa
  set Vb : ℝ → ℂ := fun T => ∫ y : ℝ in -T..T, R ((b : ℂ) + (y : ℂ) * I) with hVb

  have hrect : ∀ T : ℝ, H (-T) - H T + I • Vb T - I • Va T = 0 := by
    intro T
    have := integral_boundary_rect_eq_zero_of_differentiableOn R (⟨a, -T⟩ : ℂ) (⟨b, T⟩ : ℂ)
      (hR.mono (by
        intro s hs
        exact (mem_reProdIm.1 hs).1))
    simpa [hH, hVa, hVb] using this

  have hHlim : ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) → Tendsto (fun T => H (sgn * T)) atTop (𝓝 0) := by
    intro sgn hsgn
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := hdecay (ε / (|b - a| + 1)) (by positivity)
    refine ⟨max T₀ 0, fun T hT => ?_⟩
    have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
    have habs : T₀ ≤ |sgn * T| := by
      rcases hsgn with h | h <;> simp [h, abs_of_nonneg hT0] <;> exact le_trans (le_max_left _ _) hT
    have hbound : ‖H (sgn * T)‖ ≤ ε / (|b - a| + 1) * |b - a| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      have hx' : x ∈ uIcc a b := uIoc_subset_uIcc hx
      have := hT₀ (sgn * T) habs x hx'
      simpa using this
    rw [dist_zero_right]
    calc ‖H (sgn * T)‖ ≤ ε / (|b - a| + 1) * |b - a| := hbound
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (b - a)]
  have hH1 : Tendsto (fun T => H T) atTop (𝓝 0) := by
    simpa using hHlim 1 (Or.inl rfl)
  have hH2 : Tendsto (fun T => H (-T)) atTop (𝓝 0) := by
    simpa using hHlim (-1) (Or.inr rfl)

  have hVal : Tendsto Va atTop (𝓝 (∫ t : ℝ, R ((a : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hint_a tendsto_neg_atTop_atBot tendsto_id
  have hVbl : Tendsto Vb atTop (𝓝 (∫ t : ℝ, R ((b : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hint_b tendsto_neg_atTop_atBot tendsto_id

  have hlim : Tendsto (fun T => H (-T) - H T + I • Vb T - I • Va T) atTop
      (𝓝 (0 - 0 + I • (∫ t : ℝ, R ((b : ℂ) + (t : ℂ) * I)) - I • ∫ t : ℝ, R ((a : ℂ) + (t : ℂ) * I))) :=
    ((hH2.sub hH1).add (hVbl.const_smul I)).sub (hVal.const_smul I)
  have hconst : Tendsto (fun T => H (-T) - H T + I • Vb T - I • Va T) atTop (𝓝 0) := by
    simp only [hrect]; exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hlim hconst
  simp only [sub_zero, zero_add, smul_eq_mul] at heq
  have : I * ((∫ t : ℝ, R ((b : ℂ) + (t : ℂ) * I)) - ∫ t : ℝ, R ((a : ℂ) + (t : ℂ) * I)) = 0 := by
    rw [mul_sub]; exact heq
  rcases mul_eq_zero.1 this with hI | h
  · exact absurd hI I_ne_zero
  · exact sub_eq_zero.1 h

private lemma re_add_mul_I_ne_zero {x : ℝ} (hx : x ≠ 0) (y : ℝ) : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  exact hx this

private lemma one_div_re_add_mul_I (x y : ℝ) :
    1 / ((x : ℂ) + (y : ℂ) * I) =
      ((x / (x ^ 2 + y ^ 2) : ℝ) : ℂ) + ((-y / (x ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
  have hc : conj ((x : ℂ) + (y : ℂ) * I) = (x : ℂ) - (y : ℂ) * I := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [one_div, Complex.inv_def, Complex.normSq_add_mul_I, hc]
  push_cast
  ring

private lemma hasDerivAt_primitive (x x' : ℝ) (hx : x ≠ 0) (hx' : x' ≠ 0) (y : ℝ) :
    HasDerivAt (fun y : ℝ =>
        ((Real.arctan (y * x⁻¹) - Real.arctan (y * x'⁻¹) : ℝ) : ℂ)
          + ((-(1 / 2) * (Real.log (x ^ 2 + y ^ 2) - Real.log (x' ^ 2 + y ^ 2)) : ℝ) : ℂ) * I)
      (1 / ((x : ℂ) + (y : ℂ) * I) - 1 / ((x' : ℂ) + (y : ℂ) * I)) y := by
  have hpos : ∀ c : ℝ, c ≠ 0 → 0 < c ^ 2 + y ^ 2 := fun c hc =>
    add_pos_of_pos_of_nonneg (lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc))) (sq_nonneg y)

  have h1 : ∀ c : ℝ, c ≠ 0 →
      HasDerivAt (fun y : ℝ => Real.arctan (y * c⁻¹)) (c / (c ^ 2 + y ^ 2)) y := by
    intro c hc
    have := (hasDerivAt_mul_const c⁻¹ (x := y)).arctan
    refine this.congr_deriv ?_
    have hc2 : 0 < c ^ 2 := lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc))
    have hcy : c ^ 2 + y ^ 2 ≠ 0 := (add_pos_of_pos_of_nonneg hc2 (sq_nonneg y)).ne'
    rw [eq_div_iff hcy]
    field_simp
  have h2 : ∀ c : ℝ, c ≠ 0 →
      HasDerivAt (fun y : ℝ => Real.log (c ^ 2 + y ^ 2)) (2 * y / (c ^ 2 + y ^ 2)) y := by
    intro c hc
    have := ((hasDerivAt_pow 2 y).const_add (c ^ 2)).log (hpos c hc).ne'
    refine this.congr_deriv ?_
    simp
  have hre : HasDerivAt (fun y : ℝ => ((Real.arctan (y * x⁻¹) - Real.arctan (y * x'⁻¹) : ℝ) : ℂ))
      (((x / (x ^ 2 + y ^ 2) - x' / (x' ^ 2 + y ^ 2) : ℝ) : ℂ)) y :=
    ((h1 x hx).sub (h1 x' hx')).ofReal_comp
  have him : HasDerivAt
      (fun y : ℝ => ((-(1 / 2) * (Real.log (x ^ 2 + y ^ 2) - Real.log (x' ^ 2 + y ^ 2)) : ℝ) : ℂ) * I)
      ((((-(1 / 2)) * (2 * y / (x ^ 2 + y ^ 2) - 2 * y / (x' ^ 2 + y ^ 2)) : ℝ) : ℂ) * I) y :=
    (((h2 x hx).sub (h2 x' hx')).const_mul (-(1 / 2))).ofReal_comp.mul_const I
  refine (hre.add him).congr_deriv ?_
  rw [one_div_re_add_mul_I x y, one_div_re_add_mul_I x' y]
  have e1 : ((-(1 / 2)) * (2 * y / (x ^ 2 + y ^ 2) - 2 * y / (x' ^ 2 + y ^ 2)) : ℝ)
      = -y / (x ^ 2 + y ^ 2) - (-y / (x' ^ 2 + y ^ 2)) := by ring
  rw [e1]
  push_cast
  ring

private lemma integrable_one_div_sub (x x' : ℝ) (hx : x ≠ 0) (hx' : x' ≠ 0) :
    Integrable fun y : ℝ => 1 / ((x : ℂ) + (y : ℂ) * I) - 1 / ((x' : ℂ) + (y : ℂ) * I) := by
  set m : ℝ := min |x| |x'| with hm
  have hm0 : 0 < m := lt_min (abs_pos.2 hx) (abs_pos.2 hx')
  set μ0 : ℝ := min (m ^ 2) 1 with hμ0
  have hμ0pos : 0 < μ0 := lt_min (by positivity) one_pos
  have hμ0le1 : μ0 ≤ 1 := min_le_right _ _
  have hμ0lem : μ0 ≤ m ^ 2 := min_le_left _ _
  set K : ℝ := |x' - x| * (2 / μ0) with hK
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K) ?_ ?_
  · refine (Continuous.sub ?_ ?_).aestronglyMeasurable
    · exact continuous_const.div (by fun_prop) (re_add_mul_I_ne_zero hx)
    · exact continuous_const.div (by fun_prop) (re_add_mul_I_ne_zero hx')
  · refine ae_of_all _ fun y => ?_
    have hu := re_add_mul_I_ne_zero hx y
    have hv := re_add_mul_I_ne_zero hx' y
    have hform : 1 / ((x : ℂ) + (y : ℂ) * I) - 1 / ((x' : ℂ) + (y : ℂ) * I)
        = ((x' - x : ℝ) : ℂ) / (((x : ℂ) + (y : ℂ) * I) * ((x' : ℂ) + (y : ℂ) * I)) := by
      rw [one_div, one_div, inv_sub_inv hu hv]
      push_cast
      ring
    rw [hform, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]

    set M : ℝ := max m |y| with hM
    have hM0 : 0 ≤ M := le_trans hm0.le (le_max_left _ _)
    have hnorm_ge : ∀ c : ℝ, c ≠ 0 → m ≤ |c| → M ≤ ‖(c : ℂ) + (y : ℂ) * I‖ := by
      intro c hc hmc
      refine max_le ?_ ?_
      · refine le_trans hmc ?_
        have := abs_re_le_norm ((c : ℂ) + (y : ℂ) * I)
        simpa using this
      · have := abs_im_le_norm ((c : ℂ) + (y : ℂ) * I)
        simpa using this
    have hU : M ≤ ‖(x : ℂ) + (y : ℂ) * I‖ := hnorm_ge x hx (min_le_left _ _)
    have hV : M ≤ ‖(x' : ℂ) + (y : ℂ) * I‖ := hnorm_ge x' hx' (min_le_right _ _)
    have hprod : M ^ 2 ≤ ‖(x : ℂ) + (y : ℂ) * I‖ * ‖(x' : ℂ) + (y : ℂ) * I‖ := by
      rw [sq]; exact mul_le_mul hU hV hM0 (norm_nonneg _)
    have hmM : m ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hm0.le (le_max_left _ _) 2
    have hyM : y ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg y) (le_max_right _ _) 2
    have hM2 : μ0 * (1 + y ^ 2) ≤ 2 * M ^ 2 := by nlinarith [sq_nonneg y]
    have hMpos : 0 < M ^ 2 := lt_of_lt_of_le (by positivity) hmM
    calc |x' - x| / (‖(x : ℂ) + (y : ℂ) * I‖ * ‖(x' : ℂ) + (y : ℂ) * I‖)
        ≤ |x' - x| / (M ^ 2) := div_le_div_of_nonneg_left (abs_nonneg _) hMpos hprod
      _ ≤ |x' - x| / (μ0 * (1 + y ^ 2) / 2) := by
        refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
        linarith
      _ = K * (1 + y ^ 2)⁻¹ := by
        rw [hK]
        field_simp

private lemma tendsto_arctan_mul_atTop_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => Real.arctan (y * c)) atTop (𝓝 (π / 2)) :=
  (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atTop_mul_const hc)

private lemma tendsto_arctan_mul_atBot_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => Real.arctan (y * c)) atBot (𝓝 (-(π / 2))) :=
  (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atBot_mul_const hc)

private lemma tendsto_arctan_mul_atTop_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun y : ℝ => Real.arctan (y * c)) atTop (𝓝 (-(π / 2))) :=
  (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atTop_mul_const_of_neg hc)

private lemma tendsto_arctan_mul_atBot_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun y : ℝ => Real.arctan (y * c)) atBot (𝓝 (π / 2)) :=
  (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_id.atBot_mul_const_of_neg hc)

private lemma tendsto_log_sub_log (x x' : ℝ) {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => y ^ 2) l atTop) :
    Tendsto (fun y : ℝ => Real.log (x ^ 2 + y ^ 2) - Real.log (x' ^ 2 + y ^ 2)) l (𝓝 0) := by
  have hev : ∀ᶠ y in l, 0 < x' ^ 2 + y ^ 2 ∧ 0 < x ^ 2 + y ^ 2 := by
    filter_upwards [hl.eventually_gt_atTop 0] with y hy using ⟨by positivity, by positivity⟩

  have hratio : Tendsto (fun y : ℝ => (x ^ 2 + y ^ 2) / (x' ^ 2 + y ^ 2)) l (𝓝 1) := by
    have h1 : Tendsto (fun y : ℝ => 1 + (x ^ 2 - x' ^ 2) * (x' ^ 2 + y ^ 2)⁻¹) l (𝓝 (1 + (x ^ 2 - x' ^ 2) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul
        ((tendsto_const_nhds.add_atTop hl).inv_tendsto_atTop))
    rw [mul_zero, add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hev] with y hy
    have hy1 := hy.1.ne'
    field_simp
    ring
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [hev] with y hy
  simp [Function.comp, Real.log_div hy.2.ne' hy.1.ne']

private theorem integral_one_div_sub_one_div (x x' : ℝ) (hx : x ≠ 0) (hx' : x' ≠ 0) {A B A' B' : ℝ}
    (hA : Tendsto (fun y : ℝ => Real.arctan (y * x⁻¹)) atTop (𝓝 A))
    (hB : Tendsto (fun y : ℝ => Real.arctan (y * x⁻¹)) atBot (𝓝 B))
    (hA' : Tendsto (fun y : ℝ => Real.arctan (y * x'⁻¹)) atTop (𝓝 A'))
    (hB' : Tendsto (fun y : ℝ => Real.arctan (y * x'⁻¹)) atBot (𝓝 B')) :
    ∫ y : ℝ, (1 / ((x : ℂ) + (y : ℂ) * I) - 1 / ((x' : ℂ) + (y : ℂ) * I))
      = (((A - A') - (B - B') : ℝ) : ℂ) := by
  have hsq_top : Tendsto (fun y : ℝ => y ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hsq_bot : Tendsto (fun y : ℝ => y ^ 2) atBot atTop := by
    have h : Tendsto (fun y : ℝ => (-y) ^ 2) atBot atTop :=
      (tendsto_pow_atTop two_ne_zero).comp tendsto_neg_atBot_atTop
    simpa using h
  have htop : Tendsto (fun y : ℝ =>
        ((Real.arctan (y * x⁻¹) - Real.arctan (y * x'⁻¹) : ℝ) : ℂ)
          + ((-(1 / 2) * (Real.log (x ^ 2 + y ^ 2) - Real.log (x' ^ 2 + y ^ 2)) : ℝ) : ℂ) * I)
      atTop (𝓝 (((A - A' : ℝ) : ℂ) + ((-(1 / 2) * 0 : ℝ) : ℂ) * I)) :=
    ((continuous_ofReal.tendsto _).comp (hA.sub hA')).add
      (((continuous_ofReal.tendsto _).comp
        ((tendsto_log_sub_log x x' hsq_top).const_mul (-(1 / 2)))).mul_const I)
  have hbot : Tendsto (fun y : ℝ =>
        ((Real.arctan (y * x⁻¹) - Real.arctan (y * x'⁻¹) : ℝ) : ℂ)
          + ((-(1 / 2) * (Real.log (x ^ 2 + y ^ 2) - Real.log (x' ^ 2 + y ^ 2)) : ℝ) : ℂ) * I)
      atBot (𝓝 (((B - B' : ℝ) : ℂ) + ((-(1 / 2) * 0 : ℝ) : ℂ) * I)) :=
    ((continuous_ofReal.tendsto _).comp (hB.sub hB')).add
      (((continuous_ofReal.tendsto _).comp
        ((tendsto_log_sub_log x x' hsq_bot).const_mul (-(1 / 2)))).mul_const I)
  have := integral_of_hasDerivAt_of_tendsto (hasDerivAt_primitive x x' hx hx')
    (integrable_one_div_sub x x' hx hx') hbot htop
  rw [this]
  push_cast
  ring

private theorem integral_kernel_right (s₀ : ℂ) (L σ : ℝ) (hL : 0 < L) (hσ : s₀.re < σ) :
    ∫ t : ℝ, (1 / ((σ : ℂ) + (t : ℂ) * I - s₀) - 1 / ((σ : ℂ) + (t : ℂ) * I - (s₀ - L))) = 0 := by
  have hx : 0 < σ - s₀.re := sub_pos.2 hσ
  have hx' : 0 < σ - s₀.re + L := by linarith
  have key := integral_one_div_sub_one_div (σ - s₀.re) (σ - s₀.re + L) hx.ne' hx'.ne'
    (tendsto_arctan_mul_atTop_pos (inv_pos.2 hx)) (tendsto_arctan_mul_atBot_pos (inv_pos.2 hx))
    (tendsto_arctan_mul_atTop_pos (inv_pos.2 hx')) (tendsto_arctan_mul_atBot_pos (inv_pos.2 hx'))
  have hshift := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => 1 / (((σ - s₀.re : ℝ) : ℂ) + (t : ℂ) * I) - 1 / (((σ - s₀.re + L : ℝ) : ℂ) + (t : ℂ) * I))
    s₀.im
  have hpt : ∀ t : ℝ,
      1 / ((σ : ℂ) + (t : ℂ) * I - s₀) - 1 / ((σ : ℂ) + (t : ℂ) * I - (s₀ - L))
        = 1 / (((σ - s₀.re : ℝ) : ℂ) + ((t - s₀.im : ℝ) : ℂ) * I)
          - 1 / (((σ - s₀.re + L : ℝ) : ℂ) + ((t - s₀.im : ℝ) : ℂ) * I) := by
    intro t
    conv_lhs => rw [← re_add_im s₀]
    push_cast
    ring_nf
  simp_rw [hpt]
  rw [hshift, key]
  simp

private theorem integral_kernel_between (s₀ : ℂ) (L σ : ℝ) (hσ : σ < s₀.re) (hσ' : s₀.re - L < σ) :
    ∫ t : ℝ, (1 / ((σ : ℂ) + (t : ℂ) * I - s₀) - 1 / ((σ : ℂ) + (t : ℂ) * I - (s₀ - L)))
      = -(2 * π : ℂ) := by
  have hx : σ - s₀.re < 0 := sub_neg.2 hσ
  have hx' : 0 < σ - s₀.re + L := by linarith
  have key := integral_one_div_sub_one_div (σ - s₀.re) (σ - s₀.re + L) hx.ne hx'.ne'
    (tendsto_arctan_mul_atTop_neg (inv_lt_zero.2 hx)) (tendsto_arctan_mul_atBot_neg (inv_lt_zero.2 hx))
    (tendsto_arctan_mul_atTop_pos (inv_pos.2 hx')) (tendsto_arctan_mul_atBot_pos (inv_pos.2 hx'))
  have hshift := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => 1 / (((σ - s₀.re : ℝ) : ℂ) + (t : ℂ) * I) - 1 / (((σ - s₀.re + L : ℝ) : ℂ) + (t : ℂ) * I))
    s₀.im
  have hpt : ∀ t : ℝ,
      1 / ((σ : ℂ) + (t : ℂ) * I - s₀) - 1 / ((σ : ℂ) + (t : ℂ) * I - (s₀ - L))
        = 1 / (((σ - s₀.re : ℝ) : ℂ) + ((t - s₀.im : ℝ) : ℂ) * I)
          - 1 / (((σ - s₀.re + L : ℝ) : ℂ) + ((t - s₀.im : ℝ) : ℂ) * I) := by
    intro t
    conv_lhs => rw [← re_add_im s₀]
    push_cast
    ring_nf
  simp_rw [hpt]
  rw [hshift, key]
  push_cast
  ring

private theorem integrable_kernel (s₀ : ℂ) (L σ : ℝ) (hσ : σ ≠ s₀.re) (hσ' : σ ≠ s₀.re - L) :
    Integrable fun t : ℝ =>
      1 / ((σ : ℂ) + (t : ℂ) * I - s₀) - 1 / ((σ : ℂ) + (t : ℂ) * I - (s₀ - L)) := by
  have hx : σ - s₀.re ≠ 0 := sub_ne_zero.2 hσ
  have hx' : σ - s₀.re + L ≠ 0 := by
    intro h; apply hσ'; linarith
  have base := integrable_one_div_sub (σ - s₀.re) (σ - s₀.re + L) hx hx'
  have hpt : ∀ t : ℝ,
      1 / ((σ : ℂ) + (t : ℂ) * I - s₀) - 1 / ((σ : ℂ) + (t : ℂ) * I - (s₀ - L))
        = 1 / (((σ - s₀.re : ℝ) : ℂ) + ((t - s₀.im : ℝ) : ℂ) * I)
          - 1 / (((σ - s₀.re + L : ℝ) : ℂ) + ((t - s₀.im : ℝ) : ℂ) * I) := by
    intro t
    conv_lhs => rw [← re_add_im s₀]
    push_cast
    ring_nf
  simp_rw [hpt]
  exact base.comp_sub_right s₀.im

private theorem norm_kernel_le (s₀ : ℂ) (L : ℝ) (hL : 0 < L) (σ T : ℝ) (hT : |s₀.im| + 1 ≤ |T|) :
    ‖1 / ((σ : ℂ) + (T : ℂ) * I - s₀) - 1 / ((σ : ℂ) + (T : ℂ) * I - (s₀ - L))‖
      ≤ L / (|T| - |s₀.im|) ^ 2 := by
  have hgap : 1 ≤ |T| - |s₀.im| := by linarith
  have him : ∀ w : ℂ, w = (σ : ℂ) + (T : ℂ) * I - s₀ ∨ w = (σ : ℂ) + (T : ℂ) * I - (s₀ - L) →
      |T| - |s₀.im| ≤ ‖w‖ := by
    intro w hw
    have hwim : w.im = T - s₀.im := by
      rcases hw with h | h <;> simp [h]
    calc |T| - |s₀.im| ≤ |T - s₀.im| := abs_sub_abs_le_abs_sub T s₀.im
      _ = |w.im| := by rw [hwim]
      _ ≤ ‖w‖ := abs_im_le_norm w
  have hu0 : (σ : ℂ) + (T : ℂ) * I - s₀ ≠ 0 := by
    intro h
    have := him _ (Or.inl rfl)
    rw [h, norm_zero] at this
    linarith
  have hv0 : (σ : ℂ) + (T : ℂ) * I - (s₀ - L) ≠ 0 := by
    intro h
    have := him _ (Or.inr rfl)
    rw [h, norm_zero] at this
    linarith
  rw [one_div, one_div, inv_sub_inv hu0 hv0]
  have hnum : (σ : ℂ) + (T : ℂ) * I - (s₀ - L) - ((σ : ℂ) + (T : ℂ) * I - s₀) = (L : ℂ) := by ring
  rw [hnum, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  have hprod : (|T| - |s₀.im|) ^ 2 ≤ ‖(σ : ℂ) + (T : ℂ) * I - s₀‖ * ‖(σ : ℂ) + (T : ℂ) * I - (s₀ - L)‖ := by
    rw [sq]
    exact mul_le_mul (him _ (Or.inl rfl)) (him _ (Or.inr rfl)) (by linarith) (norm_nonneg _)
  exact div_le_div_of_nonneg_left hL.le (by positivity) hprod

private theorem integral_vertical_sub_integral_vertical_eq_two_pi_mul_residue
    (G : ℂ → ℂ) (ρ s₀ : ℂ) (a b : ℝ) (ha : a < s₀.re) (hb : s₀.re < b)
    (U : Set ℂ) (hUstrip : {s : ℂ | a ≤ s.re ∧ s.re ≤ b} ⊆ U)
    (R : ℂ → ℂ) (hR : DifferentiableOn ℂ R U)
    (hGR : ∀ s ∈ U, s ≠ s₀ → G s = R s + ρ / (s - s₀))
    (hint_a : Integrable fun t : ℝ => G ((a : ℂ) + (t : ℂ) * I))
    (hint_b : Integrable fun t : ℝ => G ((b : ℂ) + (t : ℂ) * I))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ |T| →
      ∀ σ : ℝ, a ≤ σ → σ ≤ b → ‖G ((σ : ℂ) + (T : ℂ) * I)‖ ≤ ε) :
    (∫ t : ℝ, G ((b : ℂ) + (t : ℂ) * I)) - (∫ t : ℝ, G ((a : ℂ) + (t : ℂ) * I)) = 2 * π * ρ := by
  have hab : a ≤ b := (ha.trans hb).le

  set L : ℝ := s₀.re - a + 1 with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  set Q : ℂ → ℂ := fun s => ρ * (1 / (s - s₀) - 1 / (s - (s₀ - L))) with hQ
  set R₁ : ℂ → ℂ := fun s => R s + ρ / (s - (s₀ - L)) with hR₁

  have hGQ : ∀ s ∈ U, s ≠ s₀ → G s - Q s = R₁ s := by
    intro s hs hs0
    rw [hGR s hs hs0, hQ, hR₁]
    simp only
    ring
  have hstripU : ∀ σ t : ℝ, a ≤ σ → σ ≤ b → ((σ : ℂ) + (t : ℂ) * I) ∈ U := fun σ t h1 h2 =>
    hUstrip ⟨by simpa using h1, by simpa using h2⟩
  have hne_line : ∀ σ t : ℝ, σ ≠ s₀.re → ((σ : ℂ) + (t : ℂ) * I) ≠ s₀ := by
    intro σ t hσ h
    apply hσ
    have := congrArg Complex.re h
    simpa using this

  have hR₁d : DifferentiableOn ℂ R₁ {s : ℂ | s.re ∈ uIcc a b} := by
    intro s hs
    have hs' : a ≤ s.re ∧ s.re ≤ b := by
      simpa [uIcc_of_le hab] using hs
    have hsU : s ∈ U := hUstrip hs'
    have hs1 : s - (s₀ - L) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp [hL] at this
      linarith [hs'.1]
    refine ((hR s hsU).add ?_).mono (fun z hz => hUstrip (by simpa [uIcc_of_le hab] using hz))
    exact ((differentiableAt_const ρ).div ((differentiableAt_id).sub (differentiableAt_const _)) hs1)
      |>.differentiableWithinAt

  have hQa : Integrable fun t : ℝ => Q ((a : ℂ) + (t : ℂ) * I) := by
    simpa [hQ] using (integrable_kernel s₀ L a ha.ne (by rw [hL]; linarith)).const_mul ρ
  have hQb : Integrable fun t : ℝ => Q ((b : ℂ) + (t : ℂ) * I) := by
    simpa [hQ] using (integrable_kernel s₀ L b hb.ne' (by rw [hL]; linarith)).const_mul ρ

  have hR₁a_eq : (fun t : ℝ => R₁ ((a : ℂ) + (t : ℂ) * I))
      = fun t : ℝ => G ((a : ℂ) + (t : ℂ) * I) - Q ((a : ℂ) + (t : ℂ) * I) := by
    funext t; exact (hGQ _ (hstripU a t le_rfl hab) (hne_line a t ha.ne)).symm
  have hR₁b_eq : (fun t : ℝ => R₁ ((b : ℂ) + (t : ℂ) * I))
      = fun t : ℝ => G ((b : ℂ) + (t : ℂ) * I) - Q ((b : ℂ) + (t : ℂ) * I) := by
    funext t; exact (hGQ _ (hstripU b t hab le_rfl) (hne_line b t hb.ne')).symm
  have hR₁a : Integrable fun t : ℝ => R₁ ((a : ℂ) + (t : ℂ) * I) := by
    rw [hR₁a_eq]; exact hint_a.sub hQa
  have hR₁b : Integrable fun t : ℝ => R₁ ((b : ℂ) + (t : ℂ) * I) := by
    rw [hR₁b_eq]; exact hint_b.sub hQb

  have hR₁decay : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ |T| →
      ∀ σ : ℝ, σ ∈ uIcc a b → ‖R₁ ((σ : ℂ) + (T : ℂ) * I)‖ ≤ ε := by
    intro ε hε
    obtain ⟨T₀, hT₀⟩ := hdecay (ε / 2) (by positivity)

    obtain ⟨C, hC1, hC⟩ : ∃ C : ℝ, 1 ≤ C ∧ L / C ^ 2 ≤ ε / (2 * (‖ρ‖ + 1)) := by
      refine ⟨max 1 (Real.sqrt (L * (2 * (‖ρ‖ + 1)) / ε)), le_max_left _ _, ?_⟩
      have hden : 0 < 2 * (‖ρ‖ + 1) := by positivity
      have hsq : L * (2 * (‖ρ‖ + 1)) / ε ≤ (max 1 (Real.sqrt (L * (2 * (‖ρ‖ + 1)) / ε))) ^ 2 := by
        calc L * (2 * (‖ρ‖ + 1)) / ε = (Real.sqrt (L * (2 * (‖ρ‖ + 1)) / ε)) ^ 2 := by
              rw [Real.sq_sqrt]; positivity
          _ ≤ (max 1 (Real.sqrt (L * (2 * (‖ρ‖ + 1)) / ε))) ^ 2 :=
              pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2
      have hCpos : 0 < (max 1 (Real.sqrt (L * (2 * (‖ρ‖ + 1)) / ε))) ^ 2 := by positivity
      rw [div_le_div_iff₀ hCpos hden]
      rw [div_le_iff₀ hε] at hsq
      nlinarith
    refine ⟨max T₀ (|s₀.im| + C), fun T hT σ hσ => ?_⟩
    have hσ' : a ≤ σ ∧ σ ≤ b := by simpa [uIcc_of_le hab] using hσ
    have hT1 : T₀ ≤ |T| := le_trans (le_max_left _ _) hT
    have hT2 : |s₀.im| + C ≤ |T| := le_trans (le_max_right _ _) hT
    have hpt : ((σ : ℂ) + (T : ℂ) * I) ≠ s₀ := by
      intro h
      have := congrArg Complex.im h
      simp at this
      have : |T| = |s₀.im| := by rw [this]
      linarith
    rw [← hGQ _ (hstripU σ T hσ'.1 hσ'.2) hpt]
    have hG := hT₀ T hT1 σ hσ'.1 hσ'.2
    have hKer := norm_kernel_le s₀ L hLpos σ T (by linarith)
    have hQn : ‖Q ((σ : ℂ) + (T : ℂ) * I)‖ ≤ ε / 2 := by
      rw [hQ]
      simp only
      rw [norm_mul]
      have hden : C ^ 2 ≤ (|T| - |s₀.im|) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hk : ‖1 / ((σ : ℂ) + (T : ℂ) * I - s₀) - 1 / ((σ : ℂ) + (T : ℂ) * I - (s₀ - L))‖
          ≤ ε / (2 * (‖ρ‖ + 1)) := by
        refine hKer.trans (le_trans ?_ hC)
        exact div_le_div_of_nonneg_left hLpos.le (by positivity) hden
      calc ‖ρ‖ * ‖1 / ((σ : ℂ) + (T : ℂ) * I - s₀) - 1 / ((σ : ℂ) + (T : ℂ) * I - (s₀ - L))‖
          ≤ ‖ρ‖ * (ε / (2 * (‖ρ‖ + 1))) := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
        _ ≤ (‖ρ‖ + 1) * (ε / (2 * (‖ρ‖ + 1))) := by gcongr; linarith
        _ = ε / 2 := by field_simp
    calc ‖G ((σ : ℂ) + (T : ℂ) * I) - Q ((σ : ℂ) + (T : ℂ) * I)‖
        ≤ ‖G ((σ : ℂ) + (T : ℂ) * I)‖ + ‖Q ((σ : ℂ) + (T : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add hG hQn
      _ = ε := by ring

  have hshift := integral_vertical_eq_of_differentiableOn R₁ a b hR₁d hR₁a hR₁b hR₁decay

  have hQa_val : ∫ t : ℝ, Q ((a : ℂ) + (t : ℂ) * I) = ρ * (-(2 * π : ℂ)) := by
    have := integral_kernel_between s₀ L a ha (by rw [hL]; linarith)
    rw [hQ]
    simp only
    rw [MeasureTheory.integral_const_mul, this]
  have hQb_val : ∫ t : ℝ, Q ((b : ℂ) + (t : ℂ) * I) = 0 := by
    have := integral_kernel_right s₀ L b hLpos hb
    rw [hQ]
    simp only
    rw [MeasureTheory.integral_const_mul, this, mul_zero]

  have hGa : ∫ t : ℝ, G ((a : ℂ) + (t : ℂ) * I)
      = (∫ t : ℝ, R₁ ((a : ℂ) + (t : ℂ) * I)) + ∫ t : ℝ, Q ((a : ℂ) + (t : ℂ) * I) := by
    rw [hR₁a_eq, integral_sub hint_a hQa]; ring
  have hGb : ∫ t : ℝ, G ((b : ℂ) + (t : ℂ) * I)
      = (∫ t : ℝ, R₁ ((b : ℂ) + (t : ℂ) * I)) + ∫ t : ℝ, Q ((b : ℂ) + (t : ℂ) * I) := by
    rw [hR₁b_eq, integral_sub hint_b hQb]; ring
  rw [hGa, hGb, hshift, hQa_val, hQb_val]
  ring

end AxisShift

namespace AxisPerIndex

open Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Real ComplexConjugate

variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]

private lemma differentiableAt_conj_comp {f : ℂ → ℂ} {s : ℂ} (hf : DifferentiableAt ℂ f (conj s)) :
    DifferentiableAt ℂ (fun z => conj (f (conj z))) s := by
  have := hf.conj_conj
  simpa [Function.comp_def] using this

private theorem integral_integral_shift
    (μK : Measure K) [IsFiniteMeasure μK]
    (φ ψ M Mreg : ℂ → K → ℂ) (w q : ℂ) (hq : q.re = 1 / 2)
    (U : Set ℂ) (hU : IsOpen U) (hUsub : {s : ℂ | 0 ≤ s.re} ⊆ U)
    (hφc : Continuous (Function.uncurry φ)) (hψc : Continuous (Function.uncurry ψ))
    (hφa : ∀ k, Differentiable ℂ (fun s => φ s k)) (hψa : ∀ k, Differentiable ℂ (fun s => ψ s k))
    (hMa : ∀ k, DifferentiableOn ℂ (fun s => Mreg s k) U)
    (hMjc : ContinuousOn (Function.uncurry Mreg) (U ×ˢ Set.univ))
    (hMM : ∀ s ∈ U, s ≠ q → ∀ k, Mreg s k = (s - q) * M s k)
    (N : ℕ) (A Bψ δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hA : 0 ≤ A) (hBψ : 0 ≤ Bψ)
    (mφ : ℝ → ℝ) (hmφ : Integrable mφ) (Bφ : ℝ) (hmφB : ∀ t, mφ t ≤ Bφ)
    (hφb : ∀ (σ t : ℝ) (k : K), 0 ≤ σ → σ ≤ 1 →
      (1 + |t|) ^ (N + 1) * ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ mφ t)
    (hψb : ∀ (σ t : ℝ) (k : K), -1 ≤ σ → σ ≤ 0 → ‖ψ ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ Bψ)
    (hMg : ∀ (s : ℂ) (k : K), 0 ≤ s.re → s.re ≤ 1 → δ ≤ ‖s - q‖ → ‖M s k‖ ≤ A * (1 + |s.im|) ^ N) :
    ∫ t : ℝ, ((∫ k, φ (((1 : ℝ) : ℂ) + (t : ℂ) * I) k * conj (ψ (-((1 : ℝ) : ℂ) + (t : ℂ) * I) k) ∂μK)
        + w * ∫ k, φ (((1 : ℝ) : ℂ) + (t : ℂ) * I) k * conj (M (((1 : ℝ) : ℂ) - (t : ℂ) * I) k) ∂μK)
      = (∫ t : ℝ, ((∫ k, φ ((t : ℂ) * I) k * conj (ψ ((t : ℂ) * I) k) ∂μK)
          + w * ∫ k, φ ((t : ℂ) * I) k
              * conj (limUnder (𝓝[≠] (-((t : ℂ) * I))) (fun s => M s k)) ∂μK))
        + 2 * π * (w * ∫ k, φ (conj q) k * conj (Mreg q k) ∂μK) := by

  set p : ℂ := conj q with hp
  have hp_re : p.re = 1 / 2 := by simp [hp, hq]
  have hconj_p : conj p = q := by simp [hp]
  have hqU : q ∈ U := hUsub (by simp [hq])
  set U' : Set ℂ := {s | conj s ∈ U} with hU'
  have hU'open : IsOpen U' := hU.preimage continuous_conj
  have hpU' : p ∈ U' := by simpa [hU', hp] using hqU
  have hU'sub : {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1} ⊆ U' := fun s hs => hUsub (by simpa using hs.1)

  have hMeq : ∀ s ∈ U, s ≠ q → ∀ k, M s k = Mreg s k / (s - q) := by
    intro s hs hsq k
    rw [hMM s hs hsq k, mul_div_cancel_left₀ _ (sub_ne_zero.2 hsq)]

  have hMcont : ∀ k, ∀ s ∈ U, s ≠ q → ContinuousAt (fun z => M z k) s := by
    intro k s hs hsq
    have hev : (fun z => Mreg z k / (z - q)) =ᶠ[𝓝 s] fun z => M z k := by
      filter_upwards [hU.mem_nhds hs, isOpen_ne.mem_nhds hsq] with z hz hzq
      exact (hMeq z hz hzq k).symm
    refine ContinuousAt.congr ?_ hev
    have h1 : ContinuousAt (fun z => Mreg z k) s :=
      ((hMa k).differentiableAt (hU.mem_nhds hs)).continuousAt
    exact h1.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hsq)

  set g : ℂ → K → ℂ := fun s k => φ s k * conj (ψ (-conj s) k) + w * (φ s k * conj (M (conj s) k)) with hg
  set Nf : K → ℂ → ℂ := fun k s => φ s k * conj (Mreg (conj s) k) with hNf
  set R : K → ℂ → ℂ := fun k s => φ s k * conj (ψ (-conj s) k) + w * dslope (Nf k) p s with hR
  set ρ : K → ℂ := fun k => w * Nf k p with hρ

  have hAdiff : ∀ k, Differentiable ℂ (fun s => φ s k * conj (ψ (-conj s) k)) := by
    intro k s
    refine (hφa k s).mul ?_
    have h : DifferentiableAt ℂ (fun z => ψ (-z) k) (conj s) := ((hψa k).comp differentiable_neg) _
    exact differentiableAt_conj_comp h
  have hNfdiff : ∀ k, DifferentiableOn ℂ (Nf k) U' := by
    intro k s hs
    refine (((hφa k s).mul ?_).differentiableWithinAt)
    exact differentiableAt_conj_comp ((hMa k).differentiableAt (hU.mem_nhds hs))
  have hdslope : ∀ k, DifferentiableOn ℂ (dslope (Nf k) p) U' := by
    intro k s hs
    rcases eq_or_ne s p with hsp | hsp
    · rw [hsp] at hs ⊢
      have han : AnalyticAt ℂ (Nf k) p := (hNfdiff k).analyticOnNhd hU'open p hs
      obtain ⟨P, hP⟩ := han
      exact (hP.has_fpower_series_dslope_fslope.analyticAt.differentiableAt).differentiableWithinAt
    · exact ((differentiableAt_dslope_of_ne hsp).2
        ((hNfdiff k).differentiableAt (hU'open.mem_nhds hs))).differentiableWithinAt
  have hRdiff : ∀ k, DifferentiableOn ℂ (R k) U' := by
    intro k
    exact (hAdiff k).differentiableOn.add ((hdslope k).const_mul w)

  have hGR : ∀ k, ∀ s ∈ U', s ≠ p → g s k = R k s + ρ k / (s - p) := by
    intro k s hs hsp
    have hcs : conj s ∈ U := hs
    have hcsq : conj s ≠ q := by
      intro h; apply hsp; rw [hp, ← h, conj_conj]
    have hM := hMeq (conj s) hcs hcsq k
    have hsp' : s - p ≠ 0 := sub_ne_zero.2 hsp
    have hconjden : conj (conj s - q) = s - p := by simp [hp]
    have hslope : Nf k s = Nf k p + (s - p) * dslope (Nf k) p s := by
      have := sub_smul_dslope (Nf k) p s
      rw [smul_eq_mul] at this
      rw [this]; ring
    simp only [hg, hR, hρ]
    rw [hM, map_div₀, hconjden]
    have : φ s k * (conj (Mreg (conj s) k) / (s - p)) = Nf k s / (s - p) := by
      simp only [hNf]; ring
    rw [this, hslope]
    field_simp
    ring

  have hconj_pt : ∀ σ t : ℝ, conj ((σ : ℂ) + (t : ℂ) * I) = (σ : ℂ) - (t : ℂ) * I := by
    intro σ t
    rw [map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]; ring
  have hneg_conj_pt : ∀ σ t : ℝ, -conj ((σ : ℂ) + (t : ℂ) * I) = ((-σ : ℝ) : ℂ) + (t : ℂ) * I := by
    intro σ t
    rw [hconj_pt]; push_cast; ring
  set C : ℝ := Bψ + ‖w‖ * A with hC
  have hC0 : 0 ≤ C := by positivity
  have hmφ0 : ∀ (t : ℝ) (k : K), 0 ≤ mφ t := fun t k =>
    le_trans (by positivity) (hφb 0 t k le_rfl zero_le_one)
  have hpow1 : ∀ t : ℝ, (1 : ℝ) ≤ (1 + |t|) ^ (N + 1) := fun t =>
    one_le_pow₀ (by linarith [abs_nonneg t])

  have hg_norm : ∀ (σ t : ℝ) (k : K), 0 ≤ σ → σ ≤ 1 →
      ‖g ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖
        * (Bψ + ‖w‖ * ‖M ((σ : ℂ) - (t : ℂ) * I) k‖) := by
    intro σ t k h0 h1
    simp only [hg]
    rw [hneg_conj_pt, hconj_pt]
    have hψ := hψb (-σ) t k (by linarith) (by linarith)
    calc ‖φ ((σ : ℂ) + (t : ℂ) * I) k * conj (ψ (((-σ : ℝ) : ℂ) + (t : ℂ) * I) k)
            + w * (φ ((σ : ℂ) + (t : ℂ) * I) k * conj (M ((σ : ℂ) - (t : ℂ) * I) k))‖
        ≤ ‖φ ((σ : ℂ) + (t : ℂ) * I) k * conj (ψ (((-σ : ℝ) : ℂ) + (t : ℂ) * I) k)‖
            + ‖w * (φ ((σ : ℂ) + (t : ℂ) * I) k * conj (M ((σ : ℂ) - (t : ℂ) * I) k))‖ := norm_add_le _ _
      _ = ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ * ‖ψ (((-σ : ℝ) : ℂ) + (t : ℂ) * I) k‖
            + ‖w‖ * (‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ * ‖M ((σ : ℂ) - (t : ℂ) * I) k‖) := by
          simp only [norm_mul, Complex.norm_conj]
      _ ≤ ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ * Bψ
            + ‖w‖ * (‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ * ‖M ((σ : ℂ) - (t : ℂ) * I) k‖) := by
          gcongr
      _ = _ := by ring

  have hM_norm : ∀ (σ t : ℝ) (k : K), 0 ≤ σ → σ ≤ 1 → δ ≤ ‖((σ : ℂ) - (t : ℂ) * I) - q‖ →
      ‖M ((σ : ℂ) - (t : ℂ) * I) k‖ ≤ A * (1 + |t|) ^ N := by
    intro σ t k h0 h1 hsep
    have := hMg ((σ : ℂ) - (t : ℂ) * I) k (by simpa using h0) (by simpa using h1) hsep
    simpa using this

  have hsep_line : ∀ (σ t : ℝ), σ = 0 ∨ σ = 1 → δ ≤ ‖((σ : ℂ) - (t : ℂ) * I) - q‖ := by
    intro σ t hσ
    refine le_trans ?_ (abs_re_le_norm _)
    have hre : (((σ : ℂ) - (t : ℂ) * I) - q).re = σ - 1 / 2 := by simp [hq]
    rw [hre]
    rcases hσ with rfl | rfl
    · rw [zero_sub, abs_neg, abs_of_pos one_half_pos]; exact hδ'
    · rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, abs_of_pos one_half_pos]; exact hδ'
  have hsep_far : ∀ (σ t : ℝ), |q.im| + 1 ≤ |t| → δ ≤ ‖((σ : ℂ) - (t : ℂ) * I) - q‖ := by
    intro σ t ht
    refine le_trans ?_ (abs_im_le_norm _)
    have him : (((σ : ℂ) - (t : ℂ) * I) - q).im = -t - q.im := by simp
    rw [him]
    have h1 : |-t| ≤ |-t - q.im| + |q.im| := by
      calc |-t| = |(-t - q.im) + q.im| := by rw [sub_add_cancel]
        _ ≤ |-t - q.im| + |q.im| := abs_add_le _ _
    rw [abs_neg] at h1
    linarith

  have hline_bd : ∀ (σ t : ℝ) (k : K), σ = 0 ∨ σ = 1 →
      ‖g ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ mφ t * C := by
    intro σ t k hσ
    have h0 : 0 ≤ σ := by rcases hσ with rfl | rfl <;> norm_num
    have h1 : σ ≤ 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hmk := hmφ0 t k
    have hφ1 : ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ mφ t / (1 + |t|) ^ (N + 1) := by
      rw [le_div_iff₀ (by positivity), mul_comm]; exact hφb σ t k h0 h1
    have hM1 := hM_norm σ t k h0 h1 (hsep_line σ t hσ)
    have hpowN : (1 + |t|) ^ N ≤ (1 + |t|) ^ (N + 1) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (Nat.le_succ N)
    have hpos : 0 < (1 + |t|) ^ (N + 1) := by positivity
    calc ‖g ((σ : ℂ) + (t : ℂ) * I) k‖
        ≤ ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ * (Bψ + ‖w‖ * ‖M ((σ : ℂ) - (t : ℂ) * I) k‖) :=
          hg_norm σ t k h0 h1
      _ ≤ (mφ t / (1 + |t|) ^ (N + 1)) * (Bψ + ‖w‖ * (A * (1 + |t|) ^ N)) := by gcongr
      _ = mφ t * (Bψ / (1 + |t|) ^ (N + 1) + ‖w‖ * A * ((1 + |t|) ^ N / (1 + |t|) ^ (N + 1))) := by
          ring
      _ ≤ mφ t * (Bψ + ‖w‖ * A * 1) := by
          have ha : Bψ / (1 + |t|) ^ (N + 1) ≤ Bψ := div_le_self hBψ (hpow1 t)
          have hb : (1 + |t|) ^ N / (1 + |t|) ^ (N + 1) ≤ 1 := (div_le_one hpos).2 hpowN
          gcongr
      _ = mφ t * C := by rw [hC, mul_one]

  have hfar_bd : ∀ (σ T : ℝ) (k : K), 0 ≤ σ → σ ≤ 1 → |q.im| + 1 ≤ |T| →
      ‖g ((σ : ℂ) + (T : ℂ) * I) k‖ ≤ Bφ * C / (1 + |T|) := by
    intro σ T k h0 h1 hT
    have hpos : 0 < (1 + |T|) ^ (N + 1) := by positivity
    have hpos1 : 0 < 1 + |T| := by positivity
    have hBφk : 0 ≤ Bφ := le_trans (hmφ0 T k) (hmφB T)
    have hφ1 : ‖φ ((σ : ℂ) + (T : ℂ) * I) k‖ ≤ Bφ / (1 + |T|) ^ (N + 1) := by
      rw [le_div_iff₀ hpos, mul_comm]; exact (hφb σ T k h0 h1).trans (hmφB T)
    have hM1 := hM_norm σ T k h0 h1 (hsep_far σ T hT)
    calc ‖g ((σ : ℂ) + (T : ℂ) * I) k‖
        ≤ ‖φ ((σ : ℂ) + (T : ℂ) * I) k‖ * (Bψ + ‖w‖ * ‖M ((σ : ℂ) - (T : ℂ) * I) k‖) :=
          hg_norm σ T k h0 h1
      _ ≤ (Bφ / (1 + |T|) ^ (N + 1)) * (Bψ + ‖w‖ * (A * (1 + |T|) ^ N)) := by gcongr
      _ = Bφ * (Bψ / (1 + |T|) ^ (N + 1)) + Bφ * (‖w‖ * A) * ((1 + |T|) ^ N / (1 + |T|) ^ (N + 1)) := by
          ring
      _ ≤ Bφ * (Bψ / (1 + |T|)) + Bφ * (‖w‖ * A) * (1 / (1 + |T|)) := by
          have ha : Bψ / (1 + |T|) ^ (N + 1) ≤ Bψ / (1 + |T|) := by
            refine div_le_div_of_nonneg_left hBψ hpos1 ?_
            calc (1 + |T|) = (1 + |T|) ^ 1 := (pow_one _).symm
              _ ≤ (1 + |T|) ^ (N + 1) := pow_le_pow_right₀ (by linarith [abs_nonneg T]) (by omega)
          have hne : (1 + |T|) ≠ 0 := hpos1.ne'
          have hb : (1 + |T|) ^ N / (1 + |T|) ^ (N + 1) = 1 / (1 + |T|) := by
            rw [pow_succ, eq_div_iff hne, div_mul_eq_mul_div, div_eq_iff (by positivity), one_mul]
          rw [hb]
          gcongr
      _ = Bφ * C / (1 + |T|) := by rw [hC]; ring

  have hjoint : ∀ σ : ℝ, σ = 0 ∨ σ = 1 →
      Continuous (Function.uncurry fun (t : ℝ) (k : K) => g ((σ : ℂ) + (t : ℂ) * I) k) := by
    intro σ hσ
    have h0 : 0 ≤ σ := by rcases hσ with rfl | rfl <;> norm_num
    have hσq : ∀ t : ℝ, ((σ : ℂ) - (t : ℂ) * I) ≠ q := by
      intro t h
      have := congrArg Complex.re h
      simp [hq] at this
      rcases hσ with rfl | rfl <;> norm_num at this
    have hmemU : ∀ t : ℝ, ((σ : ℂ) - (t : ℂ) * I) ∈ U := fun t => hUsub (by simpa using h0)

    have hpt1 : Continuous fun z : ℝ × K => (((σ : ℂ) + (z.1 : ℂ) * I), z.2) :=
      (continuous_const.add ((continuous_ofReal.comp continuous_fst).mul continuous_const)).prodMk
        continuous_snd
    have hpt2 : Continuous fun z : ℝ × K => ((((-σ : ℝ) : ℂ) + (z.1 : ℂ) * I), z.2) :=
      (continuous_const.add ((continuous_ofReal.comp continuous_fst).mul continuous_const)).prodMk
        continuous_snd
    have hpt3 : Continuous fun z : ℝ × K => (((σ : ℂ) - (z.1 : ℂ) * I), z.2) :=
      (continuous_const.sub ((continuous_ofReal.comp continuous_fst).mul continuous_const)).prodMk
        continuous_snd
    have hφz : Continuous fun z : ℝ × K => φ ((σ : ℂ) + (z.1 : ℂ) * I) z.2 := hφc.comp hpt1
    have hψz : Continuous fun z : ℝ × K => ψ (((-σ : ℝ) : ℂ) + (z.1 : ℂ) * I) z.2 := hψc.comp hpt2
    have hMregz : Continuous fun z : ℝ × K => Mreg ((σ : ℂ) - (z.1 : ℂ) * I) z.2 :=
      hMjc.comp_continuous hpt3 (fun z => ⟨hmemU z.1, Set.mem_univ _⟩)
    have hden : Continuous fun z : ℝ × K => ((σ : ℂ) - (z.1 : ℂ) * I) - q :=
      (continuous_const.sub ((continuous_ofReal.comp continuous_fst).mul continuous_const)).sub
        continuous_const
    have hMz : Continuous fun z : ℝ × K => M ((σ : ℂ) - (z.1 : ℂ) * I) z.2 := by
      have hmodel : Continuous fun z : ℝ × K => Mreg ((σ : ℂ) - (z.1 : ℂ) * I) z.2 / (((σ : ℂ) - (z.1 : ℂ) * I) - q) :=
        hMregz.div hden (fun z => sub_ne_zero.2 (hσq z.1))
      refine hmodel.congr ?_
      intro z
      exact (hMeq _ (hmemU z.1) (hσq z.1) z.2).symm
    have hmodel : Continuous fun z : ℝ × K =>
        φ ((σ : ℂ) + (z.1 : ℂ) * I) z.2 * conj (ψ (((-σ : ℝ) : ℂ) + (z.1 : ℂ) * I) z.2)
          + w * (φ ((σ : ℂ) + (z.1 : ℂ) * I) z.2 * conj (M ((σ : ℂ) - (z.1 : ℂ) * I) z.2)) :=
      (hφz.mul (continuous_conj.comp hψz)).add (continuous_const.mul (hφz.mul (continuous_conj.comp hMz)))
    refine hmodel.congr ?_
    intro z
    simp only [Function.uncurry, hg]
    rw [hneg_conj_pt, hconj_pt]
  have hcont_line : ∀ σ : ℝ, σ = 0 ∨ σ = 1 → ∀ k : K,
      Continuous fun t : ℝ => g ((σ : ℂ) + (t : ℂ) * I) k := fun σ hσ k =>
    (hjoint σ hσ).comp (continuous_id.prodMk continuous_const)

  have hprod_int : ∀ σ : ℝ, σ = 0 ∨ σ = 1 →
      Integrable (Function.uncurry fun (t : ℝ) (k : K) => g ((σ : ℂ) + (t : ℂ) * I) k)
        ((volume : Measure ℝ).prod μK) := by
    intro σ hσ
    refine Integrable.mono' ((hmφ.mul_const C).mul_prod (integrable_const (1 : ℝ)))
      (hjoint σ hσ).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, mul_one]
    exact hline_bd σ z.1 z.2 hσ
  have hline_int : ∀ σ : ℝ, σ = 0 ∨ σ = 1 → ∀ k : K,
      Integrable fun t : ℝ => g ((σ : ℂ) + (t : ℂ) * I) k := by
    intro σ hσ k
    exact Integrable.mono' (hmφ.mul_const C) (hcont_line σ hσ k).aestronglyMeasurable
      (ae_of_all _ fun t => hline_bd σ t k hσ)

  have hdecay : ∀ k : K, ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ |T| →
      ∀ σ : ℝ, (0 : ℝ) ≤ σ → σ ≤ (1 : ℝ) → ‖g ((σ : ℂ) + (T : ℂ) * I) k‖ ≤ ε := by
    intro k ε hε
    refine ⟨max (|q.im| + 1) (Bφ * C / ε), fun T hT σ h0 h1 => ?_⟩
    have hT1 : |q.im| + 1 ≤ |T| := le_trans (le_max_left _ _) hT
    have hT2 : Bφ * C / ε ≤ |T| := le_trans (le_max_right _ _) hT
    have hBφk : 0 ≤ Bφ := le_trans (hmφ0 T k) (hmφB T)
    have hpos1 : 0 < 1 + |T| := by positivity
    refine (hfar_bd σ T k h0 h1 hT1).trans ?_
    rw [div_le_iff₀ hpos1]
    rw [div_le_iff₀ hε] at hT2
    nlinarith [mul_nonneg hBφk hC0]
  have hU'sub01 : {s : ℂ | (0 : ℝ) ≤ s.re ∧ s.re ≤ (1 : ℝ)} ⊆ U' := hU'sub
  have hper : ∀ k : K,
      (∫ t : ℝ, g (((1 : ℝ) : ℂ) + (t : ℂ) * I) k) - (∫ t : ℝ, g (((0 : ℝ) : ℂ) + (t : ℂ) * I) k)
        = 2 * π * ρ k := by
    intro k
    exact AxisShift.integral_vertical_sub_integral_vertical_eq_two_pi_mul_residue (fun s => g s k) (ρ k) p
      0 1 (by rw [hp_re]; norm_num) (by rw [hp_re]; norm_num) U' hU'sub01 (R k) (hRdiff k)
      (fun s hs hsp => hGR k s hs hsp) (hline_int 0 (Or.inl rfl) k) (hline_int 1 (Or.inr rfl) k)
      (hdecay k)

  have hswap : ∀ σ : ℝ, σ = 0 ∨ σ = 1 →
      (∫ t : ℝ, (∫ k, g ((σ : ℂ) + (t : ℂ) * I) k ∂μK)) = ∫ k, (∫ t : ℝ, g ((σ : ℂ) + (t : ℂ) * I) k) ∂μK :=
    fun σ hσ => integral_integral_swap (hprod_int σ hσ)
  have hKint : ∀ σ : ℝ, σ = 0 ∨ σ = 1 →
      Integrable (fun k => ∫ t : ℝ, g ((σ : ℂ) + (t : ℂ) * I) k) μK :=
    fun σ hσ => (hprod_int σ hσ).integral_prod_right
  have hρint : Integrable (fun k => 2 * π * ρ k) μK := by
    have := (hKint 1 (Or.inr rfl)).sub (hKint 0 (Or.inl rfl))
    refine this.congr (ae_of_all _ fun k => ?_)
    simp only [Pi.sub_apply]
    exact hper k
  have hK1 : (∫ k, (∫ t : ℝ, g (((1 : ℝ) : ℂ) + (t : ℂ) * I) k) ∂μK)
      = (∫ k, (∫ t : ℝ, g (((0 : ℝ) : ℂ) + (t : ℂ) * I) k) ∂μK) + 2 * π * (w * ∫ k, Nf k p ∂μK) := by
    have hpt : ∀ k, (∫ t : ℝ, g (((1 : ℝ) : ℂ) + (t : ℂ) * I) k)
        = (∫ t : ℝ, g (((0 : ℝ) : ℂ) + (t : ℂ) * I) k) + 2 * π * ρ k := fun k =>
      sub_eq_iff_eq_add'.1 (hper k)
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add (hKint 0 (Or.inl rfl)) hρint]
    congr 1
    simp only [hρ]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

  have hKpieces : ∀ (σ t : ℝ), σ = 0 ∨ σ = 1 →
      Integrable (fun k => φ ((σ : ℂ) + (t : ℂ) * I) k * conj (ψ (((-σ : ℝ) : ℂ) + (t : ℂ) * I) k)) μK ∧
      Integrable (fun k => φ ((σ : ℂ) + (t : ℂ) * I) k * conj (M ((σ : ℂ) - (t : ℂ) * I) k)) μK := by
    intro σ t hσ
    have h0 : 0 ≤ σ := by rcases hσ with rfl | rfl <;> norm_num
    have h1 : σ ≤ 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hσq : ((σ : ℂ) - (t : ℂ) * I) ≠ q := by
      intro h
      have := congrArg Complex.re h
      simp [hq] at this
      rcases hσ with rfl | rfl <;> norm_num at this
    have hmemU : ((σ : ℂ) - (t : ℂ) * I) ∈ U := hUsub (by simpa using h0)
    have hφk : Continuous fun k : K => φ ((σ : ℂ) + (t : ℂ) * I) k :=
      hφc.comp (continuous_const.prodMk continuous_id)
    have hψk : Continuous fun k : K => ψ (((-σ : ℝ) : ℂ) + (t : ℂ) * I) k :=
      hψc.comp (continuous_const.prodMk continuous_id)
    have hMregk : Continuous fun k : K => Mreg ((σ : ℂ) - (t : ℂ) * I) k :=
      hMjc.comp_continuous (continuous_const.prodMk continuous_id) (fun k => ⟨hmemU, Set.mem_univ _⟩)
    have hMk : Continuous fun k : K => M ((σ : ℂ) - (t : ℂ) * I) k := by
      refine (hMregk.div_const (((σ : ℂ) - (t : ℂ) * I) - q)).congr ?_
      intro k
      exact (hMeq _ hmemU hσq k).symm
    have hφ1 : ∀ k, ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ ≤ mφ t := fun k => by
      have := hφb σ t k h0 h1
      have hmk := hmφ0 t k
      calc ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ = 1 * ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ := (one_mul _).symm
        _ ≤ (1 + |t|) ^ (N + 1) * ‖φ ((σ : ℂ) + (t : ℂ) * I) k‖ := by gcongr; exact hpow1 t
        _ ≤ mφ t := this
    constructor
    · refine Integrable.mono' (integrable_const (mφ t * Bψ))
        (hφk.mul (continuous_conj.comp hψk)).aestronglyMeasurable (ae_of_all _ fun k => ?_)
      rw [norm_mul, Complex.norm_conj]
      have := hψb (-σ) t k (by linarith) (by linarith)
      have hmk := hmφ0 t k
      gcongr
      exact hφ1 k
    · refine Integrable.mono' (integrable_const (mφ t * (A * (1 + |t|) ^ N)))
        (hφk.mul (continuous_conj.comp hMk)).aestronglyMeasurable (ae_of_all _ fun k => ?_)
      rw [norm_mul, Complex.norm_conj]
      have := hM_norm σ t k h0 h1 (hsep_line σ t hσ)
      have hmk := hmφ0 t k
      gcongr
      exact hφ1 k

  have hsplit : ∀ (σ t : ℝ), σ = 0 ∨ σ = 1 →
      ∫ k, g ((σ : ℂ) + (t : ℂ) * I) k ∂μK
        = (∫ k, φ ((σ : ℂ) + (t : ℂ) * I) k * conj (ψ (((-σ : ℝ) : ℂ) + (t : ℂ) * I) k) ∂μK)
          + w * ∫ k, φ ((σ : ℂ) + (t : ℂ) * I) k * conj (M ((σ : ℂ) - (t : ℂ) * I) k) ∂μK := by
    intro σ t hσ
    obtain ⟨hA, hB⟩ := hKpieces σ t hσ
    have hpt : ∀ k, g ((σ : ℂ) + (t : ℂ) * I) k
        = φ ((σ : ℂ) + (t : ℂ) * I) k * conj (ψ (((-σ : ℝ) : ℂ) + (t : ℂ) * I) k)
          + w * (φ ((σ : ℂ) + (t : ℂ) * I) k * conj (M ((σ : ℂ) - (t : ℂ) * I) k)) := by
      intro k
      simp only [hg]
      rw [hneg_conj_pt, hconj_pt]
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add hA (hB.const_mul w), MeasureTheory.integral_const_mul]

  have hL : ∫ t : ℝ, ((∫ k, φ (((1 : ℝ) : ℂ) + (t : ℂ) * I) k * conj (ψ (-((1 : ℝ) : ℂ) + (t : ℂ) * I) k) ∂μK)
        + w * ∫ k, φ (((1 : ℝ) : ℂ) + (t : ℂ) * I) k * conj (M (((1 : ℝ) : ℂ) - (t : ℂ) * I) k) ∂μK)
      = ∫ t : ℝ, (∫ k, g (((1 : ℝ) : ℂ) + (t : ℂ) * I) k ∂μK) := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    beta_reduce
    rw [hsplit 1 t (Or.inr rfl)]
    have : (((-1 : ℝ) : ℝ) : ℂ) = -((1 : ℝ) : ℂ) := by push_cast; ring
    simp only [this]

  have hAx : ∫ t : ℝ, ((∫ k, φ ((t : ℂ) * I) k * conj (ψ ((t : ℂ) * I) k) ∂μK)
          + w * ∫ k, φ ((t : ℂ) * I) k
              * conj (limUnder (𝓝[≠] (-((t : ℂ) * I))) (fun s => M s k)) ∂μK)
      = ∫ t : ℝ, (∫ k, g (((0 : ℝ) : ℂ) + (t : ℂ) * I) k ∂μK) := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    beta_reduce
    rw [hsplit 0 t (Or.inl rfl)]
    have e1 : (((0 : ℝ) : ℂ) + (t : ℂ) * I) = (t : ℂ) * I := by push_cast; ring
    have e2 : ((((-0 : ℝ) : ℝ) : ℂ) + (t : ℂ) * I) = (t : ℂ) * I := by push_cast; ring
    have e3 : (((0 : ℝ) : ℂ) - (t : ℂ) * I) = -((t : ℂ) * I) := by push_cast; ring
    have hlim : ∀ k, limUnder (𝓝[≠] (-((t : ℂ) * I))) (fun s => M s k) = M (-((t : ℂ) * I)) k := by
      intro k
      have hmem : (-((t : ℂ) * I)) ∈ U := hUsub (by simp)
      have hne : (-((t : ℂ) * I)) ≠ q := by
        intro h; have := congrArg Complex.re h; simp [hq] at this
      exact ((hMcont k _ hmem hne).tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
    simp only [e1, e2, e3, hlim]

  rw [hL, hAx, hswap 1 (Or.inr rfl), hswap 0 (Or.inl rfl), hK1]
  congr 2
  simp only [hNf, hconj_p]

end AxisPerIndex

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
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
      (ι : Type) [Fintype ι]
      (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 F) F (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 F) F (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 F) F (ν e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ι)
        (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)
      (r : ι → ι) (_hr : ∀ e, μ (r e) = ν e ∧ ν (r e) = μ e)
      (_hdist : ∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x)
      (φf ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite F (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth F (ψf e s))
      (_hψKu : ∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (φ ψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
      (_hψ : AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ)
      (_hφrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        φ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (Mc : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ (e : ι) (g : AdelicGL2 (𝓞 F) F), MeromorphicNFOn (fun s : ℂ => Mc e s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc e s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf e s) g)
      (pφ pψ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hpφ : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ pφ)
      (_hpψ : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ pψ)
      (_hpφc : ∀ ε > (0:ℝ),
        ∃ q ∈ AutomorphicForm.residualSpan (𝓞 F) F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).Z ξ,
          IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ q ∧
          eLpNorm (pφ - q) 2
            ((productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).μ.restrict
              (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).D) < ENNReal.ofReal ε)
      (_hpψc : ∀ ε > (0:ℝ),
        ∃ q ∈ AutomorphicForm.residualSpan (𝓞 F) F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).Z ξ,
          IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ q ∧
          eLpNorm (pψ - q) 2
            ((productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).μ.restrict
              (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).D) < ENNReal.ofReal ε)
      (_hpφo : ∀ h : AdelicGL2 (𝓞 F) F → ℂ,
        IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ h →
        h ∈ AutomorphicForm.residualSpan (𝓞 F) F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).Z ξ →
          ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).D,
              (AutomorphicForm.pseudoEisenstein F φ g - pφ g) * starRingEnd ℂ (h g)
            ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).μ = 0)
      (_hpψo : ∀ h : AdelicGL2 (𝓞 F) F → ℂ,
        IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ h →
        h ∈ AutomorphicForm.residualSpan (𝓞 F) F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).Z ξ →
          ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).D,
              (AutomorphicForm.pseudoEisenstein F ψ g - pψ g) * starRingEnd ℂ (h g)
            ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).μ = 0),
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
        AutomorphicForm.pseudoEisenstein F φ g * starRingEnd ℂ (AutomorphicForm.pseudoEisenstein F ψ g)
      ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ =
    (∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
        pφ g * starRingEnd ℂ (pψ g)
      ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ) +
    ((c.toReal * ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal * V.toReal ^ 2
        * Real.log (d₂ / d₁) / (16 * Real.pi) : ℝ) : ℂ) *
    ∑ e, ∫ t : ℝ,
      ((∫ k, φf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
            * starRingEnd ℂ (ψf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
          ∂(maximalCompactHaar F))
        + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
          ∫ k, φf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
            * starRingEnd ℂ (Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I)))
                (fun s : ℂ => Mc (r e) s (k : AdelicGL2 (𝓞 F) F)))
          ∂(maximalCompactHaar F)) := by
  intro α hα d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ c _hc0 _hcT _hc D _hDm _hDF V _hV0 _hVT _hV ξ ι _inst μ ν _hμ _hν _hμic _hνic
    _hμc _hμν r _hr _hdist φf ψf _hφf _hψf _hφjc _hψjc _hφhol _hψhol _hψK _hψsm _hψKu _hνc _hφdec _hψdec φ ψ _hφ _hψ
    _hφrep _hψrep Mc _hMc pφ pψ _hpφ _hpψ _hpφc _hpψc _hpφo _hpψo
  classical

  have hφdec0 : ∀ (e : ι) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t := by
    intro e σ₀ C hC
    obtain ⟨m, hm, hB, h⟩ := _hφdec e 0 σ₀ C hC
    exact ⟨m, hm, hB, fun σ' hσ' t g hg => by simpa using h σ' hσ' t g hg⟩
  have hψdec0 : ∀ (e : ι) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t := by
    intro e σ₀ C hC
    obtain ⟨m, hm, hB, h⟩ := _hψdec e 0 σ₀ C hC
    exact ⟨m, hm, hB, fun σ' hσ' t g hg => by simpa using h σ' hσ' t g hg⟩
  have h7a := AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_sum_integral_maximalCompact_pairing_slab F hα
    d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ c _hc0 _hcT _hc D _hDm _hDF V _hV0 _hVT _hV ξ ι μ ν _hμ _hν _hμic _hνic _hμc _hμν r _hr
    _hdist φf ψf _hφf _hψf _hφjc _hψjc _hφhol hφdec0 hψdec0 φ ψ _hφ _hψ _hφrep _hψrep 1 (by norm_num)

  set P : Finset ι := Finset.univ.filter (fun e => μ e = ν e) with hPdef
  have hP : ∀ e, e ∈ P ↔ μ e = ν e := fun e => by simp [hPdef]
  have h3 :=
    AutomorphicForm.setIntegral_residualProj_mul_conj_eq_sum_integral_maximalCompact_residue_pairing_slab
    F hα d₁ d₂ _hd₁ _hd Φ _hΦs _hΦ c _hc0 _hcT _hc D _hDm _hDF V _hV0 _hVT _hV ξ ι μ ν _hμ _hν _hμic _hνic _hμc _hμν r
    _hr _hdist φf ψf _hφf _hψf _hφjc _hψjc _hφhol _hψhol _hψK _hψsm _hψKu _hνc _hφdec _hψdec φ ψ _hφ _hψ _hφrep _hψrep
    Mc _hMc pφ pψ _hpφ _hpψ _hpφc _hpψc _hpφo _hpψo P hP

  have halign : ∀ e, (∃ t : ℝ, μ (r e) * (ν (r e))⁻¹ = NumberField.TateGlobal.normPowChar F t) → μ e = ν e := by
    rintro e ⟨t, ht⟩
    obtain ⟨hr1, hr2⟩ := _hr e
    have hone : ∀ x ∈ NumberField.TateGlobal.normOneIdeles F, ν e x = μ e x := by
      intro x hx
      have h := congrArg (fun χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ => χ x) ht
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, hr1, hr2] at h
      rw [NumberField.TateGlobal.normPowChar_eq_one_of_ideleNorm_eq_one t
        ((NumberField.TateGlobal.mem_normOneIdeles_iff x).1 hx)] at h
      exact mul_inv_eq_one.1 h
    have hre : r e = e := by
      by_contra hne
      obtain ⟨x, hx, h⟩ := _hdist (r e) e hne
      rw [hr1, hr2] at h
      rcases h with h | h
      · exact h (hone x hx)
      · exact h (hone x hx).symm
    have := hr1
    rw [hre] at this
    exact this
  have hself : ∀ e, μ e = ν e → μ (r e) * (ν (r e))⁻¹ = NumberField.TateGlobal.normPowChar F 0 := by
    intro e he
    obtain ⟨hr1, hr2⟩ := _hr e
    rw [NumberField.TateGlobal.normPowChar_zero, hr1, hr2, he]
    exact mul_inv_cancel (ν e)
  have hτ0 : ∀ τ : ℝ, NumberField.TateGlobal.normPowChar F τ = 1 → τ = 0 := by
    intro τ hτ
    by_contra hne
    have hτpos : 0 < |τ| := abs_pos.2 hne
    set M : ℝ := Real.exp (2 * Real.pi / |τ|) with hM
    have hM1 : 1 < M := by rw [hM]; exact Real.one_lt_exp_iff.2 (by positivity)
    have hnot : ∀ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z ∉ Set.Ioo 1 M := by
      intro z hz
      have hz0 : 0 < NumberField.TateGlobal.ideleNorm F z := NumberField.TateGlobal.ideleNorm_pos z
      have h1 : ((NumberField.TateGlobal.normPowChar F τ z : ℂˣ) : ℂ) = 1 := by rw [hτ]; simp
      rw [NumberField.TateGlobal.coe_normPowChar_apply,
        Complex.cpow_def_of_ne_zero (by exact_mod_cast hz0.ne'), Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      rw [(Complex.ofReal_log hz0.le).symm] at hn
      have him : Real.log (NumberField.TateGlobal.ideleNorm F z) * τ = (n : ℝ) * (2 * Real.pi) := by
        have h := congrArg Complex.im hn
        simpa [Complex.mul_im, Complex.mul_re] using h
      have hl0 : 0 < Real.log (NumberField.TateGlobal.ideleNorm F z) := Real.log_pos hz.1
      have hl1 : Real.log (NumberField.TateGlobal.ideleNorm F z) < 2 * Real.pi / |τ| := by
        have := Real.log_lt_log hz0 hz.2
        rwa [hM, Real.log_exp] at this
      have habs : |Real.log (NumberField.TateGlobal.ideleNorm F z) * τ| < 2 * Real.pi := by
        rw [abs_mul, abs_of_pos hl0]
        calc Real.log (NumberField.TateGlobal.ideleNorm F z) * |τ|
            < 2 * Real.pi / |τ| * |τ| := by gcongr
          _ = 2 * Real.pi := by field_simp
      have hprod_ne : Real.log (NumberField.TateGlobal.ideleNorm F z) * τ ≠ 0 := mul_ne_zero hl0.ne' hne
      rw [him] at habs hprod_ne
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hprod_ne (by simp)
      have hlt : |(n : ℝ)| < 1 := by
        have h2 : |(n : ℝ)| * (2 * Real.pi) < 1 * (2 * Real.pi) := by
          rw [one_mul]
          calc |(n : ℝ)| * (2 * Real.pi) = |(n : ℝ) * (2 * Real.pi)| := by
                rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
            _ < 2 * Real.pi := habs
        exact lt_of_mul_lt_mul_right h2 (by positivity)
      have : |n| < 1 := by exact_mod_cast hlt
      exact hn0 (Int.abs_lt_one_iff.1 this)
    have hVeq := _hV ((Set.Ioo 1 M).indicator fun _ => (1 : ℝ≥0∞)) (measurable_const.indicator measurableSet_Ioo)
    have hL : ∫⁻ z in D, (Set.Ioo 1 M).indicator (fun _ => (1 : ℝ≥0∞)) (NumberField.TateGlobal.ideleNorm F z)
        ∂(NumberField.Idele.idelicHaar F) = 0 := by
      refine (lintegral_congr fun z => ?_).trans lintegral_zero
      exact Set.indicator_of_notMem (hnot z) _
    have hR : ∫⁻ y in Set.Ioi (0 : ℝ), (Set.Ioo 1 M).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ ≠ 0 := by
      have hle : ∀ y : ℝ, (Set.Ioo 1 M).indicator (fun _ => ENNReal.ofReal M⁻¹) y
          ≤ (Set.Ioo 1 M).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal y⁻¹ := by
        intro y
        by_cases hy : y ∈ Set.Ioo 1 M
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [inv_le_inv₀ (by linarith [hy.1]) (by linarith [hy.1])]
          exact hy.2.le
        · simp [Set.indicator_of_notMem hy]
      intro h0
      have hmono := lintegral_mono (μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) hle
      have hsub : Set.Ioo (1 : ℝ) M ∩ Set.Ioi 0 = Set.Ioo 1 M :=
        Set.inter_eq_left.2 fun y hy => lt_trans zero_lt_one hy.1
      rw [h0, lintegral_indicator_const measurableSet_Ioo, Measure.restrict_apply measurableSet_Ioo, hsub,
        Real.volume_Ioo] at hmono
      have hM0 : 0 < M := lt_trans zero_lt_one hM1
      have hpos : 0 < ENNReal.ofReal M⁻¹ * ENNReal.ofReal (M - 1) :=
        ENNReal.mul_pos (ENNReal.ofReal_pos.2 (inv_pos.2 hM0)).ne' (ENNReal.ofReal_pos.2 (by linarith)).ne'
      exact absurd hmono (not_le.2 hpos)
    rw [hL] at hVeq
    exact (mul_ne_zero _hV0 hR) hVeq.symm

  have hcpt : IsCompact (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) := isCompact_adelicMaximalCompact F
  have key : ∀ e : ι,

      (∫ t : ℝ,
            ((∫ k, φf e (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
                  * starRingEnd ℂ (ψf e (-((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
                ∂(maximalCompactHaar F))
              + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
                ∫ k, φf e (((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
                  * starRingEnd ℂ (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
                      (ψf (r e) (((1 : ℝ) : ℂ) - (t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
                ∂(maximalCompactHaar F))) =
      (∫ t : ℝ,
            ((∫ k, φf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
                  * starRingEnd ℂ (ψf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
                ∂(maximalCompactHaar F))
              + (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
                ∫ k, φf e ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)
                  * starRingEnd ℂ (Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I)))
                      (fun s : ℂ => Mc (r e) s (k : AdelicGL2 (𝓞 F) F)))
                ∂(maximalCompactHaar F)))
      + 2 * (Real.pi : ℂ) * (if μ e = ν e then
          (((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹ *
            ∫ k, φf e (1 / 2 : ℂ) (k : AdelicGL2 (𝓞 F) F)
              * starRingEnd ℂ (Filter.limUnder (𝓝[≠] (1 / 2 : ℂ))
                  (fun s : ℂ => (s - (1 / 2 : ℂ)) * Mc (r e) s (k : AdelicGL2 (𝓞 F) F)))
            ∂(maximalCompactHaar F)
        else 0) := by
    intro e

    obtain ⟨A, hA0, N, hgrowth⟩ :=
      AutomorphicForm.exists_polynomial_bound_intertwining_continuation_of_isInducedSection F hα (μ (r e)) (ν (r e))
        (_hμ (r e)) (_hν (r e)) (_hμic (r e)) (_hνic (r e)) (ψf (r e)) (_hψf (r e)) (_hψK (r e)) (_hψsm (r e))
        (_hψjc (r e)) (_hψhol (r e)) (_hμc (r e)) (_hνc (r e)) (_hψKu (r e)) (Mc (r e)) (_hMc (r e)) 1 one_pos
        (1 / 2) (by norm_num)

    obtain ⟨mψ', -, ⟨B', hB'⟩, hψ'⟩ := _hψdec (r e) 0 1 _ hcpt
    obtain ⟨mφ, hmφ, ⟨Bφ, hBφ⟩, hφb'⟩ := _hφdec e (N + 1) 1 _ hcpt
    obtain ⟨mψ, -, ⟨Bψ', hBψ'⟩, hψb'⟩ := _hψdec e 0 1 _ hcpt
    have hsup : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
        (⨆ k' : ↥(adelicMaximalCompact F), ‖ψf (r e) s (k' : AdelicGL2 (𝓞 F) F)‖) ≤ max B' 0 := by
      intro s h0 h1
      haveI : Nonempty ↥(adelicMaximalCompact F) := ⟨⟨1, (adelicMaximalCompact F).one_mem⟩⟩
      refine ciSup_le fun k' => ?_
      have h := hψ' s.re (abs_le.2 ⟨by linarith, h1⟩) s.im (k' : AdelicGL2 (𝓞 F) F) k'.2
      rw [pow_zero, one_mul, Complex.re_add_im] at h
      exact h.trans ((hB' _).trans (le_max_left _ _))
    have hMg : ∀ (s : ℂ) (k : ↥(adelicMaximalCompact F)), 0 ≤ s.re → s.re ≤ 1 →
        (∀ τ : ℝ, μ (r e) * (ν (r e))⁻¹ = NumberField.TateGlobal.normPowChar F τ →
          (1 / 2 : ℝ) ≤ ‖s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)‖) →
        ‖Mc (r e) s (k : AdelicGL2 (𝓞 F) F)‖ ≤ A * max B' 0 * (1 + |s.im|) ^ N := by
      intro s k h0 h1 hsep
      have h := hgrowth s h0 h1 hsep (k : AdelicGL2 (𝓞 F) F) k.2
      refine h.trans ?_
      have := hsup s h0 h1
      calc A * (1 + |s.im|) ^ N * (⨆ k' : ↥(adelicMaximalCompact F), ‖ψf (r e) s (k' : AdelicGL2 (𝓞 F) F)‖)
          ≤ A * (1 + |s.im|) ^ N * max B' 0 := by gcongr
        _ = A * max B' 0 * (1 + |s.im|) ^ N := by ring
    have hφb : ∀ (σ t : ℝ) (k : ↥(adelicMaximalCompact F)), 0 ≤ σ → σ ≤ 1 →
        (1 + |t|) ^ (N + 1) * ‖φf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ≤ mφ t :=
      fun σ t k h0 h1 => hφb' σ (abs_le.2 ⟨by linarith, h1⟩) t (k : AdelicGL2 (𝓞 F) F) k.2
    have hψb : ∀ (σ t : ℝ) (k : ↥(adelicMaximalCompact F)), -1 ≤ σ → σ ≤ 0 →
        ‖ψf e ((σ : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ≤ max Bψ' 0 := by
      intro σ t k h0 h1
      have h := hψb' σ (abs_le.2 ⟨h0, by linarith⟩) t (k : AdelicGL2 (𝓞 F) F) k.2
      rw [pow_zero, one_mul] at h
      exact h.trans ((hBψ' t).trans (le_max_left _ _))

    have hφc : Continuous (Function.uncurry fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) =>
        φf e s (k : AdelicGL2 (𝓞 F) F)) :=
      (_hφjc e).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have hψc : Continuous (Function.uncurry fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) =>
        ψf e s (k : AdelicGL2 (𝓞 F) F)) :=
      (_hψjc e).comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

    have hW : ∀ (t : ℝ) (k : ↥(adelicMaximalCompact F)),
        weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F)
            (ψf (r e) (((1 : ℝ) : ℂ) - (t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F)
          = Mc (r e) (((1 : ℝ) : ℂ) - (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) := fun t k =>
      ((_hMc (r e) (k : AdelicGL2 (𝓞 F) F)).2 (((1 : ℝ) : ℂ) - (t : ℂ) * Complex.I) (by norm_num)).symm
    simp_rw [hW]
    by_cases he : μ e = ν e
    ·
      have hres := hself e he
      obtain ⟨U, hUo, hUsub, Mreg, hMa, hMjc, hMM⟩ :=
        (AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection
          F hα (μ (r e)) (ν (r e)) (_hμ (r e)) (_hν (r e)) (_hμic (r e)) (_hνic (r e)) (ψf (r e)) (_hψf (r e))
          (_hψK (r e)) (_hψsm (r e)) (_hψjc (r e)) (_hψhol (r e)) (_hμc (r e)) (_hνc (r e)) (_hψKu (r e)) (Mc (r e))
          (_hMc (r e))).1 0 hres
      have hpt : ((1 / 2 : ℂ) - (((0 : ℝ) / 2 : ℝ) : ℂ) * Complex.I) = (1 / 2 : ℂ) := by push_cast; ring
      rw [hpt] at hMM
      have hτuniq : ∀ τ : ℝ, μ (r e) * (ν (r e))⁻¹ = NumberField.TateGlobal.normPowChar F τ → τ = 0 := by
        intro τ hτ
        refine hτ0 τ ?_
        rw [← hτ, hres, NumberField.TateGlobal.normPowChar_zero]
      have hg := AxisPerIndex.integral_integral_shift (maximalCompactHaar F)
        (fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) => φf e s (k : AdelicGL2 (𝓞 F) F))
        (fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) => ψf e s (k : AdelicGL2 (𝓞 F) F))
        (fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) => Mc (r e) s (k : AdelicGL2 (𝓞 F) F))
        (fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) => Mreg s (k : AdelicGL2 (𝓞 F) F))
        ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹) (1 / 2 : ℂ) (by norm_num) U hUo hUsub hφc hψc
        (fun k => _hφhol e (k : AdelicGL2 (𝓞 F) F)) (fun k => _hψhol e (k : AdelicGL2 (𝓞 F) F))
        (fun k => (hMa (k : AdelicGL2 (𝓞 F) F)).differentiableOn)
        (hMjc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
          (fun p hp => ⟨hp.1, Set.mem_univ _⟩))
        (fun s hs hsq k => hMM s hs hsq (k : AdelicGL2 (𝓞 F) F))
        N (A * max B' 0) (max Bψ' 0) (1 / 2) one_half_pos le_rfl (by positivity) (le_max_right _ _)
        mφ hmφ Bφ hBφ hφb hψb
        (fun s k h0 h1 hsep => hMg s k h0 h1 (fun τ hτ => by
          have := hτuniq τ hτ; subst this; rw [hpt]; exact hsep))
      beta_reduce at hg
      refine hg.trans ?_
      rw [if_pos he]

      have hconj : (starRingEnd ℂ) (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
        rw [map_div₀, map_one, map_ofNat]
      have hlim : ∀ k : ↥(adelicMaximalCompact F),
          Filter.limUnder (𝓝[≠] (1 / 2 : ℂ)) (fun s : ℂ => (s - (1 / 2 : ℂ)) * Mc (r e) s (k : AdelicGL2 (𝓞 F) F))
            = Mreg (1 / 2 : ℂ) (k : AdelicGL2 (𝓞 F) F) := by
        intro k
        refine Filter.Tendsto.limUnder_eq ?_
        have hcont : ContinuousAt (fun s => Mreg s (k : AdelicGL2 (𝓞 F) F)) (1 / 2 : ℂ) :=
          (hMa (k : AdelicGL2 (𝓞 F) F) (1 / 2 : ℂ) (hUsub (by norm_num))).continuousAt
        refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        have hU12 : U ∈ 𝓝[≠] (1 / 2 : ℂ) := mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds (hUsub (by norm_num)))
        filter_upwards [hU12, self_mem_nhdsWithin] with s hsU hs12
        exact hMM s hsU hs12 (k : AdelicGL2 (𝓞 F) F)
      simp_rw [hconj, hlim]
    ·
      have hnon : ∀ τ : ℝ, μ (r e) * (ν (r e))⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ :=
        fun τ hτ => he (halign e ⟨τ, hτ⟩)
      obtain ⟨U, hUo, hUsub, hMa, hMjc⟩ :=
        (AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection
          F hα (μ (r e)) (ν (r e)) (_hμ (r e)) (_hν (r e)) (_hμic (r e)) (_hνic (r e)) (ψf (r e)) (_hψf (r e))
          (_hψK (r e)) (_hψsm (r e)) (_hψjc (r e)) (_hψhol (r e)) (_hμc (r e)) (_hνc (r e)) (_hψKu (r e)) (Mc (r e))
          (_hMc (r e))).2 hnon
      have hg := AxisPerIndex.integral_integral_shift (maximalCompactHaar F)
        (fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) => φf e s (k : AdelicGL2 (𝓞 F) F))
        (fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) => ψf e s (k : AdelicGL2 (𝓞 F) F))
        (fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) => Mc (r e) s (k : AdelicGL2 (𝓞 F) F))
        (fun (s : ℂ) (k : ↥(adelicMaximalCompact F)) => (s - (1 / 2 : ℂ)) * Mc (r e) s (k : AdelicGL2 (𝓞 F) F))
        ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)⁻¹) (1 / 2 : ℂ) (by norm_num) U hUo hUsub hφc hψc
        (fun k => _hφhol e (k : AdelicGL2 (𝓞 F) F)) (fun k => _hψhol e (k : AdelicGL2 (𝓞 F) F))
        (fun k => (differentiableOn_id.sub (differentiableOn_const _)).mul
          (hMa (k : AdelicGL2 (𝓞 F) F)).differentiableOn)
        (((continuous_fst.sub continuous_const).continuousOn).mul
          (hMjc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
            (fun p hp => ⟨hp.1, Set.mem_univ _⟩)))
        (fun s _ _ k => rfl)
        N (A * max B' 0) (max Bψ' 0) (1 / 2) one_half_pos le_rfl (by positivity) (le_max_right _ _)
        mφ hmφ Bφ hBφ hφb hψb
        (fun s k h0 h1 _ => hMg s k h0 h1 (fun τ hτ => absurd hτ (hnon τ)))
      beta_reduce at hg
      refine hg.trans ?_
      rw [if_neg he]
      simp

  have hfront : ((c.toReal * ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal * V.toReal ^ 2
        * Real.log (d₂ / d₁) / (16 * Real.pi) : ℝ) : ℂ) * (2 * (Real.pi : ℂ))
      = ((c.toReal * ((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal * V.toReal ^ 2
        * Real.log (d₂ / d₁) / 8 : ℝ) : ℂ) := by
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring
  rw [h7a]
  simp only [key]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter, ← hPdef, h3, ← hfront]
  ring

end

end S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab (solution)
