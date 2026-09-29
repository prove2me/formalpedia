-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e5696ab3-0c65-5ac0-8ca2-1cf78270f6c9

import Mathlib
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_and_sub_eq_cross_sub_and_sub_eq_zero_two_pairs_slab
import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_cross_and_eq_zero_two_pairs_slab_of_re_lt_re
import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_twoTerm_slab_of_exists_ideleNorm_eq_one_ne
import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab
import Theorems.Thm_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family
import Theorems.Thm_AutomorphicForm_analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family
import Theorems.Thm_Complex_differentiableOn_integral_mul_of_memLp_two_of_tendsto_eLpNorm_of_forall_differentiableOn
import Theorems.Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne
p2m_attr_erase "instance" "FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions"
p2m_attr_erase "instance" "instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS"
p2m_attr_erase "simp" "AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv"
p2m_attr_erase "simp" "LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.TateLocal.conductorExponentAt_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open NumberField.AdelicHeight
open IsDedekindDomain AutomorphicForm Filter Topology Set
open scoped ComplexConjugate NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace R4TwoPairAxis

theorem conj_mem_half {u : ℂ} (hu : (1 : ℝ) / 2 < u.re) : (1 : ℝ) / 2 < (conj u).re := by
  simpa using hu

theorem sesqui_identity_lt {O₁ O₂ : Set ℂ} (h₁ : IsOpen O₁) (h₁c : IsPreconnected O₁)
    (h₁h : {s : ℂ | 1 / 2 < s.re} ⊆ O₁)
    (h₂ : IsOpen O₂) (h₂c : IsPreconnected O₂) (h₂h : {s : ℂ | 1 / 2 < s.re} ⊆ O₂)
    (K : ℂ → ℂ → ℂ)
    (hK1 : ∀ u ∈ O₂, DifferentiableOn ℂ (fun s => K s u) O₁)
    (hK2 : ∀ s ∈ O₁, DifferentiableOn ℂ (fun u => K s u) O₂)
    (hzero : ∀ s u : ℂ, 1 / 2 < s.re → s.re < u.re → K s u = 0) :
    ∀ s ∈ O₁, ∀ u ∈ O₂, K s u = 0 := by
  have hHopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1mem : (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by simp; norm_num

  have step1 : ∀ u : ℂ, 1 / 2 < u.re → ∀ s ∈ O₁, K s u = 0 := by
    intro u hu s hs
    have han : AnalyticOnNhd ℂ (fun s => K s u) O₁ := (hK1 u (h₂h hu)).analyticOnNhd h₁
    set z₀ : ℂ := (((1 / 2 + u.re) / 2 : ℝ) : ℂ) with hz₀
    have hz₀re : z₀.re = (1 / 2 + u.re) / 2 := by rw [hz₀, Complex.ofReal_re]
    have hzmem : z₀ ∈ {s : ℂ | 1 / 2 < s.re} := by
      show 1 / 2 < z₀.re
      rw [hz₀re]; linarith
    have hVopen : IsOpen ({s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.re < u.re}) :=
      hHopen.inter (isOpen_lt Complex.continuous_re continuous_const)
    have hzV : z₀ ∈ ({s : ℂ | 1 / 2 < s.re} ∩ {s : ℂ | s.re < u.re}) := by
      refine ⟨hzmem, ?_⟩
      show z₀.re < u.re
      rw [hz₀re]; linarith
    have hev : (fun s => K s u) =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [hVopen.mem_nhds hzV] with z hz
      exact hzero z u hz.1 hz.2
    exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero h₁c (h₁h hzmem) hev hs
  intro s hs u hu
  have han : AnalyticOnNhd ℂ (fun u => K s u) O₂ := (hK2 s hs).analyticOnNhd h₂
  have hev : (fun u => K s u) =ᶠ[𝓝 (1 : ℂ)] 0 := by
    filter_upwards [hHopen.mem_nhds h1mem] with z hz
    exact step1 z hz s hs
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero h₂c (h₂h h1mem) hev hu

theorem differentiableOn_conj_conj {V : Set ℂ} (hV : IsOpen V) {J : ℂ → ℂ} (hJ : DifferentiableOn ℂ J V) :
    DifferentiableOn ℂ (fun u => conj (J (conj u))) {u : ℂ | conj u ∈ V} := by
  intro u hu
  apply DifferentiableAt.differentiableWithinAt
  have h := (hJ.differentiableAt (hV.mem_nhds hu)).conj_conj
  rw [Complex.conj_conj] at h
  exact h

theorem isOpen_conj_preimage {V : Set ℂ} (hV : IsOpen V) : IsOpen {u : ℂ | conj u ∈ V} :=
  hV.preimage Complex.continuous_conj

theorem isPreconnected_conj_preimage {V : Set ℂ} (hV : IsPreconnected V) : IsPreconnected {u : ℂ | conj u ∈ V} := by
  have : {u : ℂ | conj u ∈ V} = conj '' V := by
    ext u
    constructor
    · intro hu
      exact ⟨conj u, hu, Complex.conj_conj u⟩
    · rintro ⟨w, hw, rfl⟩
      show conj (conj w) ∈ V
      rw [Complex.conj_conj]
      exact hw
  rw [this]
  exact hV.image _ Complex.continuous_conj.continuousOn

theorem kappa_eq_zero (c c' x P Q κ : ℂ) (R₁ : ℝ) (hE1 : ‖Complex.exp x‖ ≠ 1)
    (h : ∀ n : ℕ, n ≤ 2 →
      (c' - c) * (P * Complex.exp (((R₁ + n : ℝ) : ℂ) * x) / x - Q * Complex.exp (-(((R₁ + n : ℝ) : ℂ) * x)) / x) = κ) :
    κ = 0 := by
  by_cases hcc : c' = c
  · have := h 0 (by norm_num)
    rw [hcc, sub_self, zero_mul] at this
    exact this.symm
  · have hd : c' - c ≠ 0 := sub_ne_zero.mpr hcc
    set E : ℂ := Complex.exp x with hE
    have hE0 : E ≠ 0 := by rw [hE]; exact Complex.exp_ne_zero x
    have hEne1 : E ≠ 1 := fun h1 => hE1 (by rw [h1, norm_one])
    have hE2ne1 : E ^ 2 ≠ 1 := by
      intro h2
      apply hE1
      have : ‖E‖ ^ 2 = 1 := by rw [← norm_pow, h2, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg E) two_ne_zero).mp this
    set a : ℂ := P * Complex.exp ((R₁ : ℂ) * x) / x with ha
    set b : ℂ := Q * Complex.exp (-((R₁ : ℂ) * x)) / x with hb
    clear_value E a b
    have hexp : ∀ n : ℕ, Complex.exp (((R₁ + n : ℝ) : ℂ) * x) = Complex.exp ((R₁ : ℂ) * x) * E ^ n := by
      intro n
      rw [hE, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hexp' : ∀ n : ℕ, Complex.exp (-(((R₁ + n : ℝ) : ℂ) * x)) = Complex.exp (-((R₁ : ℂ) * x)) * (E ^ n)⁻¹ := by
      intro n
      rw [Complex.exp_neg, hexp n, mul_inv, Complex.exp_neg]
    have hB : ∀ n : ℕ, n ≤ 2 → (c' - c) * (a * E ^ n - b * (E ^ n)⁻¹) = κ := by
      intro n hn
      have := h n hn
      rw [hexp n, hexp' n] at this
      rw [← this, ha, hb]
      ring
    have h0 := hB 0 (by norm_num)
    have h1 := hB 1 (by norm_num)
    have h2 := hB 2 (by norm_num)
    simp only [pow_zero, inv_one, mul_one, pow_one] at h0 h1
    have e1 : a * E - b * E⁻¹ = a - b := mul_left_cancel₀ hd (h1.trans h0.symm)
    have e2 : a * E ^ 2 - b * (E ^ 2)⁻¹ = a - b := mul_left_cancel₀ hd (h2.trans h0.symm)
    have f1 : a * E = -b := by
      have : (a * E + b) * (E - 1) = 0 := by
        field_simp at e1
        linear_combination e1
      rcases mul_eq_zero.mp this with h | h
      · linear_combination h
      · exact absurd (sub_eq_zero.mp h) hEne1
    have f2 : a * E ^ 2 = -b := by
      have : (a * E ^ 2 + b) * (E ^ 2 - 1) = 0 := by
        field_simp at e2
        linear_combination e2
      rcases mul_eq_zero.mp this with h | h
      · linear_combination h
      · exact absurd (sub_eq_zero.mp h) hE2ne1
    have ha0 : a = 0 := by
      have : a * E * (E - 1) = 0 := by linear_combination f2 - f1
      rcases mul_eq_zero.mp this with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hE0
      · exact absurd (sub_eq_zero.mp h) hEne1
    have hb0 : b = 0 := by
      have hf := f1
      rw [ha0, zero_mul] at hf
      linear_combination hf
    rw [← h0, ha0, hb0]
    ring

theorem norm_exp_ofReal_mul (h : ℝ) (w : ℂ) : ‖Complex.exp ((h : ℂ) * w)‖ = Real.exp (h * w.re) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem exists_step (Y : ℂ) (hY : Y ≠ 0) :
    ∃ h : ℝ, 0 < h ∧ Complex.exp ((h : ℂ) * Y) ≠ 1 ∧ Complex.exp ((h : ℂ) * Y) ^ 2 ≠ 1 := by
  by_cases hre : Y.re = 0
  · have hy : Y.im ≠ 0 := by
      intro him
      exact hY (Complex.ext (by simpa using hre) (by simpa using him))
    set y : ℝ := Y.im with hydef
    have hY' : Y = (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre, hydef]
    have hne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
    clear_value y
    subst hY'
    have hI1 : (Complex.I : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this
    have hIsq : (Complex.I : ℂ) ^ 2 ≠ 1 := by rw [Complex.I_sq]; norm_num
    have hnI1 : (-Complex.I : ℂ) ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this
    have hnIsq : (-Complex.I : ℂ) ^ 2 ≠ 1 := by rw [neg_sq, Complex.I_sq]; norm_num
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · refine ⟨-(Real.pi / (2 * y)), ?_, ?_⟩
      · have : Real.pi / (2 * y) < 0 := div_neg_of_pos_of_neg Real.pi_pos (by linarith)
        linarith
      · have harg : (((-(Real.pi / (2 * y)) : ℝ) : ℂ)) * ((y : ℂ) * Complex.I) = -(Real.pi / 2 * Complex.I) := by
          push_cast
          field_simp
        rw [harg, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
        exact ⟨hnI1, hnIsq⟩
    · refine ⟨Real.pi / (2 * y), by positivity, ?_⟩
      have harg : (((Real.pi / (2 * y) : ℝ) : ℂ)) * ((y : ℂ) * Complex.I) = Real.pi / 2 * Complex.I := by
        push_cast
        field_simp
      rw [harg, Complex.exp_pi_div_two_mul_I]
      exact ⟨hI1, hIsq⟩
  · refine ⟨1, one_pos, ?_, ?_⟩
    · intro h1
      have h2 : ‖Complex.exp (((1 : ℝ) : ℂ) * Y)‖ = ‖(1 : ℂ)‖ := by rw [h1]
      rw [norm_exp_ofReal_mul, one_mul, norm_one, Real.exp_eq_one_iff] at h2
      exact hre h2
    · intro h1
      have h2 : ‖Complex.exp (((1 : ℝ) : ℂ) * Y) ^ 2‖ = ‖(1 : ℂ)‖ := by rw [h1]
      rw [norm_pow, norm_exp_ofReal_mul, one_mul, norm_one, ← Real.exp_nat_mul, Real.exp_eq_one_iff] at h2
      exact hre (by simpa using h2)

theorem kappa4_eq_zero (d κ a b a' b' X Y : ℂ) (R₁ : ℝ) (hXY : |Y.re| < X.re) (hY : Y ≠ 0)
    (h : ∀ ρ : ℝ, R₁ ≤ ρ →
      d * (a * Complex.exp ((ρ : ℂ) * X) + b * Complex.exp (-((ρ : ℂ) * X))
        + a' * Complex.exp ((ρ : ℂ) * Y) + b' * Complex.exp (-((ρ : ℂ) * Y))) = κ) :
    κ = 0 := by
  obtain ⟨h₀, hh₀, hB1, hB2⟩ := exists_step Y hY
  set A : ℂ := Complex.exp ((h₀ : ℂ) * X) with hA
  set B : ℂ := Complex.exp ((h₀ : ℂ) * Y) with hB
  have hXre : 0 < X.re := lt_of_le_of_lt (abs_nonneg _) hXY
  have hA0 : A ≠ 0 := Complex.exp_ne_zero _
  have hB0 : B ≠ 0 := Complex.exp_ne_zero _

  have nA : ‖A‖ = Real.exp (h₀ * X.re) := norm_exp_ofReal_mul h₀ X
  have nB : ‖B‖ = Real.exp (h₀ * Y.re) := norm_exp_ofReal_mul h₀ Y
  have nAi : ‖A⁻¹‖ = Real.exp (-(h₀ * X.re)) := by rw [norm_inv, nA, Real.exp_neg]
  have nBi : ‖B⁻¹‖ = Real.exp (-(h₀ * Y.re)) := by rw [norm_inv, nB, Real.exp_neg]
  have hlt1 : h₀ * Y.re < h₀ * X.re := mul_lt_mul_of_pos_left (lt_of_le_of_lt (le_abs_self _) hXY) hh₀
  have hlt2 : -(h₀ * X.re) < h₀ * Y.re := by
    have := neg_abs_le Y.re
    nlinarith
  have hlt3 : -(h₀ * Y.re) < h₀ * X.re := by
    have := neg_le_abs Y.re
    nlinarith
  have hlt4 : -(h₀ * X.re) < -(h₀ * Y.re) := by linarith
  have hpos : 0 < h₀ * X.re := mul_pos hh₀ hXre

  have s01 : A ≠ A⁻¹ := fun e => by
    have := congrArg norm e; rw [nA, nAi] at this
    have := Real.exp_injective this; linarith
  have s02 : A ≠ B := fun e => by
    have := congrArg norm e; rw [nA, nB] at this
    have := Real.exp_injective this; linarith
  have s03 : A ≠ B⁻¹ := fun e => by
    have := congrArg norm e; rw [nA, nBi] at this
    have := Real.exp_injective this; linarith
  have s04 : A ≠ 1 := fun e => by
    have := congrArg norm e; rw [nA, norm_one, Real.exp_eq_one_iff] at this
    linarith
  have s12 : A⁻¹ ≠ B := fun e => by
    have := congrArg norm e; rw [nAi, nB] at this
    have := Real.exp_injective this; linarith
  have s13 : A⁻¹ ≠ B⁻¹ := fun e => by
    have := congrArg norm e; rw [nAi, nBi] at this
    have := Real.exp_injective this; linarith
  have s14 : A⁻¹ ≠ 1 := fun e => by
    have := congrArg norm e; rw [nAi, norm_one, Real.exp_eq_one_iff] at this
    linarith
  have s23 : B ≠ B⁻¹ := fun e => by
    apply hB2
    have : B * B = B * B⁻¹ := by rw [← e]
    rw [mul_inv_cancel₀ hB0] at this
    rw [sq, this]
  have s24 : B ≠ 1 := hB1

  set z : Fin 5 → ℂ := ![A, A⁻¹, B, B⁻¹, 1] with hz
  set w : Fin 5 → ℂ := ![d * a * Complex.exp ((R₁ : ℂ) * X), d * b * Complex.exp (-((R₁ : ℂ) * X)),
    d * a' * Complex.exp ((R₁ : ℂ) * Y), d * b' * Complex.exp (-((R₁ : ℂ) * Y)), -κ] with hw
  have hzinj : Function.Injective z := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hz] at hij ⊢ <;>
      first
      | exact absurd hij s01 | exact absurd hij.symm s01
      | exact absurd hij s02 | exact absurd hij.symm s02
      | exact absurd hij s03 | exact absurd hij.symm s03
      | exact absurd hij s04 | exact absurd hij.symm s04
      | exact absurd hij s12 | exact absurd hij.symm s12
      | exact absurd hij s13 | exact absurd hij.symm s13
      | exact absurd hij s14 | exact absurd hij.symm s14
      | exact absurd hij s23 | exact absurd hij.symm s23
      | exact absurd hij s24 | exact absurd hij.symm s24

  have hexpX : ∀ n : ℕ, Complex.exp (((R₁ + n * h₀ : ℝ) : ℂ) * X) = Complex.exp ((R₁ : ℂ) * X) * A ^ n := by
    intro n
    rw [hA, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hexpX' : ∀ n : ℕ, Complex.exp (-(((R₁ + n * h₀ : ℝ) : ℂ) * X))
      = Complex.exp (-((R₁ : ℂ) * X)) * (A⁻¹) ^ n := by
    intro n
    rw [inv_pow, Complex.exp_neg, hexpX n, mul_inv, Complex.exp_neg]
  have hexpY : ∀ n : ℕ, Complex.exp (((R₁ + n * h₀ : ℝ) : ℂ) * Y) = Complex.exp ((R₁ : ℂ) * Y) * B ^ n := by
    intro n
    rw [hB, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hexpY' : ∀ n : ℕ, Complex.exp (-(((R₁ + n * h₀ : ℝ) : ℂ) * Y))
      = Complex.exp (-((R₁ : ℂ) * Y)) * (B⁻¹) ^ n := by
    intro n
    rw [inv_pow, Complex.exp_neg, hexpY n, mul_inv, Complex.exp_neg]
  have hsum : ∀ i : Fin 5, (∑ j : Fin 5, w j * z j ^ (i : ℕ)) = 0 := by
    intro i
    have hρ : R₁ ≤ R₁ + (i : ℕ) * h₀ := by
      have : (0 : ℝ) ≤ (i : ℕ) * h₀ := by positivity
      linarith
    have := h (R₁ + (i : ℕ) * h₀) hρ
    rw [hexpX, hexpX', hexpY, hexpY'] at this
    simp only [hw, hz, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four, one_pow]
    linear_combination this
  have hw0 : w = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hzinj hsum
  have := congrFun hw0 4
  simp [hw] at this
  exact this

section KPair

variable (F : Type) [Field F] [NumberField F]

theorem differentiableOn_integral_maximalCompact {U : Set ℂ} (hU : IsOpen U)
    (Φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hΦc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Φ p.1 p.2) (U ×ˢ Set.univ))
    (hΦd : ∀ g : AdelicGL2 (𝓞 F) F, DifferentiableOn ℂ (fun s => Φ s g) U) :
    DifferentiableOn ℂ (fun s => ∫ k, Φ s (k : AdelicGL2 (𝓞 F) F) ∂(maximalCompactHaar F)) U := by
  have h := Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
    (Y := ↥(adelicMaximalCompact F)) (maximalCompactHaar F) hU (S := Set.univ) isCompact_univ
    (fun s k => Φ s (k : AdelicGL2 (𝓞 F) F)) ?_ (fun _ _ k hk => absurd (Set.mem_univ k) hk)
    (fun k => hΦd (k : AdelicGL2 (𝓞 F) F))
  · exact h
  · have hcont : Continuous (fun p : ℂ × ↥(adelicMaximalCompact F) => (p.1, (p.2 : AdelicGL2 (𝓞 F) F))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    refine (hΦc.comp hcont.continuousOn ?_)
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩

theorem differentiableOn_integral_maximalCompact_conj {U : Set ℂ} (hU : IsOpen U)
    (A : AdelicGL2 (𝓞 F) F → ℂ) (hA : Continuous A)
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hΨc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ψ p.1 p.2) (U ×ˢ Set.univ))
    (hΨd : ∀ g : AdelicGL2 (𝓞 F) F, DifferentiableOn ℂ (fun s => Ψ s g) U) :
    DifferentiableOn ℂ (fun u => ∫ k, A (k : AdelicGL2 (𝓞 F) F) * conj (Ψ (conj u) (k : AdelicGL2 (𝓞 F) F))
      ∂(maximalCompactHaar F)) {u : ℂ | conj u ∈ U} := by
  set J : ℂ → ℂ := fun w => ∫ k, Ψ w (k : AdelicGL2 (𝓞 F) F) * conj (A (k : AdelicGL2 (𝓞 F) F))
    ∂(maximalCompactHaar F) with hJ
  have hJd : DifferentiableOn ℂ J U := by
    refine differentiableOn_integral_maximalCompact F hU (fun w g => Ψ w g * conj (A g)) ?_ ?_
    · exact hΨc.mul (Complex.continuous_conj.comp (hA.comp continuous_snd)).continuousOn
    · intro g
      exact (hΨd g).mul_const _
  have h := differentiableOn_conj_conj hU hJd
  refine h.congr fun u _ => ?_
  simp only [hJ]
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

end KPair

section Main

variable (F : Type) [Field F] [NumberField F]

theorem continuous_section {φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)) (s : ℂ) : Continuous (φ s) :=
  hφ.comp (continuous_const.prodMk continuous_id)

theorem continuous_section_of_continuousOn {O : Set ℂ} {E : ℂ → AdelicGL2 (𝓞 F) F → ℂ}
    (hE : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => E p.1 p.2) (O ×ˢ Set.univ)) {s : ℂ} (hs : s ∈ O) :
    Continuous (E s) := by
  have h := hE.comp_continuous (f := fun x : AdelicGL2 (𝓞 F) F => (s, x)) (continuous_const.prodMk continuous_id)
    (fun x => ⟨hs, Set.mem_univ x⟩)
  exact h

theorem memLp_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} {p : ℝ≥0∞}
    (hf : MemLp f p μ) : MemLp (fun x => conj (f x)) p μ := by
  refine hf.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hf.1) ?_
  exact Filter.Eventually.of_forall fun x => by simp

theorem integrable_mul_conj_of_memLp_two {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => f x * conj (g x)) μ :=
  memLp_one_iff_integrable.mp ((memLp_conj hg).mul' hf)

end Main

end R4TwoPairAxis

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open NumberField.AdelicHeight
open IsDedekindDomain AutomorphicForm Filter Topology Set
open scoped ComplexConjugate NNReal ENNReal
open R4TwoPairAxis

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

set_option quotPrecheck false in
set_option hygiene false in
local notation "TRUNC[" R "]" => @AutomorphicForm.lambdaT _
  (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
  (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
  (fun t => AutomorphicForm.unipotentGL2 t)
  (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)

set_option maxHeartbeats 6400000 in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν μ' ν' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμ' : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ') (_hν' : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν')
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμ'F : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ') (_hν'F : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν')
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hμ'k : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ' x : ℂˣ) : ℂ))
      (_hν'k : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν' x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ' αm hαm s) (etaSnd ν' αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eψ s g = ψf s g + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g))
      (t t' : ℝ) (_ht : t ≠ t') (R : ℝ) (_hR : R₀ ≤ R),
      (μ' = μ → ν' = ν → μ = ν → t + t' ≠ 0 →
        IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
            (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I)) x) *
            conj (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t' : ℂ) * Complex.I)) x))
          (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
        (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
            (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I)) x) *
            conj (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t' : ℂ) * Complex.I)) x)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
        (c : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp ((R : ℂ) * (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nψ ((t' : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I))
            + (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nψ ((t' : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp ((R : ℂ) * (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)) )) ∧
      (μ' = μ → ν' = ν → (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) →
        IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
            (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I)) x) *
            conj (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t' : ℂ) * Complex.I)) x))
          (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
        (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
            (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I)) x) *
            conj (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t' : ℂ) * Complex.I)) x)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
        (c : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp ((R : ℂ) * (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nψ ((t' : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) + conj ((t' : ℂ) * Complex.I)) )) ∧
      (μ' = ν → ν' = μ → (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z) → t + t' ≠ 0 →
        IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
            (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I)) x) *
            conj (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t' : ℂ) * Complex.I)) x))
          (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
        (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
            (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I)) x) *
            conj (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t' : ℂ) * Complex.I)) x)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
        (c : ℂ) *
          ( (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) * conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nψ ((t' : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp ((R : ℂ) * (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I))) / (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I))
            - (∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
                Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
                ∂(AutomorphicForm.maximalCompactHaar F)) *
                Complex.exp (-((R : ℂ) * (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)))) / (((t : ℂ) * Complex.I) - conj ((t' : ℂ) * Complex.I)) )) ∧
      ((∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ' z ≠ μ z ∨ ν' z ≠ ν z) →
        (∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ' z ≠ ν z ∨ ν' z ≠ μ z) →
        IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
            (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I)) x) *
            conj (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t' : ℂ) * Complex.I)) x))
          (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
        (∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
            (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eφ ((t : ℂ) * Complex.I)) x) *
            conj (@AutomorphicForm.lambdaT _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
            (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
              (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
            (Eψ ((t' : ℂ) * Complex.I)) x)
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) = 0) := by
  intro αm hαm
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F

  obtain ⟨c, hc, R₀, hinc⟩ :=
    AutomorphicForm.exists_forall_setIntegral_lambdaT_pseudoEisenstein_mul_conj_sub_eq_maassSelberg_sub_and_sub_eq_twoTerm_sub_and_sub_eq_cross_sub_and_sub_eq_zero_two_pairs_slab
      F α β hα hαβ ΦF hαm
  obtain ⟨c₂, _hc₂, habs2⟩ :=
    AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_twoTerm_slab_of_exists_ideleNorm_eq_one_ne
      F α β hα hαβ ΦF hαm
  obtain ⟨c₄, _hc₄, habs4⟩ :=
    AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_maassSelberg_slab
      F α β hα hαβ ΦF hαm
  obtain ⟨c₃, _hc₃, R₃, habs3⟩ :=
    AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_pseudoEisenstein_mul_conj_eq_cross_and_eq_zero_two_pairs_slab_of_re_lt_re
      F α β hα hαβ ΦF hαm
  refine ⟨c, hc, R₀, ?_⟩
  intro μ ν μ' ν' hμ hν hμ' hν' hμF hνF hμ'F hν'F hμk hνk hμ'k hν'k φf hφf hφfK hφff hφfjc hφfhol hφfKu
    ψf hψf hψfK hψff hψfjc hψfhol hψfKu Oφ Eφ Nφ hEφ Oψ Eψ Nψ hEψ t t' htt R hR
  obtain ⟨hOφ, hOφc, hOφax, hOφhalf, hEφa, hNφa, hEφjc, hNφjc, hEφeq, hNφeq⟩ := hEφ
  obtain ⟨hOψ, hOψc, hOψax, hOψhalf, hEψa, hNψa, hEψjc, hNψjc, hEψeq, hNψeq⟩ := hEψ

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 F) F) := inferInstance
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : IsFiniteMeasureOnCompacts (adelicGLHaar (Fin 2) (𝓞 F) F) := inferInstance
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := inferInstance
  haveI : SFinite ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β)) := inferInstance

  obtain ⟨hL2φ, hL2φc⟩ :=
    AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family
      F α β hα hαβ ΦF hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hOφ hOφc hOφhalf
      hEφa hNφa hEφjc hNφjc hEφeq hNφeq R
  obtain ⟨hL2ψ, hL2ψc⟩ :=
    AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family
      F α β hα hαβ ΦF hαm μ' ν' hμ' hν' hμ'F hν'F hμ'k hν'k ψf hψf hψfK hψff hψfjc hψfhol hψfKu Oψ Eψ Nψ hOψ hOψc
      hOψhalf hEψa hNψa hEψjc hNψjc hEψeq hNψeq R
  obtain ⟨hCTφa, hCTφjc, _hCTφeq⟩ :=
    AutomorphicForm.analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family
      F hαm μ ν hμ hν hμF hνF φf hφf hφfK hφff hφfjc hφfhol hφfKu Oφ Eφ Nφ hOφ hOφc hOφhalf
      hEφa hNφa hEφjc hNφjc hEφeq hNφeq
  obtain ⟨hCTψa, hCTψjc, _hCTψeq⟩ :=
    AutomorphicForm.analyticOnNhd_constantTerm_and_eq_add_of_axis_continuation_family
      F hαm μ' ν' hμ' hν' hμ'F hν'F ψf hψf hψfK hψff hψfjc hψfhol hψfKu Oψ Eψ Nψ hOψ hOψc hOψhalf
      hEψa hNψa hEψjc hNψjc hEψeq hNψeq

  have hH : MeasurableSet (highSet (adelicHeight F) (Real.exp R)) :=
    measurableSet_lt measurable_const (NumberField.AdelicHeight.continuous_adelicHeight F).measurable
  have hTφ_hol : ∀ x : AdelicGL2 (𝓞 F) F, DifferentiableOn ℂ (fun s => TRUNC[R] (Eφ s) x) Oφ := by
    intro x
    show DifferentiableOn ℂ (fun s => Eφ s x - Set.indicator (highSet (adelicHeight F) (Real.exp R))
      (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => AutomorphicForm.unipotentGL2 t) (Eφ s)) x) Oφ
    refine (hEφa x).differentiableOn.sub ?_
    by_cases hx : x ∈ highSet (adelicHeight F) (Real.exp R)
    · simp only [Set.indicator_of_mem hx]
      exact (hCTφa x).differentiableOn
    · simp only [Set.indicator_of_notMem hx]
      exact differentiableOn_const 0
  have hTψ_hol : ∀ x : AdelicGL2 (𝓞 F) F, DifferentiableOn ℂ (fun s => TRUNC[R] (Eψ s) x) Oψ := by
    intro x
    show DifferentiableOn ℂ (fun s => Eψ s x - Set.indicator (highSet (adelicHeight F) (Real.exp R))
      (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => AutomorphicForm.unipotentGL2 t) (Eψ s)) x) Oψ
    refine (hEψa x).differentiableOn.sub ?_
    by_cases hx : x ∈ highSet (adelicHeight F) (Real.exp R)
    · simp only [Set.indicator_of_mem hx]
      exact (hCTψa x).differentiableOn
    · simp only [Set.indicator_of_notMem hx]
      exact differentiableOn_const 0
  have hTφ_meas : ∀ s ∈ Oφ, Measurable (TRUNC[R] (Eφ s)) := by
    intro s hs
    have h1 : Continuous (Eφ s) := continuous_section_of_continuousOn F hEφjc hs
    have h2 : Continuous (fun x => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => AutomorphicForm.unipotentGL2 t) (Eφ s) x) :=
      continuous_section_of_continuousOn F
        (E := fun s x => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => AutomorphicForm.unipotentGL2 t) (Eφ s) x) hCTφjc hs
    exact h1.measurable.sub (h2.measurable.indicator hH)
  have hTψ_meas : ∀ s ∈ Oψ, Measurable (TRUNC[R] (Eψ s)) := by
    intro s hs
    have h1 : Continuous (Eψ s) := continuous_section_of_continuousOn F hEψjc hs
    have h2 : Continuous (fun x => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => AutomorphicForm.unipotentGL2 t) (Eψ s) x) :=
      continuous_section_of_continuousOn F
        (E := fun s x => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => AutomorphicForm.unipotentGL2 t) (Eψ s) x) hCTψjc hs
    exact h1.measurable.sub (h2.measurable.indicator hH)

  have haxφ : ((t : ℂ) * Complex.I) ∈ Oφ := hOφax (by simp)
  have haxψ : ((t' : ℂ) * Complex.I) ∈ Oψ := hOψax (by simp)
  have hInt : IntegrableOn (fun x : AdelicGL2 (𝓞 F) F => TRUNC[R] (Eφ ((t : ℂ) * Complex.I)) x *
      conj (TRUNC[R] (Eψ ((t' : ℂ) * Complex.I)) x)) (canonicalTruncationDomain F α β)
      (adelicGLHaar (Fin 2) (𝓞 F) F) :=
    integrable_mul_conj_of_memLp_two (hL2φ _ haxφ) (hL2ψ _ haxψ)

  set vC : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ)) with hvC
  set Ifun : ℂ → ℂ → ℂ := fun s u => ∫ x in canonicalTruncationDomain F α β, TRUNC[R] (Eφ s) x *
    conj (TRUNC[R] (Eψ (conj u)) x) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hIfun
  set Pfun : ℂ → ℂ → ℂ := fun s u => ∫ k, φf s (k : AdelicGL2 (𝓞 F) F) * conj (ψf (conj u) (k : AdelicGL2 (𝓞 F) F))
    ∂(AutomorphicForm.maximalCompactHaar F) with hPfun
  set Qfun : ℂ → ℂ → ℂ := fun s u =>
    ∫ k, (vC⁻¹ * Nφ s (k : AdelicGL2 (𝓞 F) F)) * conj (vC⁻¹ * Nψ (conj u) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hQfun
  set PCfun : ℂ → ℂ → ℂ := fun s u =>
    ∫ k, φf s (k : AdelicGL2 (𝓞 F) F) * conj (vC⁻¹ * Nψ (conj u) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hPCfun
  set QCfun : ℂ → ℂ → ℂ := fun s u =>
    ∫ k, (vC⁻¹ * Nφ s (k : AdelicGL2 (𝓞 F) F)) * conj (ψf (conj u) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hQCfun
  set Oψ' : Set ℂ := {u : ℂ | conj u ∈ Oψ} with hOψ'
  have hOψ'o : IsOpen Oψ' := isOpen_conj_preimage hOψ
  have hOψ'c : IsPreconnected Oψ' := isPreconnected_conj_preimage hOψc
  have hOψ'h : {s : ℂ | 1 / 2 < s.re} ⊆ Oψ' := fun u hu => hOψhalf (conj_mem_half hu)

  have hMφjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => vC⁻¹ * Nφ p.1 p.2) (Oφ ×ˢ Set.univ) :=
    continuousOn_const.mul hNφjc
  have hMψjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => vC⁻¹ * Nψ p.1 p.2) (Oψ ×ˢ Set.univ) :=
    continuousOn_const.mul hNψjc
  have hMφd : ∀ g, DifferentiableOn ℂ (fun s => vC⁻¹ * Nφ s g) Oφ := fun g => (hNφa g).differentiableOn.const_mul _
  have hMψd : ∀ g, DifferentiableOn ℂ (fun s => vC⁻¹ * Nψ s g) Oψ := fun g => (hNψa g).differentiableOn.const_mul _

  have hI1 : ∀ u ∈ Oψ', DifferentiableOn ℂ (fun s => Ifun s u) Oφ := by
    intro u hu
    have hu' : conj u ∈ Oψ := hu
    exact Complex.differentiableOn_integral_mul_of_memLp_two_of_tendsto_eLpNorm_of_forall_differentiableOn
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β)) hOφ (fun s x => TRUNC[R] (Eφ s) x)
      (fun x => conj (TRUNC[R] (Eψ (conj u)) x)) (memLp_conj (hL2ψ _ hu')) hTφ_meas hL2φ hL2φc hTφ_hol
  have hP1 : ∀ u ∈ Oψ', DifferentiableOn ℂ (fun s => Pfun s u) Oφ := by
    intro u hu
    refine differentiableOn_integral_maximalCompact F hOφ (fun s g => φf s g * conj (ψf (conj u) g)) ?_ ?_
    · exact (hφfjc.mul (Complex.continuous_conj.comp ((continuous_section F hψfjc (conj u)).comp
        continuous_snd))).continuousOn
    · intro g
      exact ((hφfhol g).mul_const _).differentiableOn
  have hQ1 : ∀ u ∈ Oψ', DifferentiableOn ℂ (fun s => Qfun s u) Oφ := by
    intro u hu
    have hu' : conj u ∈ Oψ := hu
    refine differentiableOn_integral_maximalCompact F hOφ
      (fun s g => (vC⁻¹ * Nφ s g) * conj (vC⁻¹ * Nψ (conj u) g)) ?_ ?_
    · have h2 : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => conj (vC⁻¹ * Nψ (conj u) p.2)) :=
        Complex.continuous_conj.comp (continuous_const.mul
          ((continuous_section_of_continuousOn F hNψjc hu').comp continuous_snd))
      exact hMφjc.mul h2.continuousOn
    · intro g
      exact (hMφd g).mul_const _
  have hPC1 : ∀ u ∈ Oψ', DifferentiableOn ℂ (fun s => PCfun s u) Oφ := by
    intro u hu
    have hu' : conj u ∈ Oψ := hu
    refine differentiableOn_integral_maximalCompact F hOφ
      (fun s g => φf s g * conj (vC⁻¹ * Nψ (conj u) g)) ?_ ?_
    · have h2 : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => conj (vC⁻¹ * Nψ (conj u) p.2)) :=
        Complex.continuous_conj.comp (continuous_const.mul
          ((continuous_section_of_continuousOn F hNψjc hu').comp continuous_snd))
      exact hφfjc.continuousOn.mul h2.continuousOn
    · intro g
      exact ((hφfhol g).mul_const _).differentiableOn
  have hQC1 : ∀ u ∈ Oψ', DifferentiableOn ℂ (fun s => QCfun s u) Oφ := by
    intro u hu
    refine differentiableOn_integral_maximalCompact F hOφ
      (fun s g => (vC⁻¹ * Nφ s g) * conj (ψf (conj u) g)) ?_ ?_
    · have h2 : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => conj (ψf (conj u) p.2)) :=
        Complex.continuous_conj.comp ((continuous_section F hψfjc (conj u)).comp continuous_snd)
      exact hMφjc.mul h2.continuousOn
    · intro g
      exact (hMφd g).mul_const _

  have hI2 : ∀ s ∈ Oφ, DifferentiableOn ℂ (fun u => Ifun s u) Oψ' := by
    intro s hs
    set J : ℂ → ℂ := fun w => ∫ x in canonicalTruncationDomain F α β, TRUNC[R] (Eψ w) x * conj (TRUNC[R] (Eφ s) x)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hJ
    have hJd : DifferentiableOn ℂ J Oψ :=
      Complex.differentiableOn_integral_mul_of_memLp_two_of_tendsto_eLpNorm_of_forall_differentiableOn
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (canonicalTruncationDomain F α β)) hOψ (fun w x => TRUNC[R] (Eψ w) x)
        (fun x => conj (TRUNC[R] (Eφ s) x)) (memLp_conj (hL2φ _ hs)) hTψ_meas hL2ψ hL2ψc hTψ_hol
    have h := differentiableOn_conj_conj hOψ hJd
    refine h.congr fun u _ => ?_
    simp only [hIfun, hJ]
    rw [← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  have hP2 : ∀ s ∈ Oφ, DifferentiableOn ℂ (fun u => Pfun s u) Oψ' := by
    intro s hs
    have h := differentiableOn_integral_maximalCompact_conj F isOpen_univ (φf s) (continuous_section F hφfjc s) ψf
      hψfjc.continuousOn (fun g => (hψfhol g).differentiableOn)
    exact h.mono fun _ _ => Set.mem_univ _
  have hQ2 : ∀ s ∈ Oφ, DifferentiableOn ℂ (fun u => Qfun s u) Oψ' := by
    intro s hs
    exact differentiableOn_integral_maximalCompact_conj F hOψ (fun g => vC⁻¹ * Nφ s g)
      (continuous_const.mul (continuous_section_of_continuousOn F hNφjc hs)) (fun w g => vC⁻¹ * Nψ w g) hMψjc hMψd
  have hPC2 : ∀ s ∈ Oφ, DifferentiableOn ℂ (fun u => PCfun s u) Oψ' := by
    intro s hs
    exact differentiableOn_integral_maximalCompact_conj F hOψ (φf s) (continuous_section F hφfjc s)
      (fun w g => vC⁻¹ * Nψ w g) hMψjc hMψd
  have hQC2 : ∀ s ∈ Oφ, DifferentiableOn ℂ (fun u => QCfun s u) Oψ' := by
    intro s hs
    have h := differentiableOn_integral_maximalCompact_conj F isOpen_univ (fun g => vC⁻¹ * Nφ s g)
      (continuous_const.mul (continuous_section_of_continuousOn F hNφjc hs)) ψf hψfjc.continuousOn
      (fun g => (hψfhol g).differentiableOn)
    exact h.mono fun _ _ => Set.mem_univ _

  have eXs : ∀ u, DifferentiableOn ℂ (fun s : ℂ => s + u) Oφ := fun u => differentiableOn_id.add (differentiableOn_const _)
  have eYs : ∀ u, DifferentiableOn ℂ (fun s : ℂ => s - u) Oφ := fun u => differentiableOn_id.sub (differentiableOn_const _)
  have eXu : ∀ s, DifferentiableOn ℂ (fun u : ℂ => s + u) Oψ' := fun s => (differentiableOn_const _).add differentiableOn_id
  have eYu : ∀ s, DifferentiableOn ℂ (fun u : ℂ => s - u) Oψ' := fun s => (differentiableOn_const _).sub differentiableOn_id

  set s₀ : ℂ := (t : ℂ) * Complex.I with hs₀
  set u₀ : ℂ := conj ((t' : ℂ) * Complex.I) with hu₀
  have hu₀mem : u₀ ∈ Oψ' := by
    show conj u₀ ∈ Oψ
    rw [hu₀, Complex.conj_conj]
    exact haxψ
  have hcu : conj u₀ = (t' : ℂ) * Complex.I := by rw [hu₀, Complex.conj_conj]
  have hX0 : s₀ + u₀ ≠ 0 := by
    rw [hs₀, hu₀]
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact htt (by linarith)
  have hY0_of : t + t' ≠ 0 → s₀ - u₀ ≠ 0 := by
    intro htt' h0
    rw [hs₀, hu₀] at h0
    have := congrArg Complex.im h0
    simp at this
    exact htt' (by linarith)

  have wedge : ∀ s u : ℂ, 1 / 2 < s.re → s.re < u.re →
      1 / 2 < (conj u).re ∧ s.re < (conj u).re ∧ s ≠ conj (conj u) ∧ (s - conj (conj u)).re < 0 := by
    intro s u hs hlt
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Complex.conj_re]; linarith
    · rw [Complex.conj_re]; exact hlt
    · rw [Complex.conj_conj]
      intro h
      rw [h] at hlt
      exact lt_irrefl _ hlt
    · rw [Complex.conj_conj, Complex.sub_re]; linarith
  refine ⟨fun h1 h2 hμν htt' => ?_, fun h1 h2 hμν => ?_, fun h1 h2 hμν htt' => ?_, fun hD1 hD2 => ?_⟩
  ·

    obtain rfl : μ = μ' := h1.symm
    obtain rfl : ν = ν' := h2.symm
    refine ⟨hInt, ?_⟩
    have hY0 : s₀ - u₀ ≠ 0 := hY0_of htt'
    set Kfun : ℂ → ℂ → ℂ := fun s u => (s + u) * (s - u) * Ifun s u
        - (c : ℂ) * ((s - u) * (Pfun s u * Complex.exp ((R : ℂ) * (s + u)) - Qfun s u * Complex.exp (-((R : ℂ) * (s + u))))
          + (s + u) * (PCfun s u * Complex.exp ((R : ℂ) * (s - u)) - QCfun s u * Complex.exp (-((R : ℂ) * (s - u)))))
      with hKfun
    have hK1 : ∀ u ∈ Oψ', DifferentiableOn ℂ (fun s => Kfun s u) Oφ := by
      intro u hu
      have e2 : DifferentiableOn ℂ (fun s : ℂ => Complex.exp ((R : ℂ) * (s + u))) Oφ :=
        ((differentiableOn_const _).mul (eXs u)).cexp
      have e3 : DifferentiableOn ℂ (fun s : ℂ => Complex.exp (-((R : ℂ) * (s + u)))) Oφ :=
        ((differentiableOn_const _).mul (eXs u)).neg.cexp
      have e4 : DifferentiableOn ℂ (fun s : ℂ => Complex.exp ((R : ℂ) * (s - u))) Oφ :=
        ((differentiableOn_const _).mul (eYs u)).cexp
      have e5 : DifferentiableOn ℂ (fun s : ℂ => Complex.exp (-((R : ℂ) * (s - u)))) Oφ :=
        ((differentiableOn_const _).mul (eYs u)).neg.cexp
      show DifferentiableOn ℂ (fun s => (s + u) * (s - u) * Ifun s u
        - (c : ℂ) * ((s - u) * (Pfun s u * Complex.exp ((R : ℂ) * (s + u)) - Qfun s u * Complex.exp (-((R : ℂ) * (s + u))))
          + (s + u) * (PCfun s u * Complex.exp ((R : ℂ) * (s - u)) - QCfun s u * Complex.exp (-((R : ℂ) * (s - u)))))) Oφ
      exact (((eXs u).mul (eYs u)).mul (hI1 u hu)).sub ((differentiableOn_const _).mul
        (((eYs u).mul (((hP1 u hu).mul e2).sub ((hQ1 u hu).mul e3))).add
          ((eXs u).mul (((hPC1 u hu).mul e4).sub ((hQC1 u hu).mul e5)))))
    have hK2 : ∀ s ∈ Oφ, DifferentiableOn ℂ (fun u => Kfun s u) Oψ' := by
      intro s hs
      have e2 : DifferentiableOn ℂ (fun u : ℂ => Complex.exp ((R : ℂ) * (s + u))) Oψ' :=
        ((differentiableOn_const _).mul (eXu s)).cexp
      have e3 : DifferentiableOn ℂ (fun u : ℂ => Complex.exp (-((R : ℂ) * (s + u)))) Oψ' :=
        ((differentiableOn_const _).mul (eXu s)).neg.cexp
      have e4 : DifferentiableOn ℂ (fun u : ℂ => Complex.exp ((R : ℂ) * (s - u))) Oψ' :=
        ((differentiableOn_const _).mul (eYu s)).cexp
      have e5 : DifferentiableOn ℂ (fun u : ℂ => Complex.exp (-((R : ℂ) * (s - u)))) Oψ' :=
        ((differentiableOn_const _).mul (eYu s)).neg.cexp
      show DifferentiableOn ℂ (fun u => (s + u) * (s - u) * Ifun s u
        - (c : ℂ) * ((s - u) * (Pfun s u * Complex.exp ((R : ℂ) * (s + u)) - Qfun s u * Complex.exp (-((R : ℂ) * (s + u))))
          + (s + u) * (PCfun s u * Complex.exp ((R : ℂ) * (s - u)) - QCfun s u * Complex.exp (-((R : ℂ) * (s - u)))))) Oψ'
      exact (((eXu s).mul (eYu s)).mul (hI2 s hs)).sub ((differentiableOn_const _).mul
        (((eYu s).mul (((hP2 s hs).mul e2).sub ((hQ2 s hs).mul e3))).add
          ((eXu s).mul (((hPC2 s hs).mul e4).sub ((hQC2 s hs).mul e5)))))

    have hK3 : ∀ s u : ℂ, 1 / 2 < s.re → s.re < u.re → Kfun s u = 0 := by
      intro s u hs hlt
      set s' : ℂ := conj u with hs'def
      obtain ⟨hs', -, hne, -⟩ := wedge s u hs hlt
      have hcs' : conj s' = u := by rw [hs'def, Complex.conj_conj]
      have hsu : s ≠ u := by rw [← hcs']; exact hne

      set φ₁ : AdelicGL2 (𝓞 F) F → ℂ := φf s with hφ₁
      set ψ₁ : AdelicGL2 (𝓞 F) F → ℂ := ψf s' with hψ₁
      have hφ₁c : Continuous φ₁ := continuous_section F hφfjc s
      have hψ₁c : Continuous ψ₁ := continuous_section F hψfjc s'
      have hE1 : Eφ s = pseudoEisenstein F φ₁ := funext fun g => hEφeq s hs g
      have hE2 : Eψ s' = pseudoEisenstein F ψ₁ := funext fun g => hEψeq s' hs' g
      have hN1 : ∀ g, Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ₁ g := hNφeq s hs
      have hN2 : ∀ g, Nψ s' g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ₁ g := hNψeq s' hs'

      have hinc' := hinc μ ν μ ν hμ hν hμ hν hμF hνF hμF hνF s s' hs hs' φ₁ (hφf s) hφ₁c (hφfK s) (hφff s)
        ψ₁ (hψf s') hψ₁c (hψfK s') (hψff s')
      obtain ⟨R₂, habs'⟩ := habs4 μ ν hμν hμ hν hμF hνF s s' hs hs' hne φ₁ (hφf s) hφ₁c (hφfK s) (hφff s)
        ψ₁ (hψf s') hψ₁c (hψfK s') (hψff s')

      set X : ℂ := s + conj s' with hX
      set Y : ℂ := s - conj s' with hY
      have hxu : s + u = X := by rw [hX, hcs']
      have hyu : s - u = Y := by rw [hY, hcs']
      set P₁ : ℂ := ∫ k, φ₁ (k : AdelicGL2 (𝓞 F) F) * conj (ψ₁ (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hP₁
      set Q₁ : ℂ := ∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ₁ g) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ₁ g) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hQ₁
      set PC₁ : ℂ := ∫ k, φ₁ (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ₁ g) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hPC₁
      set QC₁ : ℂ := ∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ₁ g) (k : AdelicGL2 (𝓞 F) F) *
        conj (ψ₁ (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hQC₁
      set 𝓘 : ℝ → ℂ := fun ρ => ∫ y in canonicalTruncationDomain F α β, TRUNC[ρ] (pseudoEisenstein F φ₁) y *
        conj (TRUNC[ρ] (pseudoEisenstein F ψ₁) y) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with h𝓘
      set 𝓑 : ℝ → ℂ := fun ρ => P₁ * Complex.exp ((ρ : ℂ) * X) / X - Q₁ * Complex.exp (-((ρ : ℂ) * X)) / X
        + PC₁ * Complex.exp ((ρ : ℂ) * Y) / Y - QC₁ * Complex.exp (-((ρ : ℂ) * Y)) / Y with h𝓑

      set R₁ : ℝ := max R R₂ with hR₁
      have hkey : ∀ ρ : ℝ, R₁ ≤ ρ → ((c₄ : ℂ) - c) * 𝓑 ρ = 𝓘 R - c * 𝓑 R := by
        intro ρ hρ
        have hρ1 : R ≤ ρ := le_trans (le_max_left _ _) hρ
        have hρ2 : R₂ ≤ ρ := le_trans (le_max_right _ _) hρ
        obtain ⟨_, _, hI4, _, _, _⟩ := hinc' R ρ hR hρ1
        have hI := hI4 rfl rfl hμν hne
        obtain ⟨_, hA⟩ := habs' ρ hρ2
        have hI' : 𝓘 ρ - 𝓘 R = c * (𝓑 ρ - 𝓑 R) := by
          have := hI
          simp only [h𝓘, h𝓑]
          linear_combination this
        have hA' : 𝓘 ρ = c₄ * 𝓑 ρ := by
          have := hA
          simp only [h𝓘, h𝓑]
          linear_combination this
        linear_combination hI' - hA'
      have hx1 : 1 < X.re := by
        rw [hX, Complex.add_re, Complex.conj_re]
        linarith
      have hXY : |Y.re| < X.re := by
        rw [hY, hX, Complex.sub_re, Complex.add_re, Complex.conj_re]
        rw [abs_sub_lt_iff]
        constructor <;> linarith
      have hYne : Y ≠ 0 := by rw [← hyu]; exact sub_ne_zero.mpr hsu
      have hx0 : X ≠ 0 := by
        intro h0
        rw [h0, Complex.zero_re] at hx1
        linarith
      have hκ : 𝓘 R - c * 𝓑 R = 0 := by
        refine kappa4_eq_zero ((c₄ : ℂ) - c) _ (P₁ / X) (-(Q₁ / X)) (PC₁ / Y) (-(QC₁ / Y)) X Y R₁ hXY hYne
          fun ρ hρ => ?_
        rw [← hkey ρ hρ]
        simp only [h𝓑]
        ring

      have hIeq : Ifun s u = 𝓘 R := by
        simp only [hIfun, h𝓘, ← hs'def, hE1, hE2]
      have hPeq : Pfun s u = P₁ := by
        simp only [hPfun, hP₁, ← hs'def, hφ₁, hψ₁]
      have hQeq : Qfun s u = Q₁ := by
        simp only [hQfun, hQ₁, ← hs'def, hvC]
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hN1, hN2]
      have hPCeq : PCfun s u = PC₁ := by
        simp only [hPCfun, hPC₁, ← hs'def, hφ₁, hvC]
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hN2]
      have hQCeq : QCfun s u = QC₁ := by
        simp only [hQCfun, hQC₁, ← hs'def, hψ₁, hvC]
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hN1]
      have h𝓑R : X * Y * 𝓑 R = Y * (P₁ * Complex.exp ((R : ℂ) * X) - Q₁ * Complex.exp (-((R : ℂ) * X)))
          + X * (PC₁ * Complex.exp ((R : ℂ) * Y) - QC₁ * Complex.exp (-((R : ℂ) * Y))) := by
        simp only [h𝓑]
        field_simp
        ring
      simp only [hKfun]
      rw [hIeq, hPeq, hQeq, hPCeq, hQCeq, hxu, hyu]
      have : 𝓘 R = c * 𝓑 R := by linear_combination hκ
      rw [this]
      linear_combination (c : ℂ) * h𝓑R

    have hvan := sesqui_identity_lt hOφ hOφc hOφhalf hOψ'o hOψ'c hOψ'h Kfun hK1 hK2 hK3
    have hK0 := hvan s₀ haxφ u₀ hu₀mem
    simp only [hKfun, hIfun, hPfun, hQfun, hPCfun, hQCfun] at hK0
    rw [hcu, sub_eq_zero] at hK0
    set II : ℂ := ∫ x in canonicalTruncationDomain F α β, TRUNC[R] (Eφ s₀) x *
      conj (TRUNC[R] (Eψ ((t' : ℂ) * Complex.I)) x) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hII
    set PP : ℂ := ∫ k, φf s₀ (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hPP
    set QQ : ℂ := ∫ k, (vC⁻¹ * Nφ s₀ (k : AdelicGL2 (𝓞 F) F)) *
      conj (vC⁻¹ * Nψ ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hQQ
    set PC : ℂ := ∫ k, φf s₀ (k : AdelicGL2 (𝓞 F) F) *
      conj (vC⁻¹ * Nψ ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hPC
    set QC : ℂ := ∫ k, (vC⁻¹ * Nφ s₀ (k : AdelicGL2 (𝓞 F) F)) *
      conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hQC
    have hgoal : II = (c : ℂ) * (PP * Complex.exp ((R : ℂ) * (s₀ + u₀)) / (s₀ + u₀)
          - QQ * Complex.exp (-((R : ℂ) * (s₀ + u₀))) / (s₀ + u₀)
          + PC * Complex.exp ((R : ℂ) * (s₀ - u₀)) / (s₀ - u₀)
          - QC * Complex.exp (-((R : ℂ) * (s₀ - u₀))) / (s₀ - u₀)) := by
      apply mul_left_cancel₀ (mul_ne_zero hX0 hY0)
      rw [hK0]
      field_simp
      ring
    exact hgoal
  ·

    obtain rfl : μ = μ' := h1.symm
    obtain rfl : ν = ν' := h2.symm
    refine ⟨hInt, ?_⟩
    have hoff : ∃ z : (AdeleRing (𝓞 F) F)ˣ, NumberField.TateGlobal.ideleNorm F z = 1 ∧ μ z ≠ ν z := by
      obtain ⟨z, hz, hne⟩ := hμν
      exact ⟨z, (NumberField.TateGlobal.mem_normOneIdeles_iff z).mp hz, hne⟩
    set Kfun : ℂ → ℂ → ℂ := fun s u => (s + u) * Ifun s u
        - (c : ℂ) * (Pfun s u * Complex.exp ((R : ℂ) * (s + u)) - Qfun s u * Complex.exp (-((R : ℂ) * (s + u))))
      with hKfun
    have hK1 : ∀ u ∈ Oψ', DifferentiableOn ℂ (fun s => Kfun s u) Oφ := by
      intro u hu
      have e2 : DifferentiableOn ℂ (fun s : ℂ => Complex.exp ((R : ℂ) * (s + u))) Oφ :=
        ((differentiableOn_const _).mul (eXs u)).cexp
      have e3 : DifferentiableOn ℂ (fun s : ℂ => Complex.exp (-((R : ℂ) * (s + u)))) Oφ :=
        ((differentiableOn_const _).mul (eXs u)).neg.cexp
      show DifferentiableOn ℂ (fun s => (s + u) * Ifun s u
        - (c : ℂ) * (Pfun s u * Complex.exp ((R : ℂ) * (s + u)) - Qfun s u * Complex.exp (-((R : ℂ) * (s + u))))) Oφ
      exact ((eXs u).mul (hI1 u hu)).sub ((differentiableOn_const _).mul (((hP1 u hu).mul e2).sub ((hQ1 u hu).mul e3)))
    have hK2 : ∀ s ∈ Oφ, DifferentiableOn ℂ (fun u => Kfun s u) Oψ' := by
      intro s hs
      have e2 : DifferentiableOn ℂ (fun u : ℂ => Complex.exp ((R : ℂ) * (s + u))) Oψ' :=
        ((differentiableOn_const _).mul (eXu s)).cexp
      have e3 : DifferentiableOn ℂ (fun u : ℂ => Complex.exp (-((R : ℂ) * (s + u)))) Oψ' :=
        ((differentiableOn_const _).mul (eXu s)).neg.cexp
      show DifferentiableOn ℂ (fun u => (s + u) * Ifun s u
        - (c : ℂ) * (Pfun s u * Complex.exp ((R : ℂ) * (s + u)) - Qfun s u * Complex.exp (-((R : ℂ) * (s + u))))) Oψ'
      exact ((eXu s).mul (hI2 s hs)).sub ((differentiableOn_const _).mul (((hP2 s hs).mul e2).sub ((hQ2 s hs).mul e3)))

    have hK3 : ∀ s u : ℂ, 1 / 2 < s.re → s.re < u.re → Kfun s u = 0 := by
      intro s u hs hlt
      set s' : ℂ := conj u with hs'def
      obtain ⟨hs', -, -, -⟩ := wedge s u hs hlt

      set φ₁ : AdelicGL2 (𝓞 F) F → ℂ := φf s with hφ₁
      set ψ₁ : AdelicGL2 (𝓞 F) F → ℂ := ψf s' with hψ₁
      have hφ₁c : Continuous φ₁ := continuous_section F hφfjc s
      have hψ₁c : Continuous ψ₁ := continuous_section F hψfjc s'
      have hE1 : Eφ s = pseudoEisenstein F φ₁ := funext fun g => hEφeq s hs g
      have hE2 : Eψ s' = pseudoEisenstein F ψ₁ := funext fun g => hEψeq s' hs' g
      have hN1 : ∀ g, Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ₁ g := hNφeq s hs
      have hN2 : ∀ g, Nψ s' g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ₁ g := hNψeq s' hs'

      have hinc' := hinc μ ν μ ν hμ hν hμ hν hμF hνF hμF hνF s s' hs hs' φ₁ (hφf s) hφ₁c (hφfK s) (hφff s)
        ψ₁ (hψf s') hψ₁c (hψfK s') (hψff s')
      obtain ⟨R₂, habs'⟩ := habs2 μ ν hoff hμ hν hμF hνF s s' hs hs' φ₁ (hφf s) hφ₁c (hφfK s) (hφff s)
        ψ₁ (hψf s') hψ₁c (hψfK s') (hψff s')

      set x : ℂ := s + conj s' with hx
      have hxu : s + u = x := by rw [hx, hs'def, Complex.conj_conj]
      set P₁ : ℂ := ∫ k, φ₁ (k : AdelicGL2 (𝓞 F) F) * conj (ψ₁ (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hP₁
      set Q₁ : ℂ := ∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ₁ g) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ₁ g) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hQ₁
      set 𝓘 : ℝ → ℂ := fun ρ => ∫ y in canonicalTruncationDomain F α β, TRUNC[ρ] (pseudoEisenstein F φ₁) y *
        conj (TRUNC[ρ] (pseudoEisenstein F ψ₁) y) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with h𝓘
      set 𝓑 : ℝ → ℂ := fun ρ => P₁ * Complex.exp ((ρ : ℂ) * x) / x - Q₁ * Complex.exp (-((ρ : ℂ) * x)) / x with h𝓑

      set R₁ : ℝ := max R R₂ with hR₁
      have hkey : ∀ n : ℕ, n ≤ 2 → ((c₂ : ℂ) - c) * 𝓑 (R₁ + n) = 𝓘 R - c * 𝓑 R := by
        intro n _
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hR₁a : R ≤ R₁ := by rw [hR₁]; exact le_max_left _ _
        have hR₁b : R₂ ≤ R₁ := by rw [hR₁]; exact le_max_right _ _
        have hρ1 : R ≤ R₁ + n := by linarith
        have hρ2 : R₂ ≤ R₁ + n := by linarith
        obtain ⟨_, _, _, hI2', _, _⟩ := hinc' R (R₁ + n) hR hρ1
        have hI := hI2' rfl rfl hμν
        obtain ⟨_, hA⟩ := habs' (R₁ + n) hρ2
        have hI' : 𝓘 (R₁ + n) - 𝓘 R = c * (𝓑 (R₁ + n) - 𝓑 R) := by
          have := hI
          simp only [h𝓘, h𝓑]
          linear_combination this
        have hA' : 𝓘 (R₁ + n) = c₂ * 𝓑 (R₁ + n) := by
          have := hA
          simp only [h𝓘, h𝓑]
          linear_combination this
        linear_combination hI' - hA'
      have hx1 : 1 < x.re := by
        rw [hx, Complex.add_re, Complex.conj_re]
        linarith
      have hEx : ‖Complex.exp x‖ ≠ 1 := by
        rw [Complex.norm_exp]
        have : Real.exp x.re > 1 := Real.one_lt_exp_iff.mpr (by linarith)
        exact ne_of_gt this
      have hκ : 𝓘 R - c * 𝓑 R = 0 := by
        refine kappa_eq_zero c c₂ x P₁ Q₁ _ R₁ hEx fun n hn => ?_
        have := hkey n hn
        simp only [h𝓑] at this
        exact this

      have hIeq : Ifun s u = 𝓘 R := by
        simp only [hIfun, h𝓘, ← hs'def, hE1, hE2]
      have hPeq : Pfun s u = P₁ := by
        simp only [hPfun, hP₁, ← hs'def, hφ₁, hψ₁]
      have hQeq : Qfun s u = Q₁ := by
        simp only [hQfun, hQ₁, ← hs'def, hvC]
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hN1, hN2]
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, Complex.zero_re] at hx1
        linarith
      have h𝓑R : x * 𝓑 R = P₁ * Complex.exp ((R : ℂ) * x) - Q₁ * Complex.exp (-((R : ℂ) * x)) := by
        simp only [h𝓑]
        field_simp
      simp only [hKfun]
      rw [hIeq, hPeq, hQeq, hxu]
      have : 𝓘 R = c * 𝓑 R := by linear_combination hκ
      rw [this]
      linear_combination (c : ℂ) * h𝓑R

    have hvan := sesqui_identity_lt hOφ hOφc hOφhalf hOψ'o hOψ'c hOψ'h Kfun hK1 hK2 hK3
    have hK0 := hvan s₀ haxφ u₀ hu₀mem
    simp only [hKfun, hIfun, hPfun, hQfun] at hK0
    rw [hcu, sub_eq_zero] at hK0
    set II : ℂ := ∫ x in canonicalTruncationDomain F α β, TRUNC[R] (Eφ s₀) x *
      conj (TRUNC[R] (Eψ ((t' : ℂ) * Complex.I)) x) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hII
    set PP : ℂ := ∫ k, φf s₀ (k : AdelicGL2 (𝓞 F) F) * conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hPP
    set QQ : ℂ := ∫ k, (vC⁻¹ * Nφ s₀ (k : AdelicGL2 (𝓞 F) F)) *
      conj (vC⁻¹ * Nψ ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hQQ
    have hgoal : II = (c : ℂ) * (PP * Complex.exp ((R : ℂ) * (s₀ + u₀)) / (s₀ + u₀)
        - QQ * Complex.exp (-((R : ℂ) * (s₀ + u₀))) / (s₀ + u₀)) := by
      rw [show (c : ℂ) * (PP * Complex.exp ((R : ℂ) * (s₀ + u₀)) / (s₀ + u₀)
          - QQ * Complex.exp (-((R : ℂ) * (s₀ + u₀))) / (s₀ + u₀))
          = ((c : ℂ) * (PP * Complex.exp ((R : ℂ) * (s₀ + u₀)) - QQ * Complex.exp (-((R : ℂ) * (s₀ + u₀))))) / (s₀ + u₀)
          by field_simp, ← hK0, mul_div_cancel_left₀ _ hX0]
    exact hgoal
  ·

    obtain rfl : ν = μ' := h1.symm
    obtain rfl : μ = ν' := h2.symm
    refine ⟨hInt, ?_⟩
    have hY0 : s₀ - u₀ ≠ 0 := hY0_of htt'
    set Kfun : ℂ → ℂ → ℂ := fun s u => (s - u) * Ifun s u
        - (c : ℂ) * (PCfun s u * Complex.exp ((R : ℂ) * (s - u)) - QCfun s u * Complex.exp (-((R : ℂ) * (s - u))))
      with hKfun
    have hK1 : ∀ u ∈ Oψ', DifferentiableOn ℂ (fun s => Kfun s u) Oφ := by
      intro u hu
      have e4 : DifferentiableOn ℂ (fun s : ℂ => Complex.exp ((R : ℂ) * (s - u))) Oφ :=
        ((differentiableOn_const _).mul (eYs u)).cexp
      have e5 : DifferentiableOn ℂ (fun s : ℂ => Complex.exp (-((R : ℂ) * (s - u)))) Oφ :=
        ((differentiableOn_const _).mul (eYs u)).neg.cexp
      show DifferentiableOn ℂ (fun s => (s - u) * Ifun s u
        - (c : ℂ) * (PCfun s u * Complex.exp ((R : ℂ) * (s - u)) - QCfun s u * Complex.exp (-((R : ℂ) * (s - u))))) Oφ
      exact ((eYs u).mul (hI1 u hu)).sub ((differentiableOn_const _).mul (((hPC1 u hu).mul e4).sub ((hQC1 u hu).mul e5)))
    have hK2 : ∀ s ∈ Oφ, DifferentiableOn ℂ (fun u => Kfun s u) Oψ' := by
      intro s hs
      have e4 : DifferentiableOn ℂ (fun u : ℂ => Complex.exp ((R : ℂ) * (s - u))) Oψ' :=
        ((differentiableOn_const _).mul (eYu s)).cexp
      have e5 : DifferentiableOn ℂ (fun u : ℂ => Complex.exp (-((R : ℂ) * (s - u)))) Oψ' :=
        ((differentiableOn_const _).mul (eYu s)).neg.cexp
      show DifferentiableOn ℂ (fun u => (s - u) * Ifun s u
        - (c : ℂ) * (PCfun s u * Complex.exp ((R : ℂ) * (s - u)) - QCfun s u * Complex.exp (-((R : ℂ) * (s - u))))) Oψ'
      exact ((eYu s).mul (hI2 s hs)).sub ((differentiableOn_const _).mul (((hPC2 s hs).mul e4).sub ((hQC2 s hs).mul e5)))

    have hK3 : ∀ s u : ℂ, 1 / 2 < s.re → s.re < u.re → Kfun s u = 0 := by
      intro s u hs hlt
      set s' : ℂ := conj u with hs'def
      obtain ⟨hs', hlt', hne, hYre⟩ := wedge s u hs hlt

      set φ₁ : AdelicGL2 (𝓞 F) F → ℂ := φf s with hφ₁
      set ψ₁ : AdelicGL2 (𝓞 F) F → ℂ := ψf s' with hψ₁
      have hφ₁c : Continuous φ₁ := continuous_section F hφfjc s
      have hψ₁c : Continuous ψ₁ := continuous_section F hψfjc s'
      have hE1 : Eφ s = pseudoEisenstein F φ₁ := funext fun g => hEφeq s hs g
      have hE2 : Eψ s' = pseudoEisenstein F ψ₁ := funext fun g => hEψeq s' hs' g
      have hN1 : ∀ g, Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ₁ g := hNφeq s hs
      have hN2 : ∀ g, Nψ s' g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ₁ g := hNψeq s' hs'

      have hinc' := hinc μ ν ν μ hμ hν hν hμ hμF hνF hνF hμF s s' hs hs' φ₁ (hφf s) hφ₁c (hφfK s) (hφff s)
        ψ₁ (hψf s') hψ₁c (hψfK s') (hψff s')
      have habs' := habs3 μ ν ν μ hμ hν hν hμ hμF hνF hνF hμF s s' hs hs' hlt' φ₁ (hφf s) hφ₁c (hφfK s) (hφff s)
        ψ₁ (hψf s') hψ₁c (hψfK s') (hψff s')

      set Y : ℂ := s - conj s' with hY
      have hyu : s - u = Y := by rw [hY, hs'def, Complex.conj_conj]
      set PC₁ : ℂ := ∫ k, φ₁ (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) ψ₁ g) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hPC₁
      set QC₁ : ℂ := ∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ₁ g) (k : AdelicGL2 (𝓞 F) F) *
        conj (ψ₁ (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F) with hQC₁
      set 𝓘 : ℝ → ℂ := fun ρ => ∫ y in canonicalTruncationDomain F α β, TRUNC[ρ] (pseudoEisenstein F φ₁) y *
        conj (TRUNC[ρ] (pseudoEisenstein F ψ₁) y) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with h𝓘
      set 𝓑 : ℝ → ℂ := fun ρ => PC₁ * Complex.exp ((ρ : ℂ) * Y) / Y - QC₁ * Complex.exp (-((ρ : ℂ) * Y)) / Y with h𝓑

      set R₁ : ℝ := max R R₃ with hR₁
      have hkey : ∀ n : ℕ, n ≤ 2 → ((c₃ : ℂ) - c) * 𝓑 (R₁ + n) = 𝓘 R - c * 𝓑 R := by
        intro n _
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hR₁a : R ≤ R₁ := by rw [hR₁]; exact le_max_left _ _
        have hR₁b : R₃ ≤ R₁ := by rw [hR₁]; exact le_max_right _ _
        have hρ1 : R ≤ R₁ + n := by linarith
        have hρ2 : R₃ ≤ R₁ + n := by linarith
        obtain ⟨_, _, _, _, hIC', _⟩ := hinc' R (R₁ + n) hR hρ1
        have hI := hIC' rfl rfl hμν hne
        obtain ⟨hC3, _⟩ := habs' (R₁ + n) hρ2
        obtain ⟨_, hA⟩ := hC3 rfl rfl hμν
        have hI' : 𝓘 (R₁ + n) - 𝓘 R = c * (𝓑 (R₁ + n) - 𝓑 R) := by
          have := hI
          simp only [h𝓘, h𝓑]
          linear_combination this
        have hA' : 𝓘 (R₁ + n) = c₃ * 𝓑 (R₁ + n) := by
          have := hA
          simp only [h𝓘, h𝓑]
          linear_combination this
        linear_combination hI' - hA'
      have hEy : ‖Complex.exp Y‖ ≠ 1 := by
        rw [Complex.norm_exp]
        have hYre' : Y.re < 0 := by rw [hY, hs'def]; exact hYre
        have : Real.exp Y.re < 1 := Real.exp_lt_one_iff.mpr hYre'
        exact ne_of_lt this
      have hκ : 𝓘 R - c * 𝓑 R = 0 := by
        refine kappa_eq_zero c c₃ Y PC₁ QC₁ _ R₁ hEy fun n hn => ?_
        have := hkey n hn
        simp only [h𝓑] at this
        exact this

      have hIeq : Ifun s u = 𝓘 R := by
        simp only [hIfun, h𝓘, ← hs'def, hE1, hE2]
      have hPCeq : PCfun s u = PC₁ := by
        simp only [hPCfun, hPC₁, ← hs'def, hφ₁, hvC]
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hN2]
      have hQCeq : QCfun s u = QC₁ := by
        simp only [hQCfun, hQC₁, ← hs'def, hψ₁, hvC]
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hN1]
      have hy0 : Y ≠ 0 := by
        intro h0
        have hYre' : Y.re < 0 := by rw [hY, hs'def]; exact hYre
        rw [h0, Complex.zero_re] at hYre'
        exact lt_irrefl _ hYre'
      have h𝓑R : Y * 𝓑 R = PC₁ * Complex.exp ((R : ℂ) * Y) - QC₁ * Complex.exp (-((R : ℂ) * Y)) := by
        simp only [h𝓑]
        field_simp
      simp only [hKfun]
      rw [hIeq, hPCeq, hQCeq, hyu]
      have : 𝓘 R = c * 𝓑 R := by linear_combination hκ
      rw [this]
      linear_combination (c : ℂ) * h𝓑R

    have hvan := sesqui_identity_lt hOφ hOφc hOφhalf hOψ'o hOψ'c hOψ'h Kfun hK1 hK2 hK3
    have hK0 := hvan s₀ haxφ u₀ hu₀mem
    simp only [hKfun, hIfun, hPCfun, hQCfun] at hK0
    rw [hcu, sub_eq_zero] at hK0
    set II : ℂ := ∫ x in canonicalTruncationDomain F α β, TRUNC[R] (Eφ s₀) x *
      conj (TRUNC[R] (Eψ ((t' : ℂ) * Complex.I)) x) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with hII
    set PC : ℂ := ∫ k, φf s₀ (k : AdelicGL2 (𝓞 F) F) *
      conj (vC⁻¹ * Nψ ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hPC
    set QC : ℂ := ∫ k, (vC⁻¹ * Nφ s₀ (k : AdelicGL2 (𝓞 F) F)) *
      conj (ψf ((t' : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) with hQC
    have hgoal : II = (c : ℂ) * (PC * Complex.exp ((R : ℂ) * (s₀ - u₀)) / (s₀ - u₀)
        - QC * Complex.exp (-((R : ℂ) * (s₀ - u₀))) / (s₀ - u₀)) := by
      rw [show (c : ℂ) * (PC * Complex.exp ((R : ℂ) * (s₀ - u₀)) / (s₀ - u₀)
          - QC * Complex.exp (-((R : ℂ) * (s₀ - u₀))) / (s₀ - u₀))
          = ((c : ℂ) * (PC * Complex.exp ((R : ℂ) * (s₀ - u₀)) - QC * Complex.exp (-((R : ℂ) * (s₀ - u₀))))) / (s₀ - u₀)
          by field_simp, ← hK0, mul_div_cancel_left₀ _ hY0]
    exact hgoal
  ·

    refine ⟨hInt, ?_⟩
    have hK3 : ∀ s u : ℂ, 1 / 2 < s.re → s.re < u.re → Ifun s u = 0 := by
      intro s u hs hlt
      set s' : ℂ := conj u with hs'def
      obtain ⟨hs', hlt', -, -⟩ := wedge s u hs hlt
      set φ₁ : AdelicGL2 (𝓞 F) F → ℂ := φf s with hφ₁
      set ψ₁ : AdelicGL2 (𝓞 F) F → ℂ := ψf s' with hψ₁
      have hφ₁c : Continuous φ₁ := continuous_section F hφfjc s
      have hψ₁c : Continuous ψ₁ := continuous_section F hψfjc s'
      have hE1 : Eφ s = pseudoEisenstein F φ₁ := funext fun g => hEφeq s hs g
      have hE2 : Eψ s' = pseudoEisenstein F ψ₁ := funext fun g => hEψeq s' hs' g
      have hinc' := hinc μ ν μ' ν' hμ hν hμ' hν' hμF hνF hμ'F hν'F s s' hs hs' φ₁ (hφf s) hφ₁c (hφfK s) (hφff s)
        ψ₁ (hψf s') hψ₁c (hψfK s') (hψff s')
      have habs' := habs3 μ ν μ' ν' hμ hν hμ' hν' hμF hνF hμ'F hν'F s s' hs hs' hlt' φ₁ (hφf s) hφ₁c (hφfK s)
        (hφff s) ψ₁ (hψf s') hψ₁c (hψfK s') (hψff s')
      set 𝓘 : ℝ → ℂ := fun ρ => ∫ y in canonicalTruncationDomain F α β, TRUNC[ρ] (pseudoEisenstein F φ₁) y *
        conj (TRUNC[ρ] (pseudoEisenstein F ψ₁) y) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) with h𝓘
      set ρ : ℝ := max R R₃ with hρ
      have hρ1 : R ≤ ρ := le_max_left _ _
      have hρ2 : R₃ ≤ ρ := le_max_right _ _
      obtain ⟨_, _, _, _, _, hID'⟩ := hinc' R ρ hR hρ1
      have hI : 𝓘 ρ - 𝓘 R = 0 := by
        have := hID' hD1 hD2
        simp only [h𝓘]
        exact this
      obtain ⟨_, hD3⟩ := habs' ρ hρ2
      obtain ⟨_, hA⟩ := hD3 hD1 hD2
      have hA' : 𝓘 ρ = 0 := by
        simp only [h𝓘]
        exact hA
      have hIeq : Ifun s u = 𝓘 R := by
        simp only [hIfun, h𝓘, ← hs'def, hE1, hE2]
      rw [hIeq]
      linear_combination hA' - hI
    have hvan := sesqui_identity_lt hOφ hOφc hOφhalf hOψ'o hOψ'c hOψ'h Ifun hI1 hI2 hK3
    have hK0 := hvan s₀ haxφ u₀ hu₀mem
    simp only [hIfun] at hK0
    rw [hcu] at hK0
    exact hK0

end S_AutomorphicForm_exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_and_eq_twoTerm_and_eq_cross_and_eq_zero_two_pairs_slab_of_ne (solution)
