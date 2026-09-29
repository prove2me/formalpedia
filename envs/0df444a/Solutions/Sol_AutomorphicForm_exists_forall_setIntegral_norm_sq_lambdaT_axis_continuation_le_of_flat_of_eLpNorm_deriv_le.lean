-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c02af4e6-4d0b-5d54-ab0e-d11b76de5905

import Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat
import Theorems.Thm_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Liouville
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le
p2m_attr_erase "instance" "FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions"
p2m_attr_erase "instance" "instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv"
p2m_attr_erase "simp" "LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply LanglandsTunnell.TateLocal.conductorExponentAt_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

noncomputable section

namespace R4MsL2

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open Set Filter
open scoped ComplexConjugate Topology ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section General

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem integral_mul_conj_self_eq (f : X → ℂ) :
    ∫ k, f k * conj (f k) ∂m = ((∫ k, ‖f k‖ ^ 2 ∂m : ℝ) : ℂ) := by
  have h : ∀ k, f k * conj (f k) = ((‖f k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [h]
  exact integral_ofReal

theorem integrableOn_norm_sq_and_eq_re {S : Set X} {L : X → ℂ}
    (h : IntegrableOn (fun x => L x * conj (L x)) S m) :
    IntegrableOn (fun x => ‖L x‖ ^ 2) S m ∧
      ∫ x in S, ‖L x‖ ^ 2 ∂m = (∫ x in S, L x * conj (L x) ∂m).re := by
  have hpt : ∀ x, L x * conj (L x) = ((‖L x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hfun : (fun x => L x * conj (L x)) = fun x => ((‖L x‖ ^ 2 : ℝ) : ℂ) := funext hpt
  rw [hfun] at h
  refine ⟨?_, ?_⟩
  · have h2 := h.re
    refine h2.congr (ae_of_all _ fun x => ?_)
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
  · rw [hfun]
    have : (∫ x in S, ((‖L x‖ ^ 2 : ℝ) : ℂ) ∂m) = ((∫ x in S, ‖L x‖ ^ 2 ∂m : ℝ) : ℂ) :=
      integral_ofReal
    rw [this, Complex.ofReal_re]

theorem eLpNorm_two_eq_ofReal_sqrt {g : X → ℂ} (hg : MemLp g 2 m) :
    eLpNorm g 2 m = ENNReal.ofReal (Real.sqrt (∫ k, ‖g k‖ ^ 2 ∂m)) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  congr 1
  rw [ENNReal.toReal_ofNat, Real.sqrt_eq_rpow, one_div]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp [Real.rpow_two]

theorem sqrt_integral_norm_sq_le_of_eLpNorm_le {g : X → ℂ} (hg : MemLp g 2 m) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm g 2 m ≤ ENNReal.ofReal B) : Real.sqrt (∫ k, ‖g k‖ ^ 2 ∂m) ≤ B := by
  rw [eLpNorm_two_eq_ofReal_sqrt hg] at h
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h

theorem norm_integral_mul_conj_le {f g : X → ℂ} (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    ‖∫ k, f k * conj (g k) ∂m‖ ≤
      Real.sqrt (∫ k, ‖f k‖ ^ 2 ∂m) * Real.sqrt (∫ k, ‖g k‖ ^ 2 ∂m) := by
  have hf' : MemLp f (ENNReal.ofReal 2) m := by rw [ENNReal.ofReal_ofNat]; exact hf
  have hg' : MemLp g (ENNReal.ofReal 2) m := by rw [ENNReal.ofReal_ofNat]; exact hg
  have hH := integral_mul_norm_le_Lp_mul_Lq (μ := m) Real.HolderConjugate.two_two hf' hg'
  have h1 : (∫ k, ‖f k‖ ^ (2 : ℝ) ∂m) = ∫ k, ‖f k‖ ^ 2 ∂m :=
    integral_congr_ae (ae_of_all _ fun k => by simp [Real.rpow_two])
  have h2 : (∫ k, ‖g k‖ ^ (2 : ℝ) ∂m) = ∫ k, ‖g k‖ ^ 2 ∂m :=
    integral_congr_ae (ae_of_all _ fun k => by simp [Real.rpow_two])
  rw [h1, h2] at hH
  calc ‖∫ k, f k * conj (g k) ∂m‖
      ≤ ∫ k, ‖f k * conj (g k)‖ ∂m := norm_integral_le_integral_norm _
    _ = ∫ k, ‖f k‖ * ‖g k‖ ∂m := by
        congr 1; ext k; rw [norm_mul, RCLike.norm_conj]
    _ ≤ (∫ k, ‖f k‖ ^ 2 ∂m) ^ (1 / (2 : ℝ)) * (∫ k, ‖g k‖ ^ 2 ∂m) ^ (1 / (2 : ℝ)) := hH
    _ = Real.sqrt (∫ k, ‖f k‖ ^ 2 ∂m) * Real.sqrt (∫ k, ‖g k‖ ^ 2 ∂m) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

theorem integral_norm_sq_eq_of {f : X → ℂ} {P : ℝ}
    (hf : ∫ k, f k * conj (f k) ∂m = (P : ℂ)) : ∫ k, ‖f k‖ ^ 2 ∂m = P := by
  rw [integral_mul_conj_self_eq] at hf
  exact_mod_cast hf

end General

variable (F : Type) [Field F] [NumberField F]

theorem memLp_two_of_continuous {f : adelicMaximalCompact F → ℂ} (hf : Continuous f) :
    MemLp f 2 (maximalCompactHaar F) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := adelicMaximalCompact F)).exists_bound_of_continuousOn
    hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => hC x (mem_univ _))

theorem continuous_eval_coe (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)) (s : ℂ) :
    Continuous fun k : adelicMaximalCompact F => φ s (k : AdelicGL2 (𝓞 F) F) :=
  hφ.comp (continuous_const.prodMk continuous_subtype_val)

theorem continuous_eval_coe_of_continuousOn {O : Set ℂ} (N : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hN : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => N p.1 p.2) (O ×ˢ univ)) {s : ℂ} (hs : s ∈ O)
    (c : ℂ) :
    Continuous fun k : adelicMaximalCompact F => (fun g => c * N s g) (k : AdelicGL2 (𝓞 F) F) := by
  have h : Continuous fun k : adelicMaximalCompact F => N s (k : AdelicGL2 (𝓞 F) F) :=
    hN.comp_continuous (continuous_const.prodMk continuous_subtype_val) fun k => ⟨hs, mem_univ _⟩
  exact continuous_const.mul h

theorem axis_mem {O : Set ℂ} (hO : {s : ℂ | s.re = 0} ⊆ O) (t : ℝ) : (t : ℂ) * Complex.I ∈ O :=
  hO (by simp [Complex.mul_re])

theorem stronglyMeasurable_deriv_eval {O : Set ℂ} (hO : IsOpen O) (N : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hNa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => N s g) O)
    (hNc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => N p.1 p.2) (O ×ˢ univ))
    {s₀ : ℂ} (hs₀ : s₀ ∈ O) (c : ℂ) :
    StronglyMeasurable fun k : adelicMaximalCompact F =>
      c * deriv (fun s : ℂ => N s (k : AdelicGL2 (𝓞 F) F)) s₀ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO s₀ hs₀

  set h : ℕ → ℂ := fun n => ((δ / ((n : ℝ) + 2) : ℝ) : ℂ) with hh
  have hpos : ∀ n : ℕ, 0 < δ / ((n : ℝ) + 2) := fun n => by positivity
  have hne : ∀ n, h n ≠ 0 := fun n => by
    simp only [hh, ne_eq, Complex.ofReal_eq_zero]
    exact (hpos n).ne'
  have hlt : ∀ n, ‖h n‖ < δ := fun n => by
    simp only [hh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hmem : ∀ n, s₀ + h n ∈ O := fun n => hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hlt n)
  have hlim : Tendsto h atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop this
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
    rw [Complex.ofReal_zero] at h2
    exact h2
  have hlim' : Tendsto h atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hne n⟩

  set f : ℕ → adelicMaximalCompact F → ℂ := fun n k =>
    c * ((h n)⁻¹ • (N (s₀ + h n) (k : AdelicGL2 (𝓞 F) F) - N s₀ (k : AdelicGL2 (𝓞 F) F))) with hf
  have hfc : ∀ n, StronglyMeasurable (f n) := by
    intro n
    have h1 : Continuous fun k : adelicMaximalCompact F => N (s₀ + h n) (k : AdelicGL2 (𝓞 F) F) :=
      hNc.comp_continuous (continuous_const.prodMk continuous_subtype_val) fun k => ⟨hmem n, mem_univ _⟩
    have h2 : Continuous fun k : adelicMaximalCompact F => N s₀ (k : AdelicGL2 (𝓞 F) F) :=
      hNc.comp_continuous (continuous_const.prodMk continuous_subtype_val) fun k => ⟨hs₀, mem_univ _⟩
    exact (continuous_const.fun_mul (continuous_const.fun_smul (h1.fun_sub h2))).stronglyMeasurable
  refine stronglyMeasurable_of_tendsto atTop hfc (tendsto_pi_nhds.2 fun k => ?_)
  have hd : HasDerivAt (fun s : ℂ => N s (k : AdelicGL2 (𝓞 F) F))
      (deriv (fun s : ℂ => N s (k : AdelicGL2 (𝓞 F) F)) s₀) s₀ :=
    ((hNa (k : AdelicGL2 (𝓞 F) F) s₀ hs₀).differentiableAt).hasDerivAt
  have hsl := (hasDerivAt_iff_tendsto_slope_zero.1 hd).comp hlim'
  exact tendsto_const_nhds.mul hsl

theorem osc_eq (z e : ℂ) (t : ℝ) (ht : t ≠ 0) :
    z * e / (2 * Complex.I * (t : ℂ)) - conj z * conj e / (2 * Complex.I * (t : ℂ)) =
      (((z * e).im / t : ℝ) : ℂ) := by
  have hI : (2 * Complex.I * (t : ℂ)) ≠ 0 := by
    simp [ht, Complex.I_ne_zero]
  rw [← sub_div, ← map_mul, Complex.sub_conj, Complex.ofReal_div]
  field_simp
  push_cast
  ring

theorem norm_diag_rhs_le {P₁ D z z' e e' : ℂ} {P B₁ B₂ R t : ℝ} (ht : t ≠ 0) (hP : 0 ≤ P)
    (hB₂ : 0 ≤ B₂)
    (hP₁ : P₁ = (P : ℂ)) (hD : ‖D‖ ≤ Real.sqrt P * B₁) (hz' : z' = conj z) (he' : e' = conj e)
    (he : ‖e‖ = 1) (hz : ‖z‖ ≤ P)
    (hsmall : |t| < 1 → |(z * e).im| ≤ (B₂ + 2 * |R| * P) * |t|) :
    ‖P₁ * (2 * (R : ℂ)) - D + z * e / (2 * Complex.I * (t : ℂ)) - z' * e' / (2 * Complex.I * (t : ℂ))‖ ≤
      (4 * |R| + 1) * P + Real.sqrt P * B₁ + B₂ := by
  have hosc : ‖z * e / (2 * Complex.I * (t : ℂ)) - z' * e' / (2 * Complex.I * (t : ℂ))‖ ≤
      P + B₂ + 2 * |R| * P := by
    rw [hz', he', osc_eq z e t ht, Complex.norm_real, Real.norm_eq_abs, abs_div]
    have htpos : 0 < |t| := abs_pos.2 ht
    rw [div_le_iff₀ htpos]
    by_cases hlt : |t| < 1
    · have h1 := hsmall hlt
      have hRP : 0 ≤ 2 * |R| * P := by positivity
      nlinarith
    · push Not at hlt
      have h1 : |(z * e).im| ≤ P := by
        calc |(z * e).im| ≤ ‖z * e‖ := Complex.abs_im_le_norm _
          _ = ‖z‖ := by rw [norm_mul, he, mul_one]
          _ ≤ P := hz
      have hRP : 0 ≤ 2 * |R| * P := by positivity
      nlinarith
  have hslope : ‖P₁ * (2 * (R : ℂ))‖ = 2 * |R| * P := by
    rw [hP₁, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP]
    have : ‖(2 : ℂ) * (R : ℂ)‖ = 2 * |R| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [this]; ring
  calc ‖P₁ * (2 * (R : ℂ)) - D + z * e / (2 * Complex.I * (t : ℂ)) - z' * e' / (2 * Complex.I * (t : ℂ))‖
      = ‖(P₁ * (2 * (R : ℂ)) - D) +
          (z * e / (2 * Complex.I * (t : ℂ)) - z' * e' / (2 * Complex.I * (t : ℂ)))‖ := by ring_nf
    _ ≤ ‖P₁ * (2 * (R : ℂ)) - D‖ +
          ‖z * e / (2 * Complex.I * (t : ℂ)) - z' * e' / (2 * Complex.I * (t : ℂ))‖ := norm_add_le _ _
    _ ≤ (‖P₁ * (2 * (R : ℂ))‖ + ‖D‖) + (P + B₂ + 2 * |R| * P) :=
        add_le_add (norm_sub_le _ _) hosc
    _ ≤ (2 * |R| * P + Real.sqrt P * B₁) + (P + B₂ + 2 * |R| * P) := by rw [hslope]; linarith
    _ = (4 * |R| + 1) * P + Real.sqrt P * B₁ + B₂ := by ring

theorem norm_offdiag_rhs_le {P₁ D : ℂ} {P B₁ B₂ R : ℝ} (hP : 0 ≤ P) (hB₂ : 0 ≤ B₂)
    (hP₁ : P₁ = (P : ℂ)) (hD : ‖D‖ ≤ Real.sqrt P * B₁) :
    ‖P₁ * (2 * (R : ℂ)) - D‖ ≤ (4 * |R| + 1) * P + Real.sqrt P * B₁ + B₂ := by
  have hslope : ‖P₁ * (2 * (R : ℂ))‖ = 2 * |R| * P := by
    rw [hP₁, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP]
    have : ‖(2 : ℂ) * (R : ℂ)‖ = 2 * |R| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; norm_num
    rw [this]; ring
  have hRP : 0 ≤ |R| * P := by positivity
  calc ‖P₁ * (2 * (R : ℂ)) - D‖ ≤ ‖P₁ * (2 * (R : ℂ))‖ + ‖D‖ := norm_sub_le _ _
    _ ≤ 2 * |R| * P + Real.sqrt P * B₁ := by rw [hslope]; linarith
    _ ≤ (4 * |R| + 1) * P + Real.sqrt P * B₁ + B₂ := by nlinarith

theorem exp_facts (R t : ℝ) :
    ‖Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ))‖ = 1 ∧
    Complex.exp (-(2 * Complex.I * (R : ℂ) * (t : ℂ))) = conj (Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ))) ∧
    |(Complex.exp (2 * Complex.I * (R : ℂ) * (t : ℂ))).im| ≤ 2 * |R| * |t| := by
  have hre : (2 * Complex.I * (R : ℂ) * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have him : (2 * Complex.I * (R : ℂ) * (t : ℂ)).im = 2 * R * t := by
    simp [Complex.mul_re, Complex.mul_im]
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.norm_exp, hre, Real.exp_zero]
  · rw [← Complex.exp_conj]
    congr 1
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im]
  · rw [Complex.exp_im, hre, him, Real.exp_zero, one_mul]
    calc |Real.sin (2 * R * t)| ≤ |2 * R * t| := Real.abs_sin_le_abs
      _ = 2 * |R| * |t| := by rw [abs_mul, abs_mul]; norm_num

theorem abs_im_mul_le {z z₀ e : ℂ} {P B₂ R t : ℝ}
    (hlip : ‖z - z₀‖ ≤ B₂ * |t|) (hz₀ : z₀.im = 0) (hz₀P : ‖z₀‖ ≤ P) (he : ‖e‖ = 1)
    (heim : |e.im| ≤ 2 * |R| * |t|) :
    |(z * e).im| ≤ (B₂ + 2 * |R| * P) * |t| := by
  have hsplit : z * e = (z - z₀) * e + z₀ * e := by ring
  rw [hsplit, Complex.add_im]
  have h1 : |((z - z₀) * e).im| ≤ B₂ * |t| := by
    calc |((z - z₀) * e).im| ≤ ‖(z - z₀) * e‖ := Complex.abs_im_le_norm _
      _ = ‖z - z₀‖ := by rw [norm_mul, he, mul_one]
      _ ≤ B₂ * |t| := hlip
  have h2 : |(z₀ * e).im| ≤ P * (2 * |R| * |t|) := by
    have : (z₀ * e).im = z₀.re * e.im := by rw [Complex.mul_im, hz₀, zero_mul, add_zero]
    rw [this, abs_mul]
    have hre : |z₀.re| ≤ P := (Complex.abs_re_le_norm z₀).trans hz₀P
    exact mul_le_mul hre heim (abs_nonneg _) ((abs_nonneg _).trans hre)
  calc |((z - z₀) * e).im + (z₀ * e).im| ≤ |((z - z₀) * e).im| + |(z₀ * e).im| := abs_add_le _ _
    _ ≤ B₂ * |t| + P * (2 * |R| * |t|) := add_le_add h1 h2
    _ = (B₂ + 2 * |R| * P) * |t| := by ring

section Reality

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem re_setIntegral_mul_conj_self_nonneg {S : Set X} {L : X → ℂ}
    (h : IntegrableOn (fun x => L x * conj (L x)) S m) :
    0 ≤ (∫ x in S, L x * conj (L x) ∂m).re := by
  rw [← (integrableOn_norm_sq_and_eq_re h).2]
  exact integral_nonneg fun x => by positivity

end Reality

theorem neg_le_im_div_of_re_nonneg {P₁ D z z' e e' : ℂ} {P R c₀ t CX : ℝ} (ht : t ≠ 0) (hc₀ : 0 < c₀)
    (hP : 0 ≤ P) (hP₁ : P₁ = (P : ℂ)) (hz' : z' = conj z) (he' : e' = conj e) (hD : ‖D‖ ≤ CX)
    (h : 0 ≤ ((c₀ : ℂ) * (P₁ * (2 * (R : ℂ)) - D + z * e / (2 * Complex.I * (t : ℂ)) -
      z' * e' / (2 * Complex.I * (t : ℂ)))).re) :
    -(CX + 2 * |R| * P) ≤ (z * e).im / t := by
  have hassoc : P₁ * (2 * (R : ℂ)) - D + z * e / (2 * Complex.I * (t : ℂ)) -
      z' * e' / (2 * Complex.I * (t : ℂ)) =
      (P₁ * (2 * (R : ℂ)) - D) +
        (z * e / (2 * Complex.I * (t : ℂ)) - conj z * conj e / (2 * Complex.I * (t : ℂ))) := by
    rw [hz', he']; ring
  rw [hassoc, osc_eq z e t ht, hP₁] at h
  have hw : (P : ℂ) * (2 * (R : ℂ)) - D + (((z * e).im / t : ℝ) : ℂ) =
      ((P * (2 * R) + (z * e).im / t : ℝ) : ℂ) - D := by
    push_cast; ring
  have hre : ((c₀ : ℂ) * (((P * (2 * R) + (z * e).im / t : ℝ) : ℂ) - D)).re =
      c₀ * ((P * (2 * R) + (z * e).im / t) - D.re) := by
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  have h' : 0 ≤ c₀ * ((P * (2 * R) + (z * e).im / t) - D.re) := by
    rw [hw, hre] at h
    exact h
  have h2 : 0 ≤ (P * (2 * R) + (z * e).im / t) - D.re := by
    by_contra hcon
    push Not at hcon
    have : c₀ * ((P * (2 * R) + (z * e).im / t) - D.re) < 0 := mul_neg_of_pos_of_neg hc₀ hcon
    linarith
  have hDre : -CX ≤ D.re := by
    have h3 : |D.re| ≤ ‖D‖ := Complex.abs_re_le_norm D
    have h4 := (abs_le.1 (h3.trans hD)).1
    linarith
  have hRP : P * (2 * R) ≤ 2 * |R| * P := by
    have : R ≤ |R| := le_abs_self R
    nlinarith
  linarith

theorem eq_zero_of_tendsto_of_bounds {g : ℝ → ℝ} {y₀ C r : ℝ} (hr : 0 < r)
    (hg : Tendsto g (𝓝 0) (𝓝 y₀))
    (hpos : ∀ t : ℝ, 0 < t → t ≤ r → -C * t ≤ g t)
    (hneg : ∀ t : ℝ, t < 0 → -r ≤ t → g t ≤ -C * t) : y₀ = 0 := by
  have hlin : Tendsto (fun t : ℝ => -C * t) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => -C * t := continuous_const.mul continuous_id
    simpa using hc.tendsto 0
  have h1 : 0 ≤ y₀ := by
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] (0 : ℝ)) (hlin.mono_left nhdsWithin_le_nhds)
      (hg.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iic_mem_nhds hr)] with t ht ht'
    exact hpos t ht ht'
  have h2 : y₀ ≤ 0 := by
    refine le_of_tendsto_of_tendsto (b := 𝓝[<] (0 : ℝ)) (hg.mono_left nhdsWithin_le_nhds)
      (hlin.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ici_mem_nhds (neg_lt_zero.2 hr))]
      with t ht ht'
    exact hneg t ht ht'
  linarith

theorem exists_bound_integral_mul_conj_deriv {O : Set ℂ} (hO : IsOpen O) (h0 : (0 : ℂ) ∈ O)
    (N : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hNa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => N s g) O)
    (hNc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => N p.1 p.2) (O ×ˢ univ)) (cN : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ t : ℝ, |t| ≤ r →
      ‖∫ k, (fun g => cN * N ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
          conj ((fun g => cN * deriv (fun s : ℂ => N s g) ((t : ℂ) * Complex.I))
            (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F)‖ ≤ C := by
  obtain ⟨ρ, hρ, hballO⟩ := Metric.isOpen_iff.1 hO 0 h0
  set r : ℝ := ρ / 3 with hr_def
  have hr : 0 < r := by positivity
  have hcb : Metric.closedBall (0 : ℂ) (2 * r) ⊆ O := fun z hz => hballO (by
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have : 2 * r < ρ := by rw [hr_def]; linarith
    linarith)

  have hK : IsCompact ((Metric.closedBall (0 : ℂ) (2 * r)) ×ˢ (univ : Set (adelicMaximalCompact F))) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  have hfc : ContinuousOn (fun p : ℂ × adelicMaximalCompact F => N p.1 (p.2 : AdelicGL2 (𝓞 F) F))
      ((Metric.closedBall (0 : ℂ) (2 * r)) ×ˢ (univ : Set (adelicMaximalCompact F))) := by
    have hcont : Continuous (fun p : ℂ × adelicMaximalCompact F =>
        ((p.1, (p.2 : AdelicGL2 (𝓞 F) F)) : ℂ × AdelicGL2 (𝓞 F) F)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    refine hNc.comp hcont.continuousOn ?_
    intro p hp
    exact ⟨hcb hp.1, mem_univ _⟩
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hfc
  have hN : ∀ z ∈ Metric.closedBall (0 : ℂ) (2 * r), ∀ k : adelicMaximalCompact F,
      ‖N z (k : AdelicGL2 (𝓞 F) F)‖ ≤ C₀ :=
    fun z hz k => hC₀ (z, k) ⟨hz, mem_univ _⟩
  refine ⟨r, hr, ‖cN‖ * C₀ * (‖cN‖ * (C₀ / r)), fun t ht => ?_⟩
  have htI : ‖(t : ℂ) * Complex.I‖ = |t| := by simp
  have hmem0 : (t : ℂ) * Complex.I ∈ Metric.closedBall (0 : ℂ) (2 * r) := by
    rw [Metric.mem_closedBall, dist_zero_right, htI]; linarith
  have hsub : Metric.closedBall ((t : ℂ) * Complex.I) r ⊆ Metric.closedBall (0 : ℂ) (2 * r) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ = ‖(z - (t : ℂ) * Complex.I) + (t : ℂ) * Complex.I‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (t : ℂ) * Complex.I‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ r + |t| := by rw [htI]; exact add_le_add hz le_rfl
      _ ≤ 2 * r := by linarith
  have hderiv : ∀ k : adelicMaximalCompact F,
      ‖deriv (fun s : ℂ => N s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)‖ ≤ C₀ / r := by
    intro k
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ ?_
    · exact (hNa (k : AdelicGL2 (𝓞 F) F)).differentiableOn.diffContOnCl_ball (hsub.trans hcb)
    · intro z hz
      exact hN z (hsub (Metric.sphere_subset_closedBall hz)) k
  have hC₀nn : 0 ≤ C₀ := (norm_nonneg _).trans (hN _ hmem0 1)
  have hpt : ∀ k : adelicMaximalCompact F,
      ‖(fun g => cN * N ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
          conj ((fun g => cN * deriv (fun s : ℂ => N s g) ((t : ℂ) * Complex.I))
            (k : AdelicGL2 (𝓞 F) F))‖ ≤ ‖cN‖ * C₀ * (‖cN‖ * (C₀ / r)) := by
    intro k
    rw [norm_mul, RCLike.norm_conj, norm_mul, norm_mul]
    have h1 := hN _ hmem0 k
    have h2 := hderiv k
    have hcN := norm_nonneg cN
    have hA : ‖cN‖ * ‖N ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ≤ ‖cN‖ * C₀ :=
      mul_le_mul_of_nonneg_left h1 hcN
    have hB : ‖cN‖ * ‖deriv (fun s : ℂ => N s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)‖ ≤
        ‖cN‖ * (C₀ / r) := mul_le_mul_of_nonneg_left h2 hcN
    exact mul_le_mul hA hB (by positivity) (by positivity)
  have hint := norm_integral_le_of_norm_le_const (μ := maximalCompactHaar F) (ae_of_all _ hpt)
  simpa only [probReal_univ, mul_one] using hint

end R4MsL2

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain AutomorphicForm
open Filter
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F))
    (𝔑 : Ideal (𝓞 F)) (_h𝔑 : 𝔑 ≠ ⊥) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧ ∃ R₀ : ℝ,
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hpair : μ = ν ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles F, μ z ≠ ν z)
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        φf s (k : AdelicGL2 (𝓞 F) F) = φf 0 (k : AdelicGL2 (𝓞 F) F))
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F 𝔑 ⊓ finiteAdelicGL2Subgroup F, φf s (g * u) = φf s g)
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
      (t : ℝ) (_ht : t ≠ 0) (R : ℝ) (_hR : R₀ ≤ R)
      (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
      (_hderiv : eLpNorm (fun k : adelicMaximalCompact F =>
          ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
            deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I))
        2 (AutomorphicForm.maximalCompactHaar F) ≤ ENNReal.ofReal B₁)
      (_hlip : ∀ s : ℝ, |s| ≤ 1 →
        ‖(∫ k, φf ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
              conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((s : ℂ) * Complex.I) g)
                (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)) -
          (∫ k, φf 0 (k : AdelicGL2 (𝓞 F) F) *
              conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ 0 g)
                (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F))‖ ≤ B₂ * |s|),
      IntegrableOn (fun x : AdelicGL2 (𝓞 F) F =>
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Eφ ((t : ℂ) * Complex.I)) x‖ ^ 2)
        (AutomorphicForm.canonicalTruncationDomain F α β) (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      ∫ x in AutomorphicForm.canonicalTruncationDomain F α β,
          ‖@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Eφ ((t : ℂ) * Complex.I)) x‖ ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ≤
        c * ((|R| + 1) * (∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F)) +
          Real.sqrt (∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F)) * B₁ + B₂) := by
  intro αm hαm
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F

  obtain ⟨c₀, hc₀, R₀, hMS⟩ :=
    AutomorphicForm.exists_forall_integrableOn_and_setIntegral_lambdaT_axis_continuation_mul_conj_eq_maassSelberg_or_twoTerm_slab_of_flat
      F α β hα hαβ ΦF hαm
  refine ⟨4 * c₀, by positivity, R₀, ?_⟩
  intro μ ν hμ hν hμF hνF hμk hνk hpair φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat hφflev Oφ Eφ Nφ hEφ
    t ht R hR B₁ B₂ hB₁ hB₂ hderiv hlip
  obtain ⟨hint, hdiag, hoff⟩ := hMS μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat
    φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat Oφ Eφ Nφ hEφ Oφ Eφ Nφ hEφ t ht R hR
  obtain ⟨hI, hre⟩ := R4MsL2.integrableOn_norm_sq_and_eq_re hint
  refine ⟨hI, ?_⟩
  rw [hre]

  set cN : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ with hcN_def
  set P : ℝ := ∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F) with hP_def
  have hP : 0 ≤ P := integral_nonneg fun k => by positivity
  have hax : ∀ s : ℝ, (s : ℂ) * Complex.I ∈ Oφ := fun s => R4MsL2.axis_mem hEφ.2.2.1 s

  have hφc : ∀ s : ℂ, Continuous fun k : AutomorphicForm.adelicMaximalCompact F =>
      φf s (k : AdelicGL2 (𝓞 F) F) := fun s => R4MsL2.continuous_eval_coe F φf hφfjc s
  have hMc : ∀ s : ℝ, Continuous fun k : AutomorphicForm.adelicMaximalCompact F =>
      (fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) := fun s =>
    R4MsL2.continuous_eval_coe_of_continuousOn F Nφ hEφ.2.2.2.2.2.2.2.1 (hax s) cN

  have hφP : ∀ s : ℂ, ∫ k, φf s (k : AdelicGL2 (𝓞 F) F) * conj (φf s (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) = (P : ℂ) := by
    intro s
    rw [hP_def, ← R4MsL2.integral_mul_conj_self_eq]
    congr 1; ext k; rw [hφflat s k]
  have hφP' : ∀ s : ℂ, ∫ k, ‖φf s (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F) = P :=
    fun s => R4MsL2.integral_norm_sq_eq_of (hφP s)

  have hunit : ∀ s : ℝ,
      (∫ k, (fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
          conj ((fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
        ∂(AutomorphicForm.maximalCompactHaar F)) = (P : ℂ) := by
    intro s
    rw [← hφP ((s : ℂ) * Complex.I)]
    exact
      AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
        F hαm μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu φf hφf hφfK hφff hφfjc hφfhol
        hφfKu Oφ Eφ Nφ hEφ Oφ Eφ Nφ hEφ s
  have hMP : ∀ s : ℝ, ∫ k, ‖(fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F)‖ ^ 2
      ∂(AutomorphicForm.maximalCompactHaar F) = P := fun s => R4MsL2.integral_norm_sq_eq_of (hunit s)

  have hφL2 : ∀ s : ℂ, MemLp (fun k : AutomorphicForm.adelicMaximalCompact F => φf s (k : AdelicGL2 (𝓞 F) F))
      2 (AutomorphicForm.maximalCompactHaar F) := fun s => R4MsL2.memLp_two_of_continuous F (hφc s)
  have hML2 : ∀ s : ℝ, MemLp (fun k : AutomorphicForm.adelicMaximalCompact F =>
      (fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
      2 (AutomorphicForm.maximalCompactHaar F) := fun s => R4MsL2.memLp_two_of_continuous F (hMc s)
  have hDmeas : AEStronglyMeasurable (fun k : AutomorphicForm.adelicMaximalCompact F =>
      cN * deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I))
      (AutomorphicForm.maximalCompactHaar F) :=
    (R4MsL2.stronglyMeasurable_deriv_eval F hEφ.1 Nφ hEφ.2.2.2.2.2.1 hEφ.2.2.2.2.2.2.2.1 (hax t)
      cN).aestronglyMeasurable
  have hDL2 : MemLp (fun k : AutomorphicForm.adelicMaximalCompact F =>
      cN * deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I))
      2 (AutomorphicForm.maximalCompactHaar F) :=
    ⟨hDmeas, lt_of_le_of_lt hderiv ENNReal.ofReal_lt_top⟩

  have hD : ‖∫ k, (fun g => cN * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => cN * deriv (fun s : ℂ => Nφ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F)‖ ≤ Real.sqrt P * B₁ := by
    have h1 := R4MsL2.norm_integral_mul_conj_le (hML2 t) hDL2
    rw [hMP t] at h1
    have h2 := R4MsL2.sqrt_integral_norm_sq_le_of_eLpNorm_le hDL2 hB₁ hderiv
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))

  have hzP : ∀ s : ℝ, ‖∫ k, φf ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F)‖ ≤ P := by
    intro s
    have h1 := R4MsL2.norm_integral_mul_conj_le (hφL2 ((s : ℂ) * Complex.I)) (hML2 s)
    rw [hφP' ((s : ℂ) * Complex.I), hMP s, Real.mul_self_sqrt hP] at h1
    exact h1

  have hfin : ∀ X : ℂ, ‖X‖ ≤ (4 * |R| + 1) * P + Real.sqrt P * B₁ + B₂ →
      ((c₀ : ℂ) * X).re ≤ 4 * c₀ * ((|R| + 1) * P + Real.sqrt P * B₁ + B₂) := by
    intro X hX
    have h1 : ((c₀ : ℂ) * X).re ≤ ‖(c₀ : ℂ) * X‖ := Complex.re_le_norm _
    have h2 : ‖(c₀ : ℂ) * X‖ = c₀ * ‖X‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₀]
    have hsq : 0 ≤ Real.sqrt P * B₁ := by positivity
    have h3 : (4 * |R| + 1) * P + Real.sqrt P * B₁ + B₂ ≤ 4 * ((|R| + 1) * P + Real.sqrt P * B₁ + B₂) := by
      nlinarith [abs_nonneg R]
    calc ((c₀ : ℂ) * X).re ≤ c₀ * ‖X‖ := h2 ▸ h1
      _ ≤ c₀ * ((4 * |R| + 1) * P + Real.sqrt P * B₁ + B₂) := mul_le_mul_of_nonneg_left hX hc₀.le
      _ ≤ c₀ * (4 * ((|R| + 1) * P + Real.sqrt P * B₁ + B₂)) := mul_le_mul_of_nonneg_left h3 hc₀.le
      _ = 4 * c₀ * ((|R| + 1) * P + Real.sqrt P * B₁ + B₂) := by ring
  rcases hpair with hμν | hoffd
  ·
    rw [hdiag hμν]
    apply hfin
    obtain ⟨he1, he', heim⟩ := R4MsL2.exp_facts R t
    set z₀ : ℂ := ∫ k, φf 0 (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => cN * Nφ 0 g) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
      with hz₀_def

    have hO0 : (0 : ℂ) ∈ Oφ := by simpa using hax 0
    obtain ⟨r₁, hr₁, CX, hCX⟩ := R4MsL2.exists_bound_integral_mul_conj_deriv F hEφ.1 hO0 Nφ
      hEφ.2.2.2.2.2.1 hEφ.2.2.2.2.2.2.2.1 cN

    obtain ⟨gim, hgim⟩ : ∃ gim : ℝ → ℝ, ∀ s : ℝ, gim s =
        ((∫ k, φf ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
            conj ((fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
              ∂(AutomorphicForm.maximalCompactHaar F)) *
          Complex.exp (2 * Complex.I * (R : ℂ) * (s : ℂ))).im := ⟨_, fun _ => rfl⟩

    have hq : ∀ s : ℝ, s ≠ 0 → |s| ≤ r₁ → -(CX + 2 * |R| * P) ≤ gim s / s := by
      intro s hs hsr
      obtain ⟨hint', hdiag', -⟩ := hMS μ ν hμ hν hμF hνF hμk hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu
        hφflat φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat Oφ Eφ Nφ hEφ Oφ Eφ Nφ hEφ s hs R hR
      have h0 := R4MsL2.re_setIntegral_mul_conj_self_nonneg hint'
      rw [hdiag' hμν] at h0
      obtain ⟨-, he'', -⟩ := R4MsL2.exp_facts R s
      have hzconj : (∫ k, (fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
            conj (φf ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F))
            ∂(AutomorphicForm.maximalCompactHaar F)) =
          conj (∫ k, φf ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
            conj ((fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
            ∂(AutomorphicForm.maximalCompactHaar F)) := by
        rw [← integral_conj]
        congr 1; ext k
        simp only [map_mul, RCLike.conj_conj, mul_comm]
      rw [hgim]
      exact R4MsL2.neg_le_im_div_of_re_nonneg hs hc₀ hP (hφP _) hzconj he'' (hCX s hsr) h0

    have ha : Tendsto (fun s : ℝ => ∫ k, φf ((s : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => cN * Nφ ((s : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F))
          ∂(AutomorphicForm.maximalCompactHaar F)) (𝓝 0) (𝓝 z₀) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      refine squeeze_zero' (g := fun s : ℝ => B₂ * |s|) (Eventually.of_forall fun s => norm_nonneg _) ?_ ?_
      · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with s hs
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
        exact hlip s hs.le
      · have hc : Continuous fun s : ℝ => B₂ * |s| := continuous_const.mul continuous_abs
        simpa using hc.tendsto 0
    have hexp : Tendsto (fun s : ℝ => Complex.exp (2 * Complex.I * (R : ℂ) * (s : ℂ))) (𝓝 0) (𝓝 1) := by
      have hc : Continuous fun s : ℝ => Complex.exp (2 * Complex.I * (R : ℂ) * (s : ℂ)) :=
        Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
      simpa using hc.tendsto 0
    have hgt : Tendsto gim (𝓝 0) (𝓝 z₀.im) := by
      have h1 := ha.mul hexp
      rw [mul_one] at h1
      have h2 := (Complex.continuous_im.tendsto z₀).comp h1
      exact h2.congr fun s => (hgim s).symm

    have hz₀real : z₀.im = 0 := by
      refine R4MsL2.eq_zero_of_tendsto_of_bounds (C := CX + 2 * |R| * P) hr₁ hgt ?_ ?_
      · intro s hs hsr
        have h := hq s hs.ne' (by rwa [abs_of_pos hs])
        exact (le_div_iff₀ hs).1 h
      · intro s hs hsr
        have h := hq s hs.ne (by rw [abs_of_neg hs]; linarith)
        exact (le_div_iff_of_neg hs).1 h
    have hz₀P : ‖z₀‖ ≤ P := by
      have h := hzP 0
      simp only [Complex.ofReal_zero, zero_mul] at h
      exact h
    refine R4MsL2.norm_diag_rhs_le ht hP hB₂ (hφP _) hD ?_ he' he1 (hzP t) ?_
    · rw [← integral_conj]
      congr 1; ext k
      simp only [map_mul, RCLike.conj_conj, mul_comm]
    · intro hlt
      refine R4MsL2.abs_im_mul_le (hlip t hlt.le) hz₀real hz₀P he1 heim
  ·
    rw [hoff hoffd]
    apply hfin
    exact R4MsL2.norm_offdiag_rhs_le hP hB₂ (hφP _) hD

end S_AutomorphicForm_exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_norm_sq_lambdaT_axis_continuation_le_of_flat_of_eLpNorm_deriv_le (solution)
