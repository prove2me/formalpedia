-- Prove2me | solution 1 for AutomorphicForm.exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/aa4f2398-fba9-5364-a8f9-41e382035d9b

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_AutomorphicForm_exists_localComponents_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_tprod_inv_eulerFactor_mul_tprod_eulerFactor_eq_prod_sdiff_of_norm_le_one
import Theorems.Thm_AutomorphicForm_continuous_of_isInducedSection_of_continuous_of_apply_ne_zero
import Theorems.Thm_AutomorphicForm_RealIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay
import Theorems.Thm_AutomorphicForm_continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family_of_unitary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "instance" "HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq"
p2m_attr_erase "simp" "SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

namespace T1Helpers

section B2

open MeasureTheory NumberField.InfinitePlace

variable (F : Type) [Field F] [NumberField F]

private theorem extensionEmbedding_eq_ofReal_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    Completion.extensionEmbedding w x = ((Completion.extensionEmbeddingOfIsReal hw x : ℝ) : ℂ) := by
  have h1 : Continuous fun x : w.Completion => Completion.extensionEmbedding w x :=
    (Completion.isometry_extensionEmbedding w).continuous
  have h2 : Continuous fun x : w.Completion => ((Completion.extensionEmbeddingOfIsReal hw x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  induction x using NumberField.InfinitePlace.Completion.induction_on with
  | hp => exact isClosed_eq h1 h2
  | ih y =>
    rw [Completion.extensionEmbedding_coe, Completion.extensionEmbeddingOfIsReal_coe, embedding_of_isReal_apply]

private theorem norm_eq_norm_extensionEmbedding (w : InfinitePlace F) (x : w.Completion) :
    ‖x‖ = ‖Completion.extensionEmbedding w x‖ :=
  ((Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x).symm

private theorem norm_fst_apply_of_extensionEmbedding_eq (z : AdeleRing (𝓞 F) F) (r : ℝ) (hr : 0 < r)
    (hz : ∀ w : InfinitePlace F, Completion.extensionEmbedding w (z.1 w) = (r : ℂ)) (w : InfinitePlace F) :
    ‖z.1 w‖ = r := by
  rw [norm_eq_norm_extensionEmbedding, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

private theorem distribHaarChar_eq_pow_of_dilation (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ) (hr : 0 < r)
    (hz2 : (z : AdeleRing (𝓞 F) F).2 = 1)
    (hz1 : ∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) :
    ((distribHaarChar (AdeleRing (𝓞 F) F) z : NNReal) : ℝ) = r ^ Module.finrank ℚ F := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(z : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    intro v
    rw [hz2, show (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v = 1 from rfl, norm_one]
  rw [finprod_eq_one_of_forall_eq_one h2, mul_one]
  simp_rw [norm_fst_apply_of_extensionEmbedding_eq F (z : AdeleRing (𝓞 F) F) r hr hz1]
  rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq]

private theorem val_toHomUnits_distribHaarChar_eq_pow_of_dilation (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ) (hr : 0 < r)
    (hz2 : (z : AdeleRing (𝓞 F) F).2 = 1)
    (hz1 : ∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) :
    ((((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits z : ℝˣ) : ℝ) = r ^ Module.finrank ℚ F :=
  distribHaarChar_eq_pow_of_dilation F z r hr hz2 hz1

private theorem ringEquiv_mixedSpace_fst_of_dilation (z : AdeleRing (𝓞 F) F) (r : ℝ)
    (hz : ∀ w : InfinitePlace F, Completion.extensionEmbedding w (z.1 w) = (r : ℂ))
    (i : {w : InfinitePlace F // w.IsReal}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F z.1).1 i = r := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  apply Complex.ofReal_injective
  rw [← extensionEmbedding_eq_ofReal_of_isReal F i.2, hz]

private theorem ringEquiv_mixedSpace_snd_of_dilation (z : AdeleRing (𝓞 F) F) (r : ℝ)
    (hz : ∀ w : InfinitePlace F, Completion.extensionEmbedding w (z.1 w) = (r : ℂ))
    (w : {w : InfinitePlace F // w.IsComplex}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F z.1).2 w = (r : ℂ) := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact hz w.1

end B2

section B3

open IsDedekindDomain NumberField.InfinitePlace

variable (F : Type) [Field F] [NumberField F]

private theorem fst_apply_mul_inv_fst_apply (u : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (u : AdeleRing (𝓞 F) F).1 w * ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 := by
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) u.mul_inv
  exact h

private theorem exists_norm_fst_apply_bounds_of_isCompact (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ u ∈ U, ∀ w : InfinitePlace F,
      c₁ ≤ ‖(u : AdeleRing (𝓞 F) F).1 w‖ ∧ ‖(u : AdeleRing (𝓞 F) F).1 w‖ ≤ c₂ := by
  have hcont : ∀ w : InfinitePlace F, Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => (u : AdeleRing (𝓞 F) F).1 w :=
    fun w => (continuous_apply w).comp (continuous_fst.comp Units.continuous_val)
  have hcont' : ∀ w : InfinitePlace F,
      Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w :=
    fun w => (continuous_apply w).comp (continuous_fst.comp Units.continuous_coe_inv)
  choose C hC using fun w => hU.exists_bound_of_continuousOn (hcont w).continuousOn
  choose C' hC' using fun w => hU.exists_bound_of_continuousOn (hcont' w).continuousOn
  set c₂ : ℝ := ∑ w, max (C w) 0 with hc₂
  set D : ℝ := max (∑ w, max (C' w) 0) 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  have hD0 : 0 < D := one_pos.trans_le hD1
  have hCle : ∀ w, C w ≤ c₂ := fun w =>
    (le_max_left _ _).trans (Finset.single_le_sum (fun w' _ => le_max_right (C w') 0) (Finset.mem_univ w))
  have hC'le : ∀ w, C' w ≤ D := fun w =>
    ((le_max_left _ _).trans (Finset.single_le_sum (fun w' _ => le_max_right (C' w') 0) (Finset.mem_univ w))).trans
      (le_max_left _ _)
  refine ⟨D⁻¹, c₂, inv_pos.mpr hD0, fun u hu w => ⟨?_, (hC w u hu).trans (hCle w)⟩⟩
  have hprod : ‖(u : AdeleRing (𝓞 F) F).1 w‖ * ‖((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ = 1 := by
    rw [← norm_mul, fst_apply_mul_inv_fst_apply, norm_one]
  have hinv_le : ‖((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ≤ D := (hC' w u hu).trans (hC'le w)
  have hpos : 0 < ‖(u : AdeleRing (𝓞 F) F).1 w‖ := by
    rcases (norm_nonneg ((u : AdeleRing (𝓞 F) F).1 w)).eq_or_lt with h | h
    · rw [← h, zero_mul] at hprod
      exact absurd hprod zero_ne_one
    · exact h
  rw [inv_le_iff_one_le_mul₀ hD0]
  calc 1 = ‖(u : AdeleRing (𝓞 F) F).1 w‖ * ‖((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ := hprod.symm
    _ ≤ ‖(u : AdeleRing (𝓞 F) F).1 w‖ * D := mul_le_mul_of_nonneg_left hinv_le hpos.le

private theorem norm_ringEquiv_mixedSpace_fst (y : InfiniteAdeleRing F) (i : {w : InfinitePlace F // w.IsReal}) :
    |(InfiniteAdeleRing.ringEquiv_mixedSpace F y).1 i| = ‖y i.1‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, ← Real.norm_eq_abs]
  exact (Completion.isometry_extensionEmbeddingOfIsReal i.2).norm_map_of_map_zero (map_zero _) _

private theorem norm_ringEquiv_mixedSpace_snd (y : InfiniteAdeleRing F) (w : {w : InfinitePlace F // w.IsComplex}) :
    ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F y).2 w‖ = ‖y w.1‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _

private theorem exists_mixedSpace_coord_bounds_of_isCompact (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ ∀ u ∈ U,
      (∀ i : {w : InfinitePlace F // w.IsReal},
        c₁ ≤ |(InfiniteAdeleRing.ringEquiv_mixedSpace F (u : AdeleRing (𝓞 F) F).1).1 i| ∧
        |(InfiniteAdeleRing.ringEquiv_mixedSpace F (u : AdeleRing (𝓞 F) F).1).1 i| ≤ c₂) ∧
      (∀ w : {w : InfinitePlace F // w.IsComplex},
        c₁ ≤ ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F (u : AdeleRing (𝓞 F) F).1).2 w‖ ∧
        ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F (u : AdeleRing (𝓞 F) F).1).2 w‖ ≤ c₂) := by
  obtain ⟨c₁, c₂, hc₁, h⟩ := exists_norm_fst_apply_bounds_of_isCompact F U hU
  refine ⟨c₁, c₂, hc₁, fun u hu => ⟨fun i => ?_, fun w => ?_⟩⟩
  · rw [norm_ringEquiv_mixedSpace_fst]
    exact h u hu i.1
  · rw [norm_ringEquiv_mixedSpace_snd]
    exact h u hu w.1

end B3

section B4

open MeasureTheory NumberField.InfinitePlace IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

private theorem adele_fst_mul (a b : AdeleRing (𝓞 F) F) : (a * b).1 = a.1 * b.1 := rfl

private theorem adele_snd_mul (a b : AdeleRing (𝓞 F) F) : (a * b).2 = a.2 * b.2 := rfl

private theorem infiniteAdele_mul_apply (a b : InfiniteAdeleRing F) (w : InfinitePlace F) : (a * b) w = a w * b w := rfl

private theorem snd_mul_dilation_mul (z u : (AdeleRing (𝓞 F) F)ˣ) (hz2 : (z : AdeleRing (𝓞 F) F).2 = 1)
    (x x' : AdeleRing (𝓞 F) F) :
    (x * ((z * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x').2 = (x * (u : AdeleRing (𝓞 F) F) * x').2 := by
  rw [Units.val_mul, adele_snd_mul, adele_snd_mul, adele_snd_mul, adele_snd_mul, adele_snd_mul, hz2, one_mul]

private theorem snd_mul_dilation_mul_apply (z u : (AdeleRing (𝓞 F) F)ˣ) (hz2 : (z : AdeleRing (𝓞 F) F).2 = 1)
    (x x' : AdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x * ((z * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x').2 v = (x * (u : AdeleRing (𝓞 F) F) * x').2 v := by
  rw [snd_mul_dilation_mul F z u hz2]

private theorem ringEquiv_mixedSpace_fst_mul_dilation_mul (z u : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ)
    (hz1 : ∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ))
    (x x' : AdeleRing (𝓞 F) F) (i : {w : InfinitePlace F // w.IsReal}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (x * ((z * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x').1).1 i
      = r * (InfiniteAdeleRing.ringEquiv_mixedSpace F (x * (u : AdeleRing (𝓞 F) F) * x').1).1 i := by
  have hz := ringEquiv_mixedSpace_fst_of_dilation F (z : AdeleRing (𝓞 F) F) r hz1 i
  rw [Units.val_mul, adele_fst_mul, adele_fst_mul, adele_fst_mul, adele_fst_mul, adele_fst_mul,
    map_mul, map_mul, map_mul, map_mul, map_mul]
  simp only [Prod.fst_mul, Pi.mul_apply, hz]
  ring

private theorem ringEquiv_mixedSpace_snd_mul_dilation_mul (z u : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ)
    (hz1 : ∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ))
    (x x' : AdeleRing (𝓞 F) F) (w : {w : InfinitePlace F // w.IsComplex}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (x * ((z * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x').1).2 w
      = (r : ℂ) * (InfiniteAdeleRing.ringEquiv_mixedSpace F (x * (u : AdeleRing (𝓞 F) F) * x').1).2 w := by
  have hz := ringEquiv_mixedSpace_snd_of_dilation F (z : AdeleRing (𝓞 F) F) r hz1 w
  rw [Units.val_mul, adele_fst_mul, adele_fst_mul, adele_fst_mul, adele_fst_mul, adele_fst_mul,
    map_mul, map_mul, map_mul, map_mul, map_mul]
  simp only [Prod.snd_mul, Pi.mul_apply, hz]
  ring

private theorem norm_cpowChar_dilation_mul (z u : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ) (hr : 0 < r)
    (hz2 : (z : AdeleRing (𝓞 F) F).2 = 1)
    (hz1 : ∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ))
    (s : ℂ) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)),
      ‖((cpowChar α hα (1 / 2 - s) (z * u) : ℂˣ) : ℂ)‖
        = r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) * ((α u : ℝˣ) : ℝ) ^ (1 / 2 - s.re) := by
  intro α hα
  have hre : (1 / 2 - s).re = 1 / 2 - s.re := by
    rw [Complex.sub_re]
    norm_num
  have hαz : ((α z : ℝˣ) : ℝ) = r ^ Module.finrank ℚ F :=
    val_toHomUnits_distribHaarChar_eq_pow_of_dilation F z r hr hz2 hz1
  rw [norm_cpowChar_apply, hre, map_mul, Units.val_mul, hαz, Real.mul_rpow (by positivity) (hα u).le,
    ← Real.rpow_natCast_mul hr.le]

private theorem isPrincipalTrivial_modulus [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] :
    IsPrincipalTrivial (R := 𝓞 F) (K := F)
      ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits := by
  intro η
  apply Units.ext
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F η
  rw [RingHom.toMonoidHom_eq_coe] at h
  rw [MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, h, map_one, Units.val_one]

private theorem cpowChar_modulus_principal [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (hα : ∀ t : (AdeleRing (𝓞 F) F)ˣ, 0 < ((((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp
      (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits t : ℝˣ) : ℝ)) (t : ℂ) (η : Fˣ) :
    cpowChar ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
      hα t (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η) = 1 :=
  cpowChar_isIdeleClassChar (isPrincipalTrivial_modulus F) t η

end B4

end T1Helpers

section IdeleFacts

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

private theorem T1U_idele_fst_ne_zero (U : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (U : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  have h : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w * (U : AdeleRing (𝓞 F) F).1 w = 1 :=
    congrArg (fun z : AdeleRing (𝓞 F) F => z.1 w) (Units.inv_mul U)
  exact right_ne_zero_of_mul_eq_one h

private theorem T1U_idele_valued_ne_one_finite (U : (AdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v ((U : AdeleRing (𝓞 F) F).2 v) ≠ 1}.Finite := by
  have hmul : (U : AdeleRing (𝓞 F) F).2 * ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv U)
  have hmul' : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * (U : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul U)
  have hu : IsUnit ((U : AdeleRing (𝓞 F) F).2) := ⟨⟨_, _, hmul, hmul'⟩, rfl⟩
  exact Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp hu).2

private theorem T1U_continuous_mixedSpace_fst (i : {w : InfinitePlace F // w.IsReal}) :
    Continuous fun x : InfiniteAdeleRing F => (InfiniteAdeleRing.ringEquiv_mixedSpace F x).1 i := by
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal i.2).continuous.comp (continuous_apply i.1)

private theorem T1U_continuous_mixedSpace_snd (w : {w : InfinitePlace F // w.IsComplex}) :
    Continuous fun x : InfiniteAdeleRing F => (InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 w := by
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp (continuous_apply w.1)

end IdeleFacts

section ArchDilation

open NumberField

private theorem T1F5_one_add_mul_rpow_neg_le (c x N : ℝ) (hc : 0 < c) (hx : 0 ≤ x) (hN : 0 ≤ N) :
    (1 + c * x) ^ (-N) ≤ (min 1 c) ^ (-N) * (1 + x) ^ (-N) := by
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hle : min 1 c * (1 + x) ≤ 1 + c * x := by
    have h1 : min 1 c ≤ 1 := min_le_left _ _
    have h2 : min 1 c * x ≤ c * x := mul_le_mul_of_nonneg_right (min_le_right _ _) hx
    linarith
  calc (1 + c * x) ^ (-N) ≤ (min 1 c * (1 + x)) ^ (-N) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hm0 (by linarith)) hle (by linarith)
    _ = (min 1 c) ^ (-N) * (1 + x) ^ (-N) := Real.mul_rpow hm0.le (by linarith)

private theorem T1F5_mixedSpace_algebraMap_mul (F : Type) [Field F] [NumberField F] (ξ : F) (t : AdeleRing (𝓞 F) F) :
    (∀ i : {w : InfinitePlace F // w.IsReal},
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ * t).1).1 i
        = (mixedEmbedding F ξ).1 i * (InfiniteAdeleRing.ringEquiv_mixedSpace F t.1).1 i) ∧
    ∀ w : {w : InfinitePlace F // w.IsComplex},
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ * t).1).2 w
        = (mixedEmbedding F ξ).2 w * (InfiniteAdeleRing.ringEquiv_mixedSpace F t.1).2 w := by
  have h1 : (algebraMap F (AdeleRing (𝓞 F) F) ξ * t).1 = algebraMap F (InfiniteAdeleRing F) ξ * t.1 := rfl
  have h2 : InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) ξ * t).1
      = mixedEmbedding F ξ * InfiniteAdeleRing.ringEquiv_mixedSpace F t.1 := by
    rw [h1, map_mul, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  refine ⟨fun i => ?_, fun w => ?_⟩
  · rw [h2, Prod.fst_mul, Pi.mul_apply]
  · rw [h2, Prod.snd_mul, Pi.mul_apply]

end ArchDilation

section ArchDilationTwoSided

open NumberField
open scoped Classical

private theorem T1F5_rpow_neg_mul_le_of_le (x : ℝ) (hx : 0 < x) (M M' N : ℕ) (hM : M ≤ M') :
    x ^ (-(M : ℝ)) * (1 + x) ^ (-((N + M' : ℕ) : ℝ)) ≤ x ^ (-(M' : ℝ)) * (1 + x) ^ (-(N : ℝ)) := by
  have hx1 : 0 < 1 + x := by linarith
  rw [Real.rpow_neg hx.le, Real.rpow_neg hx.le, Real.rpow_neg hx1.le, Real.rpow_neg hx1.le,
    Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast, pow_add]
  have key : (x ^ M)⁻¹ * ((1 + x) ^ M')⁻¹ ≤ (x ^ M')⁻¹ := by
    rw [← mul_inv, inv_le_inv₀ (mul_pos (pow_pos hx _) (pow_pos hx1 _)) (pow_pos hx _)]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
    calc x ^ (M + d) = x ^ M * x ^ d := pow_add _ _ _
      _ ≤ x ^ M * (1 + x) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le (by linarith) d) (pow_nonneg hx.le _)
      _ ≤ x ^ M * (1 + x) ^ (M + d) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by omega)) (pow_nonneg hx.le _)
  calc (x ^ M)⁻¹ * ((1 + x) ^ N * (1 + x) ^ M')⁻¹ = ((x ^ M)⁻¹ * ((1 + x) ^ M')⁻¹) * ((1 + x) ^ N)⁻¹ := by
        rw [mul_inv]; ring
    _ ≤ (x ^ M')⁻¹ * ((1 + x) ^ N)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.mpr (pow_nonneg hx1.le _))

private theorem T1F5_dilation_bound_of_rpow_polyDecay (j : ℂ → ℝ → ℂ) (K : Set ℂ) (M N : ℕ) (C₀ : ℝ)
    (hC₀ : 0 < C₀)
    (hj : ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖j w t‖ ≤ C₀ * |t| ^ (-(M : ℝ)) * (1 + |t|) ^ (-(N : ℝ)))
    (θ : ℝ) (hθ : θ ≠ 0) (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ (r x m : ℝ), 0 < r → x ≠ 0 → c₁ ≤ |m| →
      ‖j w (-(θ * (r * (x * m))))‖
        ≤ C * (r ^ (-(M : ℝ)) * |x| ^ (-(M : ℝ))) * (1 + r * |x|) ^ (-(N : ℝ)) := by
  have hθc : 0 < |θ| * c₁ := mul_pos (abs_pos.2 hθ) hc₁
  refine ⟨C₀ * (|θ| * c₁) ^ (-(M : ℝ)) * (min 1 (|θ| * c₁)) ^ (-(N : ℝ)),
    mul_pos (mul_pos hC₀ (Real.rpow_pos_of_pos hθc _)) (Real.rpow_pos_of_pos (lt_min one_pos hθc) _), ?_⟩
  intro w hw r x m hr hx hm
  have hm0 : 0 < |m| := hc₁.trans_le hm
  have ht0 : (-(θ * (r * (x * m)))) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hθ (mul_ne_zero hr.ne' (mul_ne_zero hx (abs_pos.mp hm0))))
  have h := hj w hw _ ht0
  have hrx : 0 < r * |x| := mul_pos hr (abs_pos.mpr hx)
  have ht₀ : |(-(θ * (r * (x * m))))| = (|θ| * |m|) * (r * |x|) := by
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos hr]; ring
  have hsing : |(-(θ * (r * (x * m))))| ^ (-(M : ℝ))
      ≤ (|θ| * c₁) ^ (-(M : ℝ)) * (r ^ (-(M : ℝ)) * |x| ^ (-(M : ℝ))) := by
    rw [ht₀, Real.mul_rpow (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hrx.le,
      Real.mul_rpow hr.le (abs_nonneg _)]
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg (abs_nonneg _) _))
    exact Real.rpow_le_rpow_of_nonpos hθc (mul_le_mul_of_nonneg_left hm (abs_nonneg θ)) (by simp)
  have hge : |θ| * c₁ * (r * |x|) ≤ |(-(θ * (r * (x * m))))| := by
    rw [ht₀]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (abs_nonneg θ)) hrx.le
  have h1 : (1 + |(-(θ * (r * (x * m))))|) ^ (-(N : ℝ)) ≤ (1 + |θ| * c₁ * (r * |x|)) ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
  have h2 := T1F5_one_add_mul_rpow_neg_le (|θ| * c₁) (r * |x|) N hθc hrx.le (Nat.cast_nonneg N)
  calc _ ≤ C₀ * |(-(θ * (r * (x * m))))| ^ (-(M : ℝ)) * (1 + |(-(θ * (r * (x * m))))|) ^ (-(N : ℝ)) := h
    _ ≤ C₀ * ((|θ| * c₁) ^ (-(M : ℝ)) * (r ^ (-(M : ℝ)) * |x| ^ (-(M : ℝ))))
          * ((min 1 (|θ| * c₁)) ^ (-(N : ℝ)) * (1 + r * |x|) ^ (-(N : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsing hC₀.le) (h1.trans h2) (by positivity) (by positivity)
    _ = _ := by ring

private theorem T1F5_dilation_bound_of_rpow_polyDecay_complex (j : ℂ → ℂ → ℂ) (K : Set ℂ) (M N : ℕ) (C₀ : ℝ)
    (hC₀ : 0 < C₀)
    (hj : ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖j w ζ‖ ≤ C₀ * ‖ζ‖ ^ (-(M : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)))
    (θ : ℂ) (hθ : θ ≠ 0) (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ (r : ℝ) (x m : ℂ), 0 < r → x ≠ 0 → c₁ ≤ ‖m‖ →
      ‖j w (-(θ * ((r : ℂ) * (x * m))))‖
        ≤ C * (r ^ (-(M : ℝ)) * ‖x‖ ^ (-(M : ℝ))) * (1 + r * ‖x‖) ^ (-(N : ℝ)) := by
  have hθc : 0 < ‖θ‖ * c₁ := mul_pos (norm_pos_iff.2 hθ) hc₁
  refine ⟨C₀ * (‖θ‖ * c₁) ^ (-(M : ℝ)) * (min 1 (‖θ‖ * c₁)) ^ (-(N : ℝ)),
    mul_pos (mul_pos hC₀ (Real.rpow_pos_of_pos hθc _)) (Real.rpow_pos_of_pos (lt_min one_pos hθc) _), ?_⟩
  intro w hw r x m hr hx hm
  have hm0 : 0 < ‖m‖ := hc₁.trans_le hm
  have ht0 : (-(θ * ((r : ℂ) * (x * m)))) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero hθ (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
      (mul_ne_zero hx (norm_pos_iff.mp hm0))))
  have h := hj w hw _ ht0
  have hrx : 0 < r * ‖x‖ := mul_pos hr (norm_pos_iff.mpr hx)
  have hζ₀ : ‖(-(θ * ((r : ℂ) * (x * m))))‖ = (‖θ‖ * ‖m‖) * (r * ‖x‖) := by
    rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]; ring
  have hsing : ‖(-(θ * ((r : ℂ) * (x * m))))‖ ^ (-(M : ℝ))
      ≤ (‖θ‖ * c₁) ^ (-(M : ℝ)) * (r ^ (-(M : ℝ)) * ‖x‖ ^ (-(M : ℝ))) := by
    rw [hζ₀, Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hrx.le,
      Real.mul_rpow hr.le (norm_nonneg _)]
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg (norm_nonneg _) _))
    exact Real.rpow_le_rpow_of_nonpos hθc (mul_le_mul_of_nonneg_left hm (norm_nonneg θ)) (by simp)
  have hge : ‖θ‖ * c₁ * (r * ‖x‖) ≤ ‖(-(θ * ((r : ℂ) * (x * m))))‖ := by
    rw [hζ₀]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (norm_nonneg θ)) hrx.le
  have h1 : (1 + ‖(-(θ * ((r : ℂ) * (x * m))))‖) ^ (-(N : ℝ)) ≤ (1 + ‖θ‖ * c₁ * (r * ‖x‖)) ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
  have h2 := T1F5_one_add_mul_rpow_neg_le (‖θ‖ * c₁) (r * ‖x‖) N hθc hrx.le (Nat.cast_nonneg N)
  calc _ ≤ C₀ * ‖(-(θ * ((r : ℂ) * (x * m))))‖ ^ (-(M : ℝ)) * (1 + ‖(-(θ * ((r : ℂ) * (x * m))))‖) ^ (-(N : ℝ)) := h
    _ ≤ C₀ * ((‖θ‖ * c₁) ^ (-(M : ℝ)) * (r ^ (-(M : ℝ)) * ‖x‖ ^ (-(M : ℝ))))
          * ((min 1 (‖θ‖ * c₁)) ^ (-(N : ℝ)) * (1 + r * ‖x‖) ^ (-(N : ℝ))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsing hC₀.le) (h1.trans h2) (by positivity) (by positivity)
    _ = _ := by ring

private theorem T1F5_prod_abs_mul_prod_norm_sq_eq_abs_norm (F : Type) [Field F] [NumberField F] (ξ : F) :
    (∏ i : {w : InfinitePlace F // w.IsReal}, |(mixedEmbedding F ξ).1 i|)
      * (∏ w : {w : InfinitePlace F // w.IsComplex}, ‖(mixedEmbedding F ξ).2 w‖) ^ 2
      = ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
  classical
  rw [← mixedEmbedding.norm_eq_norm, mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod,
    ← Finset.prod_pow]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [InfinitePlace.mult_isReal, pow_one, mixedEmbedding.normAtPlace_apply_of_isReal i.2, Real.norm_eq_abs]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [InfinitePlace.mult_isComplex, mixedEmbedding.normAtPlace_apply_of_isComplex w.2]

end ArchDilationTwoSided

section T1Main

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.InfinitePlace AutomorphicForm
open AutomorphicForm.WindowedSiegel Filter Topology
open NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain
open scoped NNReal Classical

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private noncomputable def T1jR (k : ℤ) (w : ℂ) (t : ℝ) : ℂ := ∫ x : ℝ,
  ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
      * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))

private noncomputable def T1jC (a b : ℕ) (w ζ : ℂ) : ℂ := ∫ z : ℂ,
  z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))

private noncomputable def T1JR (k : ℤ) : ℂ → ℝ → ℂ :=
  (AutomorphicForm.RealIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay k).choose

private theorem T1JR_spec (k : ℤ) :
    (∀ t : ℝ, t ≠ 0 → Differentiable ℂ (fun w : ℂ => T1JR k w t)) ∧
    (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 → T1JR k w t = T1jR k w t) ∧
    ContinuousOn (fun p : ℂ × ℝ => T1JR k p.1 p.2) (Set.univ ×ˢ {t : ℝ | t ≠ 0}) ∧
    (∀ K : Set ℂ, IsCompact K → ∃ M : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖T1JR k w t‖ ≤ C * |t| ^ (-(M : ℝ)) * (1 + |t|) ^ (-(N : ℝ))) :=
  (AutomorphicForm.RealIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay k).choose_spec

private noncomputable def T1JC (a b : ℕ) : ℂ → ℂ → ℂ :=
  (AutomorphicForm.ComplexIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay a b).choose

private theorem T1JC_spec (a b : ℕ) :
    (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => T1JC a b w ζ)) ∧
    (∀ (w : ℂ) (ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 → T1JC a b w ζ = T1jC a b w ζ) ∧
    ContinuousOn (fun p : ℂ × ℂ => T1JC a b p.1 p.2) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) ∧
    (∀ K : Set ℂ, IsCompact K → ∃ M : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖T1JC a b w ζ‖ ≤ C * ‖ζ‖ ^ (-(M : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ))) :=
  (AutomorphicForm.ComplexIwasawa.exists_entire_weightFourierIntegral_norm_le_rpow_neg_mul_polyDecay a b).choose_spec

private theorem T1JR_bound_of_le (k : ℤ) (K : Set ℂ) (hK : IsCompact K) (M : ℕ)
    (hM : ((T1JR_spec k).2.2.2 K hK).choose ≤ M) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 →
      ‖T1JR k w t‖ ≤ C * |t| ^ (-(M : ℝ)) * (1 + |t|) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, h⟩ := ((T1JR_spec k).2.2.2 K hK).choose_spec (N + M)
  refine ⟨C, hC, fun w hw t ht => (h w hw t ht).trans ?_⟩
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (T1F5_rpow_neg_mul_le_of_le |t| (abs_pos.mpr ht) _ M N hM) hC.le

private theorem T1JC_bound_of_le (a b : ℕ) (K : Set ℂ) (hK : IsCompact K) (M : ℕ)
    (hM : ((T1JC_spec a b).2.2.2 K hK).choose ≤ M) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 →
      ‖T1JC a b w ζ‖ ≤ C * ‖ζ‖ ^ (-(M : ℝ)) * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, h⟩ := ((T1JC_spec a b).2.2.2 K hK).choose_spec (N + M)
  refine ⟨C, hC, fun w hw ζ hζ => (h w hw ζ hζ).trans ?_⟩
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (T1F5_rpow_neg_mul_le_of_le ‖ζ‖ (norm_pos_iff.mpr hζ) _ M N hM) hC.le

variable (F : Type) [Field F] [NumberField F]

private noncomputable def T1frq (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F :=
  algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (y : AdeleRing (𝓞 F) F)

private noncomputable def T1Kc (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (a : (AdeleRing (𝓞 F) F)ˣ)
    (u x : AdeleRing (𝓞 F) F) : ℂ :=
  (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
    * ((((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (x * u))

private noncomputable def T1AR (n : ℕ) (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ) (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ i : {w : InfinitePlace F // w.IsReal}, T1JR (kdat j i) (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)
    (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i))

private noncomputable def T1AC (n : ℕ) (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ w : {w : InfinitePlace F // w.IsComplex}, T1JC (abm j w).1 (abm j w).2.1
    (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)
    (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w))

private noncomputable def T1P (ST S : Finset (HeightOneSpectrum (𝓞 F))) (zE : HeightOneSpectrum (𝓞 F) → ℂ)
    (s : ℂ) : ℂ :=
  ∏ v ∈ S \ ST, (1 - zE v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))

private noncomputable def T1Fi (n : ℕ) (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), Φ j v ((x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s

private noncomputable def T1J (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ST S : Finset (HeightOneSpectrum (𝓞 F))) (zE : HeightOneSpectrum (𝓞 F) → ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ((ν y : ℂˣ) : ℂ) * ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ)
    * ∑ j : Fin n, C j s * T1Kc F ψ a u (T1frq F ξ y) * T1AR F n kdat τr θr a j s (T1frq F ξ y)
        * T1AC F n abm τc θc a j s (T1frq F ξ y) * (T1P F ST S zE s * T1Fi F n Φ a j s (T1frq F ξ y))

variable {F}

private theorem T1frq_mul_eq_val (a : (AdeleRing (𝓞 F) F)ˣ) (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ) :
    T1frq F ξ y * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = ((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * y * a⁻¹ :
          (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
  simp only [T1frq, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0]

private theorem T1frq_coord_ne_zero (a : (AdeleRing (𝓞 F) F)ˣ) (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ) :
    (∀ i : {w : InfinitePlace F // w.IsReal},
      (InfiniteAdeleRing.ringEquiv_mixedSpace F
        (T1frq F ξ y * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i ≠ 0) ∧
    (∀ w : {w : InfinitePlace F // w.IsComplex},
      (InfiniteAdeleRing.ringEquiv_mixedSpace F
        (T1frq F ξ y * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w ≠ 0) := by
  rw [T1frq_mul_eq_val]
  set U : (AdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * y * a⁻¹
  refine ⟨fun i => ?_, fun w => ?_⟩
  · rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (map_ne_zero _).mpr (T1U_idele_fst_ne_zero U i.1)
  · rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (map_ne_zero _).mpr (T1U_idele_fst_ne_zero U w.1)

private theorem T1Fi_eq_prod (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) (Ux : (AdeleRing (𝓞 F) F)ˣ)
    (hUx : (Ux : AdeleRing (𝓞 F) F) = x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) :
    T1Fi F n Φ a j s x = ∏ v ∈ S ∪ (T1U_idele_valued_ne_one_finite Ux).toFinset,
      Φ j v ((x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s := by
  classical
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  rw [Function.mem_mulSupport] at hv
  rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  by_contra hc
  push Not at hc
  refine hv (hΦ1 j v hc.1 _ s ?_)
  rw [← hUx]
  exact hc.2

private theorem T1_differentiable_shiftR (τ : ℝ) :
    Differentiable ℂ (fun s : ℂ => s + 1 / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2) :=
  (differentiable_id.add_const _).add_const _

private theorem T1_differentiable_shiftC (m : ℕ) (τ : ℝ) :
    Differentiable ℂ (fun s : ℂ => 2 * s + 1 + (m : ℂ) / 2 + ((τ : ℝ) : ℂ) * Complex.I / 2) :=
  (((differentiable_id.const_mul _).add_const _).add_const _).add_const _

private theorem T1P_differentiable (ST S : Finset (HeightOneSpectrum (𝓞 F))) (zE : HeightOneSpectrum (𝓞 F) → ℂ) :
    Differentiable ℂ (T1P F ST S zE) := by
  unfold T1P
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine (differentiable_const _).sub ((differentiable_const _).mul ?_)
  refine Differentiable.const_cpow (((differentiable_id.const_mul _).add_const _).neg) (Or.inl ?_)
  exact_mod_cast fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)

private noncomputable def T1ARh (n : ℕ) (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ) (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ i : {w : InfinitePlace F // w.IsReal}, T1jR (kdat j i) (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)
    (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i))

private noncomputable def T1ACh (n : ℕ) (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ w : {w : InfinitePlace F // w.IsComplex}, T1jC (abm j w).1 (abm j w).2.1
    (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)
    (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w))

private noncomputable def T1Eu (ST : Finset (HeightOneSpectrum (𝓞 F))) (zE : HeightOneSpectrum (𝓞 F) → ℂ)
    (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ ST}, (1 - zE v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))

private noncomputable def T1Jh (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ST : Finset (HeightOneSpectrum (𝓞 F))) (zE : HeightOneSpectrum (𝓞 F) → ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ((ν y : ℂˣ) : ℂ) * ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ)
    * ∑ j : Fin n, C j s * T1Kc F ψ a u (T1frq F ξ y) * T1ARh n kdat τr θr a j s (T1frq F ξ y)
        * T1ACh n abm τc θc a j s (T1frq F ξ y) * (T1Eu ST zE s * T1Fi F n Φ a j s (T1frq F ξ y))

private theorem T1AR_eq_T1ARh (n : ℕ) (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ) (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
    (hθr : ∀ i, θr i ≠ 0) (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (hs : 0 < s.re)
    (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ) :
    T1AR F n kdat τr θr a j s (T1frq F ξ y) = T1ARh n kdat τr θr a j s (T1frq F ξ y) := by
  classical
  simp only [T1AR, T1ARh]
  refine Finset.prod_congr rfl fun i _ => (T1JR_spec (kdat j i)).2.1 _ _ ?_ ?_
  · have h1 : (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2).re = s.re + 1 / 2 := by
      norm_num [Complex.mul_re]
    rw [h1]
    linarith
  · exact neg_ne_zero.mpr (mul_ne_zero (hθr i) ((T1frq_coord_ne_zero a ξ y).1 i))

private theorem T1AC_eq_T1ACh (n : ℕ) (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hθc : ∀ w, θc w ≠ 0)
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (hs : 0 < s.re)
    (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ) :
    T1AC F n abm τc θc a j s (T1frq F ξ y) = T1ACh n abm τc θc a j s (T1frq F ξ y) := by
  classical
  simp only [T1AC, T1ACh]
  refine Finset.prod_congr rfl fun w _ => (T1JC_spec (abm j w).1 (abm j w).2.1).2.1 _ _ ?_ ?_
  · have h1 : (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2).re
        = 2 * s.re + 1 + ((abm j w).2.2 : ℝ) / 2 := by
      norm_num [Complex.mul_re]
    have h2 : (((abm j w).1 + (abm j w).2.1 : ℕ) : ℝ) ≤ ((abm j w).2.2 : ℝ) := by exact_mod_cast habm j w
    rw [h1]
    linarith
  · exact neg_ne_zero.mpr (mul_ne_zero (hθc w) ((T1frq_coord_ne_zero a ξ y).2 w))

private theorem T1J_eq_mul_T1Jh (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ST S : Finset (HeightOneSpectrum (𝓞 F))) (zE : HeightOneSpectrum (𝓞 F) → ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (hs : 0 < s.re) (y : (AdeleRing (𝓞 F) F)ˣ) (L : ℂ)
    (hEu : T1P F ST S zE s = L * T1Eu ST zE s) :
    T1J F α hα ν ψ ST S zE n C kdat τr abm τc θr θc a u Φ ξ s y
      = L * T1Jh α hα ν ψ ST zE n C kdat τr abm τc θr θc a u Φ ξ s y := by
  simp only [T1J, T1Jh, hEu, T1AR_eq_T1ARh n kdat τr θr hθr a _ s hs ξ y,
    T1AC_eq_T1ACh n abm τc θc hθc habm a _ s hs ξ y]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem T1J_differentiable (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ST S : Finset (HeightOneSpectrum (𝓞 F)))
    (zE : HeightOneSpectrum (𝓞 F) → ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hC : ∀ j, Differentiable ℂ (C j))
    (hΦd : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w))
    (hΦ1 : ∀ (j : Fin n), ∀ v ∉ ST, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ) :
    Differentiable ℂ (fun s => T1J F α hα ν ψ ST S zE n C kdat τr abm τc θr θc a u Φ ξ s y) := by
  classical
  set x : AdeleRing (𝓞 F) F := T1frq F ξ y with hx
  set Ux : (AdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * y * a⁻¹ with hUx
  have hUx' : (Ux : AdeleRing (𝓞 F) F) = x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) :=
    (T1frq_mul_eq_val a ξ y).symm
  obtain ⟨hfrR, hfrC⟩ := T1frq_coord_ne_zero a ξ y
  have hcp : Differentiable ℂ (fun s : ℂ => ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ)) := by
    simp only [cpowChar_apply_val]
    exact Differentiable.const_cpow ((differentiable_const _).sub differentiable_id)
      (Or.inl (Complex.ofReal_ne_zero.mpr (hα y).ne'))
  have hAR : ∀ j, Differentiable ℂ (fun s => T1AR F n kdat τr θr a j s x) := by
    intro j
    simp only [T1AR]
    refine Differentiable.fun_finsetProd fun i _ => ?_
    have ht : (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
        (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i)) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero (hθr i) (hfrR i))
    exact ((T1JR_spec (kdat j i)).1 _ ht).comp (T1_differentiable_shiftR (τr j i))
  have hAC : ∀ j, Differentiable ℂ (fun s => T1AC F n abm τc θc a j s x) := by
    intro j
    simp only [T1AC]
    refine Differentiable.fun_finsetProd fun w _ => ?_
    have hζ : (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
        (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w)) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero (hθc w) (hfrC w))
    exact ((T1JC_spec (abm j w).1 (abm j w).2.1).1 _ hζ).comp (T1_differentiable_shiftC (abm j w).2.2 (τc j w))
  have hP : Differentiable ℂ (T1P F ST S zE) := T1P_differentiable ST S zE
  have hFi : ∀ j, Differentiable ℂ (fun s => T1Fi F n Φ a j s x) := by
    intro j
    have hprod : Differentiable ℂ (fun s => ∏ v ∈ ST ∪ (T1U_idele_valued_ne_one_finite Ux).toFinset,
        Φ j v ((x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s) :=
      Differentiable.fun_finsetProd fun v _ => hΦd j v _
    have heq : (fun s => T1Fi F n Φ a j s x) = fun s => ∏ v ∈ ST ∪ (T1U_idele_valued_ne_one_finite Ux).toFinset,
        Φ j v ((x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s :=
      funext fun s => T1Fi_eq_prod ST n Φ hΦ1 a j s x Ux hUx'
    rw [heq]
    exact hprod
  simp only [T1J]
  refine ((differentiable_const _).mul hcp).mul (Differentiable.fun_sum fun j _ => ?_)
  exact ((((hC j).mul (differentiable_const _)).mul (hAR j)).mul (hAC j)).mul (hP.mul (hFi j))

private theorem T1J_principal (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαp : ∀ (t : ℂ) (η : Fˣ), cpowChar α hα t (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η) = 1)
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ST S : Finset (HeightOneSpectrum (𝓞 F)))
    (zE : HeightOneSpectrum (𝓞 F) → ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) :
    T1J F α hα ν ψ ST S zE n C kdat τr abm τc θr θc a u Φ ξ s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
      = T1J F α hα ν ψ ST S zE n C kdat τr abm τc θr θc a u Φ ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y := by
  have hfrq : T1frq F ξ (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) η * y)
      = T1frq F ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ y := by
    simp only [T1frq, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul, mul_assoc]
  have hcp : ((cpowChar α hα (1 / 2 - s) (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) η * y) : ℂˣ) : ℂ)
      = ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ) := by
    rw [map_mul, hαp, one_mul]
  have hνy : ((ν (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F))) η * y) : ℂˣ) : ℂ) = ((ν y : ℂˣ) : ℂ) := by
    rw [map_mul, hνF η, one_mul]
  simp only [T1J]
  rw [hfrq, hcp, hνy]

private theorem T1_continuous_lift {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [Zero Y]
    (J : ℂ → Y → ℂ) (hJ : ContinuousOn (fun q : ℂ × Y => J q.1 q.2) (Set.univ ×ˢ {t : Y | t ≠ 0}))
    (w : X → ℂ) (t : X → Y) (hw : Continuous w) (ht : Continuous t) (h0 : ∀ p, t p ≠ 0) :
    Continuous fun p => J (w p) (t p) := by
  have hcomp := hJ.comp ((hw.prodMk ht).continuousOn (s := Set.univ))
    (fun p _ => Set.mk_mem_prod (Set.mem_univ _) (h0 p))
  rw [continuousOn_univ] at hcomp
  simpa only [Function.comp_def] using hcomp

private theorem T1J_continuous (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((α y : ℝˣ) : ℝ) : ℂ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hνc : Continuous ν)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (ST S : Finset (HeightOneSpectrum (𝓞 F)))
    (zE : HeightOneSpectrum (𝓞 F) → ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hC : ∀ j, Differentiable ℂ (C j))
    (hP : Differentiable ℂ (T1P F ST S zE))
    (hFi : ∀ (x₀ : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n),
      Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (p.2 : AdeleRing (𝓞 F) F)).2 v) p.1)
    (ξ : {ξ : F // ξ ≠ 0}) :
    Continuous (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1J F α hα ν ψ ST S zE n C kdat τr abm τc θr θc a u Φ ξ p.1 p.2) := by
  classical
  set x₀ : (AdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) with hx₀
  have hfrq : ∀ y : (AdeleRing (𝓞 F) F)ˣ, T1frq F ξ y = (x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F) := by
    intro y
    simp only [T1frq, hx₀, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0]
  have hfrqc : Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ =>
      T1frq F ξ p.2 * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
    simp only [T1frq]
    exact (continuous_const.mul (Units.continuous_val.comp continuous_snd)).mul continuous_const

  have hcp : Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((cpowChar α hα (1 / 2 - p.1) p.2 : ℂˣ) : ℂ) := by
    simp only [cpowChar_apply_val]
    refine Continuous.cpow (hαc.comp continuous_snd) (continuous_const.sub continuous_fst) fun p => ?_
    exact Complex.ofReal_mem_slitPlane.mpr (hα p.2)

  have hKc : Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1Kc F ψ a u (T1frq F ξ p.2) := by
    simp only [T1Kc, T1frq]
    exact continuous_const.mul (continuous_const.mul (hψ.continuous.comp
      ((continuous_const.mul (Units.continuous_val.comp continuous_snd)).mul continuous_const)))

  have hAR : ∀ j, Continuous (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1AR F n kdat τr θr a j p.1 (T1frq F ξ p.2)) := by
    intro j
    simp only [T1AR]
    refine continuous_finsetProd _ fun i _ => ?_
    exact T1_continuous_lift _ (T1JR_spec (kdat j i)).2.2.1 _ _
      ((continuous_fst.add continuous_const).add continuous_const)
      ((continuous_const.mul ((T1U_continuous_mixedSpace_fst i).comp (continuous_fst.comp hfrqc))).neg)
      fun p => neg_ne_zero.mpr (mul_ne_zero (hθr i) ((T1frq_coord_ne_zero a ξ p.2).1 i))
  have hAC : ∀ j, Continuous (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1AC F n abm τc θc a j p.1 (T1frq F ξ p.2)) := by
    intro j
    simp only [T1AC]
    refine continuous_finsetProd _ fun w _ => ?_
    exact T1_continuous_lift _ (T1JC_spec (abm j w).1 (abm j w).2.1).2.2.1 _ _
      ((((continuous_const.mul continuous_fst).add continuous_const).add continuous_const).add continuous_const)
      ((continuous_const.mul ((T1U_continuous_mixedSpace_snd w).comp (continuous_fst.comp hfrqc))).neg)
      fun p => neg_ne_zero.mpr (mul_ne_zero (hθc w) ((T1frq_coord_ne_zero a ξ p.2).2 w))

  have hPc : Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1P F ST S zE p.1 := hP.continuous.comp continuous_fst

  have hFi' : ∀ j, Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1Fi F n Φ a j p.1 (T1frq F ξ p.2) := by
    intro j
    have h := (hFi x₀ j).comp (continuous_fst.prodMk ((continuous_snd.mul continuous_const :
      Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => p.2 * a⁻¹)))
    refine h.congr fun p => ?_
    simp only [T1Fi, hfrq, Function.comp_apply, Pi.mul_apply, Units.val_mul, mul_assoc]

  have hνc' : Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((ν p.2 : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (hνc.comp continuous_snd)
  simp only [T1J]
  refine ((hνc'.mul hcp).mul (continuous_finsetSum _ fun j _ => ?_))
  exact ((((((hC j).continuous.comp continuous_fst).mul hKc).mul (hAR j)).mul (hAC j)).mul (hPc.mul (hFi' j)))

private theorem T1AR_dilation_bound (n : ℕ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (C₀ : Set ℂ) (hC₀ : IsCompact C₀) (M : ℕ)
    (hM : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}),
      ((T1JR_spec (kdat j i)).2.2.2 _
        (hC₀.image (T1_differentiable_shiftR (τr j i)).continuous)).choose ≤ M)
    (c₁ : ℝ) (hc₁ : 0 < c₁) (N : ℕ) :
    ∃ D : Fin n → ℝ, (∀ j, 0 ≤ D j) ∧ ∀ (j : Fin n), ∀ s ∈ C₀, ∀ (z uu : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r →
      (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
      (∀ i : {w : InfinitePlace F // w.IsReal},
        c₁ ≤ |(InfiniteAdeleRing.ringEquiv_mixedSpace F ((uu * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i|) →
      ∀ ξ : {ξ : F // ξ ≠ 0}, ‖T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu))‖
        ≤ D j * (∏ i : {w : InfinitePlace F // w.IsReal}, (r ^ (-(M : ℝ)) * |(mixedEmbedding F (ξ : F)).1 i| ^ (-(M : ℝ))))
          * ∏ i : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 i|) ^ (-(N : ℝ)) := by
  classical
  choose CR hCR0 hCR using fun (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) =>
    T1JR_bound_of_le (kdat j i) _ (hC₀.image (T1_differentiable_shiftR (τr j i)).continuous) M (hM j i) N
  choose DR hDR0 hDR using fun (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) =>
    T1F5_dilation_bound_of_rpow_polyDecay (T1JR (kdat j i)) _ M N (CR j i) (hCR0 j i) (hCR j i) (θr i) (hθr i) c₁ hc₁
  refine ⟨fun j => ∏ i, DR j i, fun j => Finset.prod_nonneg fun i _ => (hDR0 j i).le,
    fun j s hs z uu r hr hz1 hufc ξ => ?_⟩
  have hcoR : ∀ i : {w : InfinitePlace F // w.IsReal},
      (InfiniteAdeleRing.ringEquiv_mixedSpace F
        (T1frq F ξ (z * uu) * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i
        = r * ((mixedEmbedding F (ξ : F)).1 i
          * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((uu * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i) := by
    intro i
    simp only [T1frq]
    rw [T1Helpers.ringEquiv_mixedSpace_fst_mul_dilation_mul F z uu r hz1, mul_assoc (algebraMap F _ (ξ : F)),
      ← Units.val_mul, (T1F5_mixedSpace_algebraMap_mul F (ξ : F) _).1 i]
  have hξi : ∀ i : {w : InfinitePlace F // w.IsReal}, (mixedEmbedding F (ξ : F)).1 i ≠ 0 := by
    intro i
    rw [mixedEmbedding.mixedEmbedding_apply_isReal]
    exact (map_ne_zero _).mpr ξ.2
  simp only [T1AR]
  rw [norm_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [hcoR i]
  exact hDR j i _ ⟨s, hs, rfl⟩ r _ _ hr (hξi i) (hufc i)

private theorem T1AC_dilation_bound (n : ℕ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (C₀ : Set ℂ) (hC₀ : IsCompact C₀) (M : ℕ)
    (hM : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
      ((T1JC_spec (abm j w).1 (abm j w).2.1).2.2.2 _
        (hC₀.image (T1_differentiable_shiftC (abm j w).2.2 (τc j w)).continuous)).choose ≤ 2 * M)
    (c₁ : ℝ) (hc₁ : 0 < c₁) (N : ℕ) :
    ∃ D : Fin n → ℝ, (∀ j, 0 ≤ D j) ∧ ∀ (j : Fin n), ∀ s ∈ C₀, ∀ (z uu : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r →
      (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
      (∀ w : {w : InfinitePlace F // w.IsComplex},
        c₁ ≤ ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F ((uu * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w‖) →
      ∀ ξ : {ξ : F // ξ ≠ 0}, ‖T1AC F n abm τc θc a j s (T1frq F ξ (z * uu))‖
        ≤ D j * (∏ w : {w : InfinitePlace F // w.IsComplex},
            (r ^ (-((2 * M : ℕ) : ℝ)) * ‖(mixedEmbedding F (ξ : F)).2 w‖ ^ (-((2 * M : ℕ) : ℝ))))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
            (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ)) := by
  classical
  choose CC hCC0 hCC using fun (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) =>
    T1JC_bound_of_le (abm j w).1 (abm j w).2.1 _
      (hC₀.image (T1_differentiable_shiftC (abm j w).2.2 (τc j w)).continuous) (2 * M) (hM j w) (2 * N)
  choose DC hDC0 hDC using fun (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) =>
    T1F5_dilation_bound_of_rpow_polyDecay_complex (T1JC (abm j w).1 (abm j w).2.1) _ (2 * M) (2 * N) (CC j w) (hCC0 j w)
      (hCC j w) (θc w) (hθc w) c₁ hc₁
  refine ⟨fun j => ∏ w, DC j w, fun j => Finset.prod_nonneg fun w _ => (hDC0 j w).le,
    fun j s hs z uu r hr hz1 hufc ξ => ?_⟩
  have hcoC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (InfiniteAdeleRing.ringEquiv_mixedSpace F
        (T1frq F ξ (z * uu) * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w
        = (r : ℂ) * ((mixedEmbedding F (ξ : F)).2 w
          * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((uu * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w) := by
    intro w
    simp only [T1frq]
    rw [T1Helpers.ringEquiv_mixedSpace_snd_mul_dilation_mul F z uu r hz1, mul_assoc (algebraMap F _ (ξ : F)),
      ← Units.val_mul, (T1F5_mixedSpace_algebraMap_mul F (ξ : F) _).2 w]
  have hξw : ∀ w : {w : InfinitePlace F // w.IsComplex}, (mixedEmbedding F (ξ : F)).2 w ≠ 0 := by
    intro w
    rw [mixedEmbedding.mixedEmbedding_apply_isComplex]
    exact (map_ne_zero _).mpr ξ.2
  have hcast : (((2 * N : ℕ) : ℝ)) = 2 * (N : ℝ) := by push_cast; ring
  simp only [T1AC]
  rw [norm_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => norm_nonneg _) fun w _ => ?_
  rw [hcoC w]
  have h := hDC j w _ ⟨s, hs, rfl⟩ r ((mixedEmbedding F (ξ : F)).2 w)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F ((uu * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w)
    hr (hξw w) (hufc w)
  rw [hcast] at h
  exact h

private theorem T1Kc_norm_le (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ x : AdeleRing (𝓞 F) F, ‖T1Kc F ψ a u x‖ ≤ K0 := by
  refine ⟨‖T1Kc F ψ a u 0‖, norm_nonneg _, fun x => le_of_eq ?_⟩
  simp only [T1Kc, norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ]

private theorem T1_sing_prod_eq (M : ℕ) (r : ℝ) (hr : 0 < r) (ξ : {ξ : F // ξ ≠ 0}) :
    (∏ i : {w : InfinitePlace F // w.IsReal}, (r ^ (-(M : ℝ)) * |(mixedEmbedding F (ξ : F)).1 i| ^ (-(M : ℝ))))
      * (∏ w : {w : InfinitePlace F // w.IsComplex},
          (r ^ (-((2 * M : ℕ) : ℝ)) * ‖(mixedEmbedding F (ξ : F)).2 w‖ ^ (-((2 * M : ℕ) : ℝ))))
      = r ^ (-((Module.finrank ℚ F : ℝ) * M)) * ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) ^ (-(M : ℝ)) := by
  have hcast2 : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring

  have HR : (∏ i : {w : InfinitePlace F // w.IsReal}, (r ^ (-(M : ℝ)) * |(mixedEmbedding F (ξ : F)).1 i| ^ (-(M : ℝ))))
      = r ^ (-((InfinitePlace.nrRealPlaces F : ℝ) * M))
        * (∏ i : {w : InfinitePlace F // w.IsReal}, |(mixedEmbedding F (ξ : F)).1 i|) ^ (-(M : ℝ)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Real.finsetProd_rpow _ _ (fun i _ => abs_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul hr.le, Finset.card_univ]
    congr 2
    simp only [InfinitePlace.nrRealPlaces]
    ring
  have HC : (∏ w : {w : InfinitePlace F // w.IsComplex},
        (r ^ (-((2 * M : ℕ) : ℝ)) * ‖(mixedEmbedding F (ξ : F)).2 w‖ ^ (-((2 * M : ℕ) : ℝ))))
      = r ^ (-(2 * (InfinitePlace.nrComplexPlaces F : ℝ) * M))
        * ((∏ w : {w : InfinitePlace F // w.IsComplex}, ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ 2) ^ (-(M : ℝ)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Real.finsetProd_rpow _ _ (fun w _ => norm_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul hr.le, Finset.card_univ, hcast2]
    congr 1
    · congr 1
      simp only [InfinitePlace.nrComplexPlaces]
      ring
    · rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Finset.prod_nonneg fun w _ => norm_nonneg _)]
      congr 1
      push_cast
      ring
  rw [HR, HC, ← T1F5_prod_abs_mul_prod_norm_sq_eq_abs_norm F (ξ : F),
    Real.mul_rpow (Finset.prod_nonneg fun i _ => abs_nonneg _)
      (pow_nonneg (Finset.prod_nonneg fun w _ => norm_nonneg _) _)]
  have hn : (Module.finrank ℚ F : ℝ) = (InfinitePlace.nrRealPlaces F : ℝ) + 2 * (InfinitePlace.nrComplexPlaces F : ℝ) := by
    rw [← InfinitePlace.card_add_two_mul_card_eq_rank]
    push_cast
    ring
  rw [hn]
  have hsplit : r ^ (-(((InfinitePlace.nrRealPlaces F : ℝ) + 2 * (InfinitePlace.nrComplexPlaces F : ℝ)) * M))
      = r ^ (-((InfinitePlace.nrRealPlaces F : ℝ) * M)) * r ^ (-(2 * (InfinitePlace.nrComplexPlaces F : ℝ) * M)) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [hsplit]
  ring

private theorem T1J_bound (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hαz : ∀ (s : ℂ) (z uu : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r → (z : AdeleRing (𝓞 F) F).2 = 1 →
      (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
      ‖((cpowChar α hα (1 / 2 - s) (z * uu) : ℂˣ) : ℂ)‖
        = r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) * ((α uu : ℝˣ) : ℝ) ^ (1 / 2 - s.re))
    (hαc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((α y : ℝˣ) : ℝ))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (ST S : Finset (HeightOneSpectrum (𝓞 F)))
    (zE : HeightOneSpectrum (𝓞 F) → ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hC : ∀ j, Differentiable ℂ (C j))
    (hP : Differentiable ℂ (T1P F ST S zE))
    (hFb : ∀ (U : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact U → ∀ R : ℝ,
      ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (c₀ c : ℝ), 0 < c₀ ∧ 0 ≤ c ∧
        (∀ ξ : F, ξ ∈ I → ξ ≠ 0 → c₀ ≤ ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ∧
        ∀ (j : Fin n) (s : ℂ), ‖s‖ ≤ R → ∀ u ∈ U, ∀ ξ : F, ξ ≠ 0 →
          (ξ ∉ I → ∏ᶠ v : HeightOneSpectrum (𝓞 F),
              Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (u : AdeleRing (𝓞 F) F)).2 v) s = 0) ∧
          ‖∏ᶠ v : HeightOneSpectrum (𝓞 F),
              Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (u : AdeleRing (𝓞 F) F)).2 v) s‖
            ≤ c * (max 1 ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) ^ k)
    (C₀ : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ) (hC₀ : IsCompact C₀) (hU : IsCompact U) :
    ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (A : ℝ) (q : ℂ → ℝ),
      (∀ s ∈ C₀, |q s| ≤ A) ∧
      ∀ N : ℕ, ∃ c : ℝ,
        ∀ s ∈ C₀, ∀ uu ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r → (z : AdeleRing (𝓞 F) F).2 = 1 →
          (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
          ∀ ξ : {ξ : F // ξ ≠ 0},
            ((ξ : F) ∉ I → T1J F α hα ν ψ ST S zE n C kdat τr abm τc θr θc a u Φ ξ s (z * uu) = 0) ∧
            ‖T1J F α hα ν ψ ST S zE n C kdat τr abm τc θr θc a u Φ ξ s (z * uu)‖
              ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - q s)) *
                (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                ∏ w : {w : InfinitePlace F // w.IsComplex},
                  (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ)) := by
  classical

  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn continuousOn_id

  have hUa : IsCompact ((fun uu : (AdeleRing (𝓞 F) F)ˣ => uu * a⁻¹) '' U) :=
    hU.image (continuous_id.mul continuous_const)
  obtain ⟨c₁, c₂, hc₁, hcoord⟩ := T1Helpers.exists_mixedSpace_coord_bounds_of_isCompact F _ hUa
  obtain ⟨k, I, c₀, cF, hc₀, hcF0, hc₀I, hF⟩ := hFb _ hUa R

  set MR : Fin n → {w : InfinitePlace F // w.IsReal} → ℕ := fun j i =>
    ((T1JR_spec (kdat j i)).2.2.2 _ (hC₀.image (T1_differentiable_shiftR (τr j i)).continuous)).choose with hMR
  set MC : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ := fun j w =>
    ((T1JC_spec (abm j w).1 (abm j w).2.1).2.2.2 _
      (hC₀.image (T1_differentiable_shiftC (abm j w).2.2 (τc j w)).continuous)).choose with hMC
  set M : ℕ := (Finset.univ.sup fun p : Fin n × {w : InfinitePlace F // w.IsReal} => MR p.1 p.2)
    + Finset.univ.sup fun p : Fin n × {w : InfinitePlace F // w.IsComplex} => MC p.1 p.2 with hMdef
  have hMRle : ∀ j i, MR j i ≤ M := fun j i =>
    (Finset.le_sup (f := fun p : Fin n × {w : InfinitePlace F // w.IsReal} => MR p.1 p.2)
      (Finset.mem_univ (j, i))).trans (Nat.le_add_right _ _)
  have hM2 : M ≤ 2 * M := by omega
  have hMCle : ∀ j w, MC j w ≤ 2 * M := fun j w =>
    ((Finset.le_sup (f := fun p : Fin n × {w : InfinitePlace F // w.IsComplex} => MC p.1 p.2)
      (Finset.mem_univ (j, w))).trans (Nat.le_add_left _ _)).trans hM2

  obtain ⟨Rre, hRre⟩ := hC₀.exists_bound_of_continuousOn Complex.continuous_re.continuousOn
  refine ⟨k, I, |Rre| + M, fun s => s.re + M, fun s hs => ?_, fun N => ?_⟩
  · have h := hRre s hs
    rw [Real.norm_eq_abs] at h
    calc |s.re + (M : ℝ)| ≤ |s.re| + |(M : ℝ)| := abs_add_le _ _
      _ ≤ |Rre| + M := add_le_add (h.trans (le_abs_self _)) (le_of_eq (abs_of_nonneg (Nat.cast_nonneg M)))

  obtain ⟨DR, hDR0, hDR⟩ := T1AR_dilation_bound n kdat τr θr hθr a C₀ hC₀ M hMRle c₁ hc₁ N
  obtain ⟨DC, hDC0, hDC⟩ := T1AC_dilation_bound n abm τc θc hθc a C₀ hC₀ M hMCle c₁ hc₁ N

  choose BC hBC using fun j : Fin n => hC₀.exists_bound_of_continuousOn (hC j).continuous.continuousOn
  obtain ⟨BE, hBE⟩ := hC₀.exists_bound_of_continuousOn hP.continuous.continuousOn
  have hcontA : ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((α p.2 : ℝˣ) : ℝ) ^ (1 / 2 - p.1.re))
      (C₀ ×ˢ U) := by
    refine Continuous.continuousOn ?_
    exact (hαc.comp continuous_snd).rpow (continuous_const.sub (Complex.continuous_re.comp continuous_fst))
      fun p => Or.inl (hα p.2).ne'
  obtain ⟨BA, hBA⟩ := (hC₀.prod hU).exists_bound_of_continuousOn hcontA
  obtain ⟨K0, hK00, hK0⟩ := T1Kc_norm_le ψ hψ a u

  set c : ℝ := |BA| * (c₀ ^ (-(M : ℝ))) * ∑ j : Fin n, |BC j| * K0 * DR j * DC j * (|BE| * cF) with hc
  refine ⟨c, fun s hs uu huu z r hr hz2 hz1 ξ => ?_⟩
  have hsR : ‖s‖ ≤ R := hR s hs
  set uf : (AdeleRing (𝓞 F) F)ˣ := uu * a⁻¹ with huf
  have hufmem : uf ∈ (fun uu : (AdeleRing (𝓞 F) F)ˣ => uu * a⁻¹) '' U := ⟨uu, huu, rfl⟩
  have hufc := hcoord uf hufmem

  have hFi : ∀ j, T1Fi F n Φ a j s (T1frq F ξ (z * uu))
      = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (uf : AdeleRing (𝓞 F) F)).2 v) s := by
    intro j
    simp only [T1Fi, T1frq]
    refine finprod_congr fun v => ?_
    rw [T1Helpers.snd_mul_dilation_mul_apply F z uu hz2, huf, Units.val_mul, mul_assoc]
  have hFj := fun j => hF j s hsR uf hufmem (ξ : F) ξ.2
  constructor
  ·
    intro hξI
    have hzero : ∀ j, T1Fi F n Φ a j s (T1frq F ξ (z * uu)) = 0 := fun j => by
      rw [hFi j]
      exact (hFj j).1 hξI
    simp only [T1J, hzero, mul_zero, Finset.sum_const_zero]
  ·
    set PR : ℝ := ∏ i : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 i|) ^ (-(N : ℝ))
      with hPR
    set PC : ℝ := ∏ w : {w : InfinitePlace F // w.IsComplex},
        (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ)) with hPC
    set MX : ℝ := (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k with hMX
    set SR : ℝ := ∏ i : {w : InfinitePlace F // w.IsReal},
        (r ^ (-(M : ℝ)) * |(mixedEmbedding F (ξ : F)).1 i| ^ (-(M : ℝ))) with hSR
    set SC : ℝ := ∏ w : {w : InfinitePlace F // w.IsComplex},
        (r ^ (-((2 * M : ℕ) : ℝ)) * ‖(mixedEmbedding F (ξ : F)).2 w‖ ^ (-((2 * M : ℕ) : ℝ))) with hSC
    have hPR0 : 0 ≤ PR := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
    have hPC0 : 0 ≤ PC := Finset.prod_nonneg fun w _ => Real.rpow_nonneg (by positivity) _
    have hMX0 : 0 ≤ MX := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) k
    have hSR0 : 0 ≤ SR := Finset.prod_nonneg fun i _ =>
      mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg (abs_nonneg _) _)
    have hSC0 : 0 ≤ SC := Finset.prod_nonneg fun w _ =>
      mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg (norm_nonneg _) _)
    have hS0 : 0 ≤ ∑ j : Fin n, |BC j| * K0 * DR j * DC j * (|BE| * cF) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hK00)
        (hDR0 j)) (hDC0 j)) (mul_nonneg (abs_nonneg _) hcF0)
    have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hc₀.le _)) hS0
    by_cases hξI : (ξ : F) ∈ I
    swap
    · have hzero : ∀ j, T1Fi F n Φ a j s (T1frq F ξ (z * uu)) = 0 := fun j => by
        rw [hFi j]
        exact (hFj j).1 hξI
      simp only [T1J, hzero, mul_zero, Finset.sum_const_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg hr.le _)) hMX0) hPR0) hPC0
    have hNξ : c₀ ≤ ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) := hc₀I (ξ : F) hξI ξ.2

    have hARb : ∀ j, ‖T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu))‖ ≤ DR j * SR * PR :=
      fun j => hDR j s hs z uu r hr hz1 (fun i => (hufc.1 i).1) ξ
    have hACb : ∀ j, ‖T1AC F n abm τc θc a j s (T1frq F ξ (z * uu))‖ ≤ DC j * SC * PC :=
      fun j => hDC j s hs z uu r hr hz1 (fun w => (hufc.2 w).1) ξ
    have hKcb : ‖T1Kc F ψ a u (T1frq F ξ (z * uu))‖ ≤ K0 := hK0 _
    have hEub : ‖T1P F ST S zE s‖ ≤ |BE| := (hBE s hs).trans (le_abs_self _)
    have hCb : ∀ j, ‖C j s‖ ≤ |BC j| := fun j => (hBC j s hs).trans (le_abs_self _)
    have hFib : ∀ j, ‖T1Fi F n Φ a j s (T1frq F ξ (z * uu))‖ ≤ cF * MX := fun j => by
      rw [hFi j]
      exact (hFj j).2
    have hcpb : ‖((cpowChar α hα (1 / 2 - s) (z * uu) : ℂˣ) : ℂ)‖
        ≤ r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) * |BA| := by
      rw [hαz s z uu r hr hz2 hz1]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr.le _)
      have h := hBA (s, uu) ⟨hs, huu⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hα uu).le _)] at h
      exact h.trans (le_abs_self _)

    have hterm : ∀ j, ‖C j s * T1Kc F ψ a u (T1frq F ξ (z * uu)) * T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu))
        * T1AC F n abm τc θc a j s (T1frq F ξ (z * uu)) * (T1P F ST S zE s * T1Fi F n Φ a j s (T1frq F ξ (z * uu)))‖
        ≤ (|BC j| * K0 * DR j * DC j * (|BE| * cF)) * ((SR * SC) * (PR * PC * MX)) := by
      intro j
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
      have n1 : 0 ≤ |BC j| * K0 := mul_nonneg (abs_nonneg _) hK00
      have n2 : 0 ≤ |BC j| * K0 * (DR j * SR * PR) := mul_nonneg n1 (mul_nonneg (mul_nonneg (hDR0 j) hSR0) hPR0)
      have n3 : 0 ≤ |BC j| * K0 * (DR j * SR * PR) * (DC j * SC * PC) :=
        mul_nonneg n2 (mul_nonneg (mul_nonneg (hDC0 j) hSC0) hPC0)
      have h1 := mul_le_mul (hCb j) hKcb (norm_nonneg _) (abs_nonneg _)
      have h2 := mul_le_mul h1 (hARb j) (norm_nonneg _) n1
      have h3 := mul_le_mul h2 (hACb j) (norm_nonneg _) n2
      have h4 := mul_le_mul hEub (hFib j) (norm_nonneg _) (abs_nonneg _)
      have h5 := mul_le_mul h3 h4 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) n3
      refine h5.trans (le_of_eq ?_)
      ring

    have hsing : SR * SC ≤ r ^ (-((Module.finrank ℚ F : ℝ) * M)) * c₀ ^ (-(M : ℝ)) := by
      rw [hSR, hSC, T1_sing_prod_eq M r hr ξ]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc₀ hNξ (by simp)) (Real.rpow_nonneg hr.le _)

    have hJ : T1J F α hα ν ψ ST S zE n C kdat τr abm τc θr θc a u Φ ξ s (z * uu)
        = ((ν (z * uu) : ℂˣ) : ℂ) * ((cpowChar α hα (1 / 2 - s) (z * uu) : ℂˣ) : ℂ)
          * ∑ j : Fin n, C j s * T1Kc F ψ a u (T1frq F ξ (z * uu))
          * T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu)) * T1AC F n abm τc θc a j s (T1frq F ξ (z * uu))
          * (T1P F ST S zE s * T1Fi F n Φ a j s (T1frq F ξ (z * uu))) := rfl
    rw [hJ, norm_mul, norm_mul, hν (z * uu), one_mul]
    have hsum : ‖∑ j : Fin n, C j s * T1Kc F ψ a u (T1frq F ξ (z * uu))
          * T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu)) * T1AC F n abm τc θc a j s (T1frq F ξ (z * uu))
          * (T1P F ST S zE s * T1Fi F n Φ a j s (T1frq F ξ (z * uu)))‖
        ≤ ∑ j : Fin n, (|BC j| * K0 * DR j * DC j * (|BE| * cF)) * ((SR * SC) * (PR * PC * MX)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    have hsum' : ‖∑ j : Fin n, C j s * T1Kc F ψ a u (T1frq F ξ (z * uu))
          * T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu)) * T1AC F n abm τc θc a j s (T1frq F ξ (z * uu))
          * (T1P F ST S zE s * T1Fi F n Φ a j s (T1frq F ξ (z * uu)))‖
        ≤ (∑ j : Fin n, |BC j| * K0 * DR j * DC j * (|BE| * cF))
          * ((r ^ (-((Module.finrank ℚ F : ℝ) * M)) * c₀ ^ (-(M : ℝ))) * (PR * PC * MX)) := by
      refine hsum.trans ?_
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_left ?_ hS0
      exact mul_le_mul_of_nonneg_right hsing (mul_nonneg (mul_nonneg hPR0 hPC0) hMX0)
    have hpow : r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) * r ^ (-((Module.finrank ℚ F : ℝ) * M))
        = r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - (s.re + M))) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    refine (mul_le_mul hcpb hsum' (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _))).trans
      (le_of_eq ?_)
    rw [hc, ← hpow]
    ring

end T1Main

section EulerBook

open NumberField NumberField.TateGlobal NumberField.AdelicLevel IsDedekindDomain
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

private theorem T1E_localChar_uniformizer_eq (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F))
    (hv : IsUnramifiedCharAt χ v) (ϖ ϖ' : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hϖ' : Valued.v (ϖ' : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    localChar χ v ϖ' = localChar χ v ϖ := by
  have hunit : localChar χ v (ϖ' * ϖ⁻¹) = 1 := by
    have hv1 : Valued.v (((ϖ' * ϖ⁻¹ : (v.adicCompletion F)ˣ)) : v.adicCompletion F) = 1 := by
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hϖ, hϖ']
      exact mul_inv_cancel₀ (by simp)
    have hv2 : Valued.v ((((ϖ' * ϖ⁻¹)⁻¹ : (v.adicCompletion F)ˣ)) : v.adicCompletion F) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hv1, inv_one]
    refine hv _ ?_ ?_
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hv1.le
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hv2.le
  calc localChar χ v ϖ' = localChar χ v (ϖ' * ϖ⁻¹ * ϖ) := by rw [inv_mul_cancel_right]
    _ = localChar χ v ϖ := by rw [map_mul, hunit, one_mul]

end EulerBook

section Final

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.InfinitePlace AutomorphicForm
open AutomorphicForm.WindowedSiegel Filter Topology NumberField.TateGlobal
open NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), S₀ ⊆ S →
      ∀ (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
        (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) →
      ∃ 𝒥 : {ξ : F // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ,
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ),
          Differentiable ℂ (fun s => 𝒥 ξ s y)) ∧
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ), 1 < s.re →
          𝒥 ξ s y
            = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                  * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹)
              * whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) (diagOne y)) ∧
        (∀ ξ : {ξ : F // ξ ≠ 0}, Continuous (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => 𝒥 ξ p.1 p.2)) ∧
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ),
          𝒥 ξ s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
            = 𝒥 ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y) ∧
        (∀ (C : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact C → IsCompact U →
          ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (A : ℝ) (q : ℂ → ℝ),
            (∀ s ∈ C, |q s| ≤ A) ∧
            ∀ N : ℕ, ∃ c : ℝ,
              ∀ s ∈ C, ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r →
                (z : AdeleRing (𝓞 F) F).2 = 1 →
                (∀ w : InfinitePlace F,
                  Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
                ∀ ξ : {ξ : F // ξ ≠ 0},
                  ((ξ : F) ∉ I → 𝒥 ξ s (z * u) = 0) ∧
                  ‖𝒥 ξ s (z * u)‖ ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - q s)) *
                    (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                    (∏ w : {w : InfinitePlace F // w.IsReal},
                      (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                    ∏ w : {w : InfinitePlace F // w.IsComplex},
                      (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ))) := by
  intro α hα μ ν hμ hν hμF hνF ψ hψ φ hφ hφK hφf hφjc hφhol hφflat E
  classical
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F

  by_cases hne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0
  swap
  · push Not at hne
    refine ⟨∅, fun S _ ϖ _ => ⟨fun _ _ _ => 0, fun _ _ => differentiable_const _, ?_, fun _ => continuous_const,
      fun _ _ _ _ => rfl, ?_⟩⟩
    · intro ξ s y _
      have hE : E s = fun _ => (0 : ℂ) := by
        funext g
        simp only [E, hne, tsum_zero, add_zero]
      rw [hE, whittakerCoefficient_zero, mul_zero]
    · intro C U _ _
      refine ⟨0, 1, 0, fun _ => 0, fun _ _ => by simp, fun N => ⟨0, fun s _ u _ z r _ _ _ ξ => ⟨fun _ => rfl, ?_⟩⟩⟩
      simp only [norm_zero, zero_mul, le_refl]

  obtain ⟨ψv, nψ, θr, θc, hψv, hψv', hnψfin, hψfin, hθr, hθc, hψarch⟩ :=
    AutomorphicForm.exists_localComponents_of_isGlobalAddChar F ψ hψ
  have hψarch' : ∀ p : mixedEmbedding.mixedSpace F,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal}, Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
            Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)) := fun p => by
    rw [hψarch p, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]
  have hϖex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ϖ : (v.adicCompletion F)ˣ,
      Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
    intro v
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    have hπ0 : (π : v.adicCompletion F) ≠ 0 := by
      intro h0
      have : Valued.v ((π : F) : v.adicCompletion F) = 0 := by rw [h0, map_zero]
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ] at this
      exact WithZero.coe_ne_zero this
    refine ⟨Units.mk0 _ hπ0, ?_⟩
    rw [Units.val_mk0, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
    rfl
  choose ϖ₀ hϖ₀ using hϖex
  obtain ⟨ST, n, C, kdat, τr, abm, τc, a, u, thr, Φ, hC, habm, hthr, hΦd, hΦ1, hΦ0, hΦb, hΦlc, hform⟩ :=
    AutomorphicForm.whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family_of_unitary
      F hα μ ν hμ hν hμF hνF ψ hψ ψv nψ hnψfin hψv hψv' hψfin θr hθr θc hθc hψarch' ϖ₀ hϖ₀ φ hφ hφK hφf hφjc
      hφhol hφflat hne

  have hαc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((α y : ℝˣ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)
  have hcp : ∀ t : ℂ, Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((cpowChar α hα t y : ℂˣ) : ℂ) := by
    intro t
    simp only [cpowChar_apply_val]
    exact hαc.cpow continuous_const fun y => Complex.ofReal_mem_slitPlane.mpr (hα y)
  obtain ⟨hμc, hνc⟩ : Continuous μ ∧ Continuous ν := by
    obtain ⟨s₀, g₀, h0⟩ := hne
    obtain ⟨h1, h2⟩ := AutomorphicForm.continuous_of_isInducedSection_of_continuous_of_apply_ne_zero F
      (etaFst μ α hα s₀) (etaSnd ν α hα s₀) (φ s₀) (hφ s₀) (hφjc.comp (continuous_const.prodMk continuous_id))
      ⟨g₀, h0⟩
    have hunits : ∀ (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ),
        (Continuous fun y => ((χ y : ℂˣ) : ℂ)) → Continuous χ := by
      intro χ h
      refine Units.continuous_iff.2 ⟨h, ?_⟩
      show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((χ y)⁻¹ : ℂˣ) : ℂ)
      simp_rw [← map_inv]
      exact h.comp continuous_inv
    have h1' : Continuous fun y => ((etaFst μ α hα s₀ y : ℂˣ) : ℂ) := Units.continuous_val.comp h1
    have h2' : Continuous fun y => ((etaSnd ν α hα s₀ y : ℂˣ) : ℂ) := Units.continuous_val.comp h2
    simp only [etaFst_apply, etaSnd_apply, Units.val_mul] at h1' h2'
    refine ⟨hunits μ ?_, hunits ν ?_⟩
    · exact (h1'.div (hcp (s₀ + 1 / 2)) fun y => (cpowChar α hα _ y).ne_zero).congr fun y => by
        rw [Pi.div_apply, mul_div_assoc, div_self (cpowChar α hα _ y).ne_zero, mul_one]
    · exact (h2'.div (hcp (-(s₀ + 1 / 2))) fun y => (cpowChar α hα _ y).ne_zero).congr fun y => by
        rw [Pi.div_apply, mul_div_assoc, div_self (cpowChar α hα _ y).ne_zero, mul_one]
  have hχc : Continuous (μ * ν⁻¹) := by
    show Continuous fun x => (μ * ν⁻¹) x
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    exact hμc.mul hνc.inv
  obtain ⟨Sram, hSram⟩ :=
    NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous F (μ * ν⁻¹) hχc

  obtain ⟨hFi, hFb⟩ :=
    AutomorphicForm.continuous_finprod_localFactor_and_exists_fractionalIdeal_norm_finprod_le_of_isCompact F ST n thr
      Φ hthr hΦd hΦ1 hΦ0 hΦb hΦlc
  set zE : HeightOneSpectrum (𝓞 F) → ℂ :=
    fun v => ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v (ϖ₀ v) : ℂˣ) : ℂ) with hzdef
  have hzE1 : ∀ (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ),
      ‖((NumberField.TateGlobal.localChar (μ * ν⁻¹) v t : ℂˣ) : ℂ)‖ ≤ 1 := by
    intro v t
    simp only [NumberField.TateGlobal.localChar, MonoidHom.comp_apply, MonoidHom.mul_apply,
      MonoidHom.inv_apply, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hμ _, hν _]
    norm_num

  refine ⟨ST ∪ Sram, fun S hS ϖ hϖ => ?_⟩
  have hSTS : ST ⊆ S := Finset.subset_union_left.trans hS
  have hSramS : Sram ⊆ S := Finset.subset_union_right.trans hS
  have hP : Differentiable ℂ (T1P F ST S zE) := T1P_differentiable ST S zE
  refine ⟨T1J F α hα ν ψ ST S zE n C kdat τr abm τc θr θc a u Φ, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro ξ y
    exact T1J_differentiable α hα ν ψ ST S zE n C kdat τr abm τc θr hθr θc hθc a u Φ hC hΦd hΦ1 ξ y
  ·
    intro ξ s y hs
    have hs0 : 0 < s.re := by linarith

    have hs2 : 1 < (2 * s + 1).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re]
      linarith
    set f : HeightOneSpectrum (𝓞 F) → ℂ := fun v => 1 - zE v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))
      with hfdef
    set L : ℂ := ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (f v.1)⁻¹ with hLdef
    have hLeq : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹) = L := by
      refine tprod_congr fun v => ?_
      have hvram : v.1 ∉ Sram := fun h => v.2 (hSramS h)
      simp only [hfdef, hzdef]
      rw [T1E_localChar_uniformizer_eq (μ * ν⁻¹) v.1 (hSram v.1 hvram) (ϖ₀ v.1) (ϖ v.1) (hϖ₀ v.1) (hϖ v.1)]
    have hEu : T1P F ST S zE s = L * T1Eu ST zE s := by
      simp only [T1P, T1Eu, hLdef, hfdef]
      exact (NumberField.tprod_inv_eulerFactor_mul_tprod_eulerFactor_eq_prod_sdiff_of_norm_le_one F ST S hSTS zE
        (fun v => hzE1 v _) (2 * s + 1) hs2).symm
    rw [hLeq, T1J_eq_mul_T1Jh α hα ν ψ ST S zE n C kdat τr abm τc θr hθr θc hθc habm a u Φ ξ s hs0 y L hEu]
    congr 1

    rw [hform s hs ξ.1 ξ.2 y]
    simp only [T1Jh, T1Kc, T1ARh, T1ACh, T1Eu, T1Fi, T1frq, T1jR, T1jC]
    rfl
  ·
    intro ξ
    exact T1J_continuous α hα hαc ν hνc ψ hψ ST S zE n C kdat τr abm τc θr hθr θc hθc a u Φ hC hP hFi ξ
  ·
    intro ξ η s y
    exact T1J_principal α hα (T1Helpers.cpowChar_modulus_principal F hα) ν hνF ψ ST S zE n C kdat τr abm τc θr θc
      a u Φ ξ η s y
  ·
    intro C₀ U hC₀ hU
    have hαz := fun (s : ℂ) (z uu : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ) (hr : 0 < r)
        (hz2 : (z : AdeleRing (𝓞 F) F).2 = 1)
        (hz1 : ∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) =>
      T1Helpers.norm_cpowChar_dilation_mul F z uu r hr hz2 hz1 s hα
    have hαc' : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((α y : ℝˣ) : ℝ) :=
      NumberField.TateGlobal.continuous_ideleNorm F
    exact T1J_bound α hα ν hν hαz hαc' ψ hψ ST S zE n C kdat τr abm τc θr hθr θc hθc a u Φ hC hP hFb C₀ U hC₀ hU

end Final

end S_AutomorphicForm_exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary
end P2MW
export P2MW.S_AutomorphicForm_exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary (solution)
