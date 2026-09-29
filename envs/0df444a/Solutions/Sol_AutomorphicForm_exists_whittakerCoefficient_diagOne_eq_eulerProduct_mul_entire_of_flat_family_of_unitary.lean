-- Prove2me | solution 1 for AutomorphicForm.exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d4a2c96f-538b-59a7-bfba-71d6e0d25aa1

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Integral.Pi
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
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
import Theorems.Thm_AutomorphicForm_RealIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one

import Theorems.Thm_AutomorphicForm_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family_of_unitary
import Theorems.Thm_AutomorphicForm_RealIwasawa_exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra"
p2m_attr_erase "instance" "HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval"
p2m_attr_erase "simp" "TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LocalGL2.swapUnit_val"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

namespace T1Helpers

section B1

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

private theorem adelicWeyl_val [MeasurableSpace (AdeleRing R K)] :
    ((adelicWeyl R K : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) = !![0, 1; 1, 0] := by
  ext i j
  rw [show adelicWeyl R K = globalPoints R K gl2Weyl from rfl, globalPoints_apply, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_val {A : Type*} [CommRing A] (a : Aˣ) :
    ((diagOne a : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(a : A), 0; 0, 1] := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_inv_val {A : Type*} [CommRing A] (a : Aˣ) :
    (((diagOne a)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![((a⁻¹ : Aˣ) : A), 0; 0, 1] := by
  rw [← map_inv, diagOne_val]

private theorem centralScalar_val (z : (AdeleRing R K)ˣ) :
    ((centralScalar R K z : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = !![(z : AdeleRing R K), 0; 0, (z : AdeleRing R K)] := by
  change Matrix.scalar (Fin 2) (z : AdeleRing R K) = _
  ext i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagOne_mem_adelicBorel (y : (AdeleRing R K)ˣ) : (diagOne y : AdelicGL2 R K) ∈ adelicBorel R K := by
  show ((diagOne y : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 0 = 0
  rw [diagOne_val]
  simp

private theorem centralScalar_mul_diagOne_inv_mem_adelicBorel (y : (AdeleRing R K)ˣ) :
    centralScalar R K y * (diagOne y)⁻¹ ∈ adelicBorel R K :=
  (adelicBorel R K).mul_mem (centralScalar_mem_adelicBorel R K y)
    ((adelicBorel R K).inv_mem (diagOne_mem_adelicBorel R K y))

private theorem centralScalar_mul_diagOne_inv_val (y : (AdeleRing R K)ˣ) :
    ((centralScalar R K y * (diagOne y)⁻¹ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = !![1, 0; 0, (y : AdeleRing R K)] := by
  rw [Units.val_mul, centralScalar_val, diagOne_inv_val, Matrix.mul_fin_two]
  simp

private theorem borelDiagFst_centralScalar_mul_diagOne_inv (y : (AdeleRing R K)ˣ) :
    borelDiagFst (⟨centralScalar R K y * (diagOne y)⁻¹, centralScalar_mul_diagOne_inv_mem_adelicBorel R K y⟩ :
      ↥(adelicBorel R K)) = 1 := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((centralScalar R K y * (diagOne y)⁻¹ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 0 0 = 1
  rw [centralScalar_mul_diagOne_inv_val]
  simp

private theorem borelDiagSnd_centralScalar_mul_diagOne_inv (y : (AdeleRing R K)ˣ) :
    borelDiagSnd (⟨centralScalar R K y * (diagOne y)⁻¹, centralScalar_mul_diagOne_inv_mem_adelicBorel R K y⟩ :
      ↥(adelicBorel R K)) = y := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((centralScalar R K y * (diagOne y)⁻¹ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) 1 1 = y
  rw [centralScalar_mul_diagOne_inv_val]
  simp

private theorem adelicWeyl_mul_unipotentGL2_mul_diagOne [MeasurableSpace (AdeleRing R K)]
    (y : (AdeleRing R K)ˣ) (x : AdeleRing R K) :
    adelicWeyl R K * unipotentGL2 x * diagOne y
      = (centralScalar R K y * (diagOne y)⁻¹) *
          (adelicWeyl R K * unipotentGL2 (((y⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K) * x)) := by
  apply Units.ext
  change ((adelicWeyl R K : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
        * ((unipotentGL2 x : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
        * ((diagOne y : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
      = ((centralScalar R K y * (diagOne y)⁻¹ : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
        * (((adelicWeyl R K : AdelicGL2 R K) : Matrix (Fin 2) (Fin 2) (AdeleRing R K))
          * ((unipotentGL2 (((y⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K) * x) : AdelicGL2 R K) :
              Matrix (Fin 2) (Fin 2) (AdeleRing R K)))
  rw [centralScalar_mul_diagOne_inv_val, adelicWeyl_val, unipotentGL2_coe, unipotentGL2_coe, diagOne_val,
    Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1 <;> simp

private theorem exists_borel_adelicWeyl_mul_unipotentGL2_mul_diagOne [MeasurableSpace (AdeleRing R K)]
    (y : (AdeleRing R K)ˣ) (x : AdeleRing R K) :
    ∃ (B : AdelicGL2 R K) (hB : B ∈ adelicBorel R K),
      borelDiagFst (⟨B, hB⟩ : ↥(adelicBorel R K)) = 1 ∧ borelDiagSnd (⟨B, hB⟩ : ↥(adelicBorel R K)) = y ∧
      adelicWeyl R K * unipotentGL2 x * diagOne y
        = B * (adelicWeyl R K * unipotentGL2 (((y⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K) * x)) :=
  ⟨_, centralScalar_mul_diagOne_inv_mem_adelicBorel R K y, borelDiagFst_centralScalar_mul_diagOne_inv R K y,
    borelDiagSnd_centralScalar_mul_diagOne_inv R K y, adelicWeyl_mul_unipotentGL2_mul_diagOne R K y x⟩

private theorem apply_adelicWeyl_mul_unipotentGL2_mul_diagOne_of_isInducedSection [MeasurableSpace (AdeleRing R K)]
    (α : (AdeleRing R K)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
    {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
    (y : (AdeleRing R K)ˣ) (x : AdeleRing R K) :
    φ (adelicWeyl R K * unipotentGL2 x * diagOne y)
      = ((cpowChar α hα (-(s + 1 / 2)) y : ℂˣ) : ℂ) *
          φ (adelicWeyl R K * unipotentGL2 (((y⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K) * x) * 1) := by
  rw [mul_one, adelicWeyl_mul_unipotentGL2_mul_diagOne R K y x,
    hφ _ (centralScalar_mul_diagOne_inv_mem_adelicBorel R K y),
    borelDiagFst_centralScalar_mul_diagOne_inv, borelDiagSnd_centralScalar_mul_diagOne_inv, map_one,
    Units.val_one, one_mul, etaSnd_apply, MonoidHom.one_apply, one_mul]

end B1

end T1Helpers

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
  | ih y => rw [Completion.extensionEmbedding_coe, Completion.extensionEmbeddingOfIsReal_coe, embedding_of_isReal_apply]

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

end T1Helpers

namespace T1Helpers

section B3

open IsDedekindDomain NumberField.InfinitePlace

variable (F : Type) [Field F] [NumberField F]

private theorem snd_apply_mul_inv_snd_apply (u : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (u : AdeleRing (𝓞 F) F).2 v * ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) u.mul_inv
  exact h

private theorem fst_apply_mul_inv_fst_apply (u : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (u : AdeleRing (𝓞 F) F).1 w * ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 := by
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) u.mul_inv
  exact h

private theorem valued_algebraMap_mul_apply (s : 𝓞 F) (y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * y) v) = v.intValuation s * Valued.v (y v) := by
  have h : (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * y) v
      = ((algebraMap (𝓞 F) F s : F) : v.adicCompletion F) * y v := rfl
  rw [h, map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

private theorem exists_finite_support_valuation_bounds_of_isCompact (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) :
    ∃ L : HeightOneSpectrum (𝓞 F) → ℤ, (Function.support L).Finite ∧ (∀ v, 0 ≤ L v) ∧
      ∀ u ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
        WithZero.exp (-(L v)) ≤ Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ∧
        Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (L v) := by

  have hC : IsCompact ((fun u : (AdeleRing (𝓞 F) F)ˣ => (u : AdeleRing (𝓞 F) F).2) '' U) :=
    hU.image (continuous_snd.comp Units.continuous_val)
  have hC' : IsCompact ((fun u : (AdeleRing (𝓞 F) F)ˣ => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) '' U) :=
    hU.image (continuous_snd.comp Units.continuous_coe_inv)
  obtain ⟨s, hs0, hs⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact (𝓞 F) F hC
  obtain ⟨s', hs'0, hs'⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact (𝓞 F) F hC'

  set n : HeightOneSpectrum (𝓞 F) → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 F))).factors with hn
  set n' : HeightOneSpectrum (𝓞 F) → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {s'} : Ideal (𝓞 F))).factors with hn'
  have hns : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation s = WithZero.exp (-(n v : ℤ)) :=
    fun v => v.intValuation_if_neg hs0
  have hns' : ∀ v : HeightOneSpectrum (𝓞 F), v.intValuation s' = WithZero.exp (-(n' v : ℤ)) :=
    fun v => v.intValuation_if_neg hs'0

  have hvan : ∀ (r : 𝓞 F) (hr : r ≠ 0) (m : HeightOneSpectrum (𝓞 F) → ℕ),
      (∀ v : HeightOneSpectrum (𝓞 F), v.intValuation r = WithZero.exp (-(m v : ℤ))) →
      ∀ v, m v ≠ 0 → v.asIdeal ∣ Ideal.span {r} := by
    intro r hr m hm v hv
    rw [← HeightOneSpectrum.intValuation_lt_one_iff_dvd, hm v, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨fun v => (n v : ℤ) + (n' v : ℤ), ?_, fun v => by positivity, ?_⟩
  · have hfin := (Ideal.finite_factors (I := Ideal.span {s}) (by simpa using hs0)).union
      (Ideal.finite_factors (I := Ideal.span {s'}) (by simpa using hs'0))
    refine hfin.subset ?_
    intro v hv
    simp only [Function.mem_support, ne_eq] at hv
    by_cases h1 : n v = 0
    · right
      exact hvan s' hs'0 n' hns' v (by omega)
    · left
      exact hvan s hs0 n hns v h1
  · intro u hu v
    have hup : ∀ (r : 𝓞 F) (m : ℕ) (y : FiniteAdeleRing (𝓞 F) F),
        v.intValuation r = WithZero.exp (-(m : ℤ)) →
        (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r * y) v ∈ HeightOneSpectrum.adicCompletionIntegers F v →
        Valued.v (y v) ≤ WithZero.exp (m : ℤ) := by
      intro r m y hr hint
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap_mul_apply, hr] at hint
      calc Valued.v (y v) = WithZero.exp (m : ℤ) * (WithZero.exp (-(m : ℤ)) * Valued.v (y v)) := by
            rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
        _ ≤ WithZero.exp (m : ℤ) * 1 := mul_le_mul_right hint _
        _ = WithZero.exp (m : ℤ) := mul_one _
    have h1 : Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (n v : ℤ) :=
      hup s (n v) _ (hns v) (hs _ ⟨u, hu, rfl⟩ v)
    have h2 : Valued.v (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (n' v : ℤ) :=
      hup s' (n' v) _ (hns' v) (hs' _ ⟨u, hu, rfl⟩ v)
    have hmul : Valued.v ((u : AdeleRing (𝓞 F) F).2 v) *
        Valued.v (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) = 1 := by
      rw [← map_mul, snd_apply_mul_inv_snd_apply, map_one]
    constructor
    · calc WithZero.exp (-((n v : ℤ) + (n' v : ℤ)))
          ≤ WithZero.exp (-(n' v : ℤ)) := by
            rw [WithZero.exp_le_exp]
            omega
        _ = Valued.v ((u : AdeleRing (𝓞 F) F).2 v) *
              (WithZero.exp (-(n' v : ℤ)) * Valued.v (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)) := by
            rw [mul_left_comm, hmul, mul_one]
        _ ≤ Valued.v ((u : AdeleRing (𝓞 F) F).2 v) * 1 := by
            refine mul_le_mul_right ?_ _
            calc WithZero.exp (-(n' v : ℤ)) * Valued.v (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
                ≤ WithZero.exp (-(n' v : ℤ)) * WithZero.exp (n' v : ℤ) := mul_le_mul_right h2 _
              _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
        _ = Valued.v ((u : AdeleRing (𝓞 F) F).2 v) := mul_one _
    · calc Valued.v ((u : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (n v : ℤ) := h1
        _ ≤ WithZero.exp ((n v : ℤ) + (n' v : ℤ)) := by
            rw [WithZero.exp_le_exp]
            omega

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

end T1Helpers

namespace T1Helpers

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

private theorem snd_dilation_mul_apply (z u : (AdeleRing (𝓞 F) F)ˣ) (hz2 : (z : AdeleRing (𝓞 F) F).2 = 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((z * u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = (u : AdeleRing (𝓞 F) F).2 v := by
  rw [Units.val_mul, adele_snd_mul, hz2, one_mul]

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

private theorem cpowChar_neg_add_half_mul_self (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) :
    ((cpowChar α hα (-(s + 1 / 2)) y : ℂˣ) : ℂ) * ((((α y : ℝˣ) : ℝ) : ℂ))
      = ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ) := by
  have h0 : (((α y : ℝˣ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα y).ne'
  rw [cpowChar_apply_val, cpowChar_apply_val]
  calc (((α y : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α y : ℝˣ) : ℝ) : ℂ)
      = (((α y : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2)) * (((α y : ℝˣ) : ℝ) : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
    _ = (((α y : ℝˣ) : ℝ) : ℂ) ^ (-(s + 1 / 2) + 1) := (Complex.cpow_add _ _ h0).symm
    _ = (((α y : ℝˣ) : ℝ) : ℂ) ^ (1 / 2 - s) := by
        congr 1
        ring

end B4

end T1Helpers

namespace T1Helpers

section B5

open MeasureTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem isOpen_setOf_valued_le (z : v.adicCompletion F) (hz : Valued.v z ≠ 0) :
    IsOpen {x : v.adicCompletion F | Valued.v x ≤ Valued.v z} := by
  have hr : Valued.v.restrict z ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  have h := Valued.isOpen_closedBall (R := v.adicCompletion F) hr
  convert h using 1
  ext y
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_le_iff]

private theorem isOpen_setOf_valued_lt (z : v.adicCompletion F) :
    IsOpen {x : v.adicCompletion F | Valued.v x < Valued.v z} := by
  have h := Valued.isOpen_ball (R := v.adicCompletion F) (Valued.v.restrict z)
  convert h using 1
  ext y
  simp only [Set.mem_setOf_eq]
  rw [Valuation.restrict_lt_iff]

private theorem measurableSet_setOf_valued_eq_exp [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (k : ℤ) : MeasurableSet {x : v.adicCompletion F | Valued.v x = WithZero.exp k} := by
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective F v (WithZero.exp k)
  have hz0 : Valued.v z ≠ 0 := by
    rw [hz]
    exact WithZero.coe_ne_zero
  have hset : {x : v.adicCompletion F | Valued.v x = WithZero.exp k}
      = {x : v.adicCompletion F | Valued.v x ≤ Valued.v z} ∩ {x : v.adicCompletion F | Valued.v x < Valued.v z}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt, ← hz]
    exact le_antisymm_iff
  rw [hset]
  exact (isOpen_setOf_valued_le F v z hz0).measurableSet.inter (isOpen_setOf_valued_lt F v z).measurableSet.compl

private theorem measurableSet_adicCompletionIntegers [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] :
    MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  (Valued.isOpen_valuationSubring _).measurableSet

private theorem addChar_neg_mul_eq_of_valued_le (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (w w₀ x : v.adicCompletion F) (h : Valued.v ((w - w₀) * x) ≤ WithZero.exp n) :
    ψ (-(w * x)) = ψ (-(w₀ * x)) := by
  have hsplit : -(w * x) = -(w₀ * x) + -((w - w₀) * x) := by ring
  rw [hsplit, AddChar.map_add_eq_mul, hψn (-((w - w₀) * x)) (by rwa [Valuation.map_neg]), mul_one]

private theorem setIntegral_integers_twist_eq_of_valued_sub_le
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (A : v.adicCompletion F → ℂ) (w w₀ : v.adicCompletion F) (hw : Valued.v (w - w₀) ≤ WithZero.exp n) :
    ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x * ψ (-(w * x)) ∂μ
      = ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x * ψ (-(w₀ * x)) ∂μ := by
  refine setIntegral_congr_fun (measurableSet_adicCompletionIntegers F v) fun x hx => ?_
  have hx1 : Valued.v x ≤ 1 := hx
  have h : Valued.v ((w - w₀) * x) ≤ WithZero.exp n := by
    rw [Valuation.map_mul]
    calc Valued.v (w - w₀) * Valued.v x ≤ WithZero.exp n * 1 := mul_le_mul' hw hx1
      _ = WithZero.exp n := mul_one _
  simp only [addChar_neg_mul_eq_of_valued_le F v ψ n hψn w w₀ x h]

private theorem setIntegral_shell_twist_eq_of_valued_sub_le
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (G : v.adicCompletion F → ℂ) (k : ℕ) (w w₀ : v.adicCompletion F)
    (hw : Valued.v (w - w₀) ≤ WithZero.exp (n - k)) :
    ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}, G x * ψ (-(w * x)) ∂μ
      = ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}, G x * ψ (-(w₀ * x)) ∂μ := by
  refine setIntegral_congr_fun (measurableSet_setOf_valued_eq_exp F v (k : ℤ)) fun x hx => ?_
  have hxk : Valued.v x = WithZero.exp (k : ℤ) := hx
  have h : Valued.v ((w - w₀) * x) ≤ WithZero.exp n := by
    rw [Valuation.map_mul, hxk]
    calc Valued.v (w - w₀) * WithZero.exp (k : ℤ) ≤ WithZero.exp (n - k) * WithZero.exp (k : ℤ) :=
          mul_le_mul' hw le_rfl
      _ = WithZero.exp n := by rw [← WithZero.exp_add, sub_add_cancel]
  simp only [addChar_neg_mul_eq_of_valued_le F v ψ n hψn w w₀ x h]

private theorem valued_eq_of_valued_sub_lt (w w₀ : v.adicCompletion F) (h : Valued.v (w - w₀) < Valued.v w₀) :
    Valued.v w = Valued.v w₀ := by
  have := Valuation.map_add_eq_of_lt_left (v := (Valued.v : Valuation (v.adicCompletion F) _)) h
  rwa [add_sub_cancel] at this

end B5

end T1Helpers

section IdeleFacts

open NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

private theorem T1U_idele_snd_ne_zero (U : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (U : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  have h : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v * (U : AdeleRing (𝓞 F) F).2 v = 1 :=
    congrArg (fun z : AdeleRing (𝓞 F) F => z.2 v) (Units.inv_mul U)
  exact right_ne_zero_of_mul_eq_one h

private theorem T1U_idele_fst_ne_zero (U : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (U : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  have h : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w * (U : AdeleRing (𝓞 F) F).1 w = 1 :=
    congrArg (fun z : AdeleRing (𝓞 F) F => z.1 w) (Units.inv_mul U)
  exact right_ne_zero_of_mul_eq_one h

private theorem T1U_idele_valued_ne_one_finite (U : (AdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v ((U : AdeleRing (𝓞 F) F).2 v) ≠ 1}.Finite := by
  have h1 : {v : HeightOneSpectrum (𝓞 F) | (U : AdeleRing (𝓞 F) F).2 v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp ((U : AdeleRing (𝓞 F) F).2).2
  have h2 : {v : HeightOneSpectrum (𝓞 F) |
      ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp (((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
  refine (h1.union h2).subset fun v hv => ?_
  by_contra hmem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hmem
  apply hv
  have hle1 : Valued.v ((U : AdeleRing (𝓞 F) F).2 v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem.1
  have hle2 : Valued.v (((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem.2
  have hprod : Valued.v ((U : AdeleRing (𝓞 F) F).2 v)
      * Valued.v (((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) = 1 := by
    rw [← map_mul, T1Helpers.snd_apply_mul_inv_snd_apply, map_one]
  refine le_antisymm hle1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((U : AdeleRing (𝓞 F) F).2 v)
        * Valued.v (((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) := hprod.symm
    _ ≤ Valued.v ((U : AdeleRing (𝓞 F) F).2 v) * 1 := mul_le_mul_right hle2 _
    _ = Valued.v ((U : AdeleRing (𝓞 F) F).2 v) := mul_one _

private theorem T1U_continuous_mixedSpace_fst (i : {w : InfinitePlace F // w.IsReal}) :
    Continuous fun x : InfiniteAdeleRing F => (InfiniteAdeleRing.ringEquiv_mixedSpace F x).1 i := by
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal i.2).continuous.comp (continuous_apply i.1)

private theorem T1U_continuous_mixedSpace_snd (w : {w : InfinitePlace F // w.IsComplex}) :
    Continuous fun x : InfiniteAdeleRing F => (InfiniteAdeleRing.ringEquiv_mixedSpace F x).2 w := by
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp (continuous_apply w.1)

end IdeleFacts

section EulerDiff

open IsDedekindDomain NumberField Filter Topology

private theorem T1F1_hasProd_inv₀ {ι : Type*} {f : ι → ℂ} {a : ℂ} (hf : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  have h : (fun s : Finset ι => ∏ b ∈ s, (f b)⁻¹) = fun s => (∏ b ∈ s, f b)⁻¹ := by
    funext s
    exact Finset.prod_inv_distrib (f := f) (s := s)
  unfold HasProd at hf ⊢
  rw [h]
  exact hf.inv₀ ha

private theorem T1F1_re_two_mul_add_one (s : ℂ) : (2 * s + 1).re = 2 * s.re + 1 := by
  simp

private theorem T1F1_multipliable_and_tprod_eq_and_ne_zero (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) :
    Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) ∧
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
      = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹)⁻¹ ∧
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) ≠ 0 := by
  obtain ⟨hE1, -, hE3⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S z hz
  have hs' : 1 < (2 * s + 1).re := by rw [T1F1_re_two_mul_add_one]; linarith
  obtain ⟨a, ha⟩ := hE1 (2 * s + 1) hs'
  have ha0 : a ≠ 0 := by rw [← ha.tprod_eq]; exact hE3 (2 * s + 1) hs'
  have hinv := T1F1_hasProd_inv₀ ha ha0
  simp only [inv_inv] at hinv
  exact ⟨hinv.multipliable, by rw [hinv.tprod_eq, ha.tprod_eq], by rw [hinv.tprod_eq]; exact inv_ne_zero ha0⟩

private theorem T1F1_differentiableOn_tprod (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) :
    DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) {s : ℂ | 0 < s.re} := by
  obtain ⟨-, hE2, hE3⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S z hz
  have haff : DifferentiableOn ℂ (fun s : ℂ => 2 * s + 1) {s : ℂ | 0 < s.re} :=
    ((differentiable_id.const_mul (2 : ℂ)).add_const 1).differentiableOn
  have hmaps : Set.MapsTo (fun s : ℂ => 2 * s + 1) {s : ℂ | 0 < s.re} {s : ℂ | 1 < s.re} := by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs ⊢
    rw [T1F1_re_two_mul_add_one]; linarith
  have hg : DifferentiableOn ℂ (fun s : ℂ => (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹)⁻¹) {s : ℂ | 0 < s.re} := by
    refine (hE2.comp haff hmaps).inv fun s hs => ?_
    exact hE3 (2 * s + 1) (hmaps hs)
  refine hg.congr fun s hs => ?_
  exact (T1F1_multipliable_and_tprod_eq_and_ne_zero F S z hz s hs).2.1

private theorem T1F1_continuousOn_tprod (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) :
    ContinuousOn (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) {s : ℂ | 0 < s.re} :=
  (T1F1_differentiableOn_tprod F S z hz).continuousOn

end EulerDiff

section FinCont

open IsDedekindDomain NumberField Filter Topology

private theorem T1F2_finite_setOf_valued_ne_one (F : Type) [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v (((U : AdeleRing (𝓞 F) F).2) v) ≠ 1}.Finite := by
  have hmul : (U : AdeleRing (𝓞 F) F).2 * ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv U)
  have hmul' : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * (U : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul U)
  have hu : IsUnit ((U : AdeleRing (𝓞 F) F).2) := ⟨⟨_, _, hmul, hmul'⟩, rfl⟩
  exact Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp hu).2

private theorem T1F2_valued_eq_one_of_mul_eq_one (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (a b : v.adicCompletion F) (hab : a * b = 1) (ha : Valued.v a ≤ 1) (hb : Valued.v b ≤ 1) :
    Valued.v a = 1 := by
  by_contra h
  have hlt : Valued.v a < 1 := lt_of_le_of_ne ha h
  have h1 : Valued.v a * Valued.v b = 1 := by rw [← map_mul, hab, map_one]
  have h2 : Valued.v a * Valued.v b ≤ Valued.v a * 1 := mul_le_mul_right hb _
  rw [h1, mul_one] at h2
  exact absurd (lt_of_le_of_lt h2 hlt) (lt_irrefl _)

private theorem T1F2_isOpen_setOf_forall_mem_integers (F : Type) [Field F] [NumberField F] :
    IsOpen {u : (AdeleRing (𝓞 F) F)ˣ |
      (∀ v : HeightOneSpectrum (𝓞 F), ((u : AdeleRing (𝓞 F) F).2) v ∈ v.adicCompletionIntegers F) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v ∈ v.adicCompletionIntegers F} := by
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)
  have h1 : Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => (u : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  exact (hO.preimage h1).inter (hO.preimage h2)

private theorem T1F2_setOf_valued_eq_one_and_valued_sub_le_mem_nhds (F : Type) [Field F] [NumberField F]
    (y₀ : (AdeleRing (𝓞 F) F)ˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) (δ : HeightOneSpectrum (𝓞 F) → ℤ) :
    {y : (AdeleRing (𝓞 F) F)ˣ |
      (∀ v : HeightOneSpectrum (𝓞 F),
        Valued.v ((((y * y₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v) = 1) ∧
      ∀ v ∈ T, Valued.v (((y : AdeleRing (𝓞 F) F).2) v - ((y₀ : AdeleRing (𝓞 F) F).2) v) ≤ WithZero.exp (δ v)}
      ∈ 𝓝 y₀ := by

  have hW := T1F2_isOpen_setOf_forall_mem_integers F
  have hm : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => y * y₀⁻¹ := continuous_id.mul continuous_const
  have hA : {y : (AdeleRing (𝓞 F) F)ˣ | ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((((y * y₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v) = 1} ∈ 𝓝 y₀ := by
    refine Filter.mem_of_superset ((hW.preimage hm).mem_nhds ?_) ?_
    · simp only [Set.mem_preimage, mul_inv_cancel, Set.mem_setOf_eq, inv_one, Units.val_one]
      exact ⟨fun v => (v.adicCompletionIntegers F).one_mem, fun v => (v.adicCompletionIntegers F).one_mem⟩
    · rintro y ⟨h1, h2⟩ v
      refine T1F2_valued_eq_one_of_mul_eq_one F v _ ((((y * y₀⁻¹)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
        ?_ (h1 v) (h2 v)
      have := congrArg Prod.snd (Units.mul_inv (y * y₀⁻¹))
      exact congrFun (congrArg DFunLike.coe this) v

  have hev : ∀ v : HeightOneSpectrum (𝓞 F), Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((y : AdeleRing (𝓞 F) F).2) v :=
    fun v => (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)
  have hB : ∀ v : HeightOneSpectrum (𝓞 F), {y : (AdeleRing (𝓞 F) F)ˣ |
      Valued.v (((y : AdeleRing (𝓞 F) F).2) v - ((y₀ : AdeleRing (𝓞 F) F).2) v) ≤ WithZero.exp (δ v)} ∈ 𝓝 y₀ := by
    intro v
    obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (δ v))
    have hc0 : Valued.v c ≠ 0 := by rw [hc]; exact WithZero.exp_ne_zero
    have hcne : c ≠ 0 := by rintro rfl; exact hc0 (map_zero _)
    have hc0' : Valued.v.restrict c ≠ 0 := by simp [hcne]
    have hs : {a : v.adicCompletion F | Valued.v (a - ((y₀ : AdeleRing (𝓞 F) F).2) v) ≤ WithZero.exp (δ v)}
        ∈ 𝓝 (((y₀ : AdeleRing (𝓞 F) F).2) v) := by
      rw [Valued.mem_nhds]
      refine ⟨Units.mk0 _ hc0', fun a ha => ?_⟩
      rw [Units.val_mk0] at ha
      have ha' := (Valuation.restrict_lt_iff _).mp ha
      rw [hc] at ha'
      exact le_of_lt ha'
    exact (hev v).continuousAt.preimage_mem_nhds hs
  have hB' : (⋂ v ∈ T, {y : (AdeleRing (𝓞 F) F)ˣ |
      Valued.v (((y : AdeleRing (𝓞 F) F).2) v - ((y₀ : AdeleRing (𝓞 F) F).2) v) ≤ WithZero.exp (δ v)}) ∈ 𝓝 y₀ :=
    (Filter.biInter_finset_mem T).mpr fun v _ => hB v
  refine Filter.mem_of_superset (Filter.inter_mem hA hB') ?_
  rintro y ⟨h1, h2⟩
  refine ⟨h1, fun v hv => ?_⟩
  exact (Set.mem_iInter₂.mp h2) v hv

private theorem T1F2_setOf_valued_eq_one_off_and_valued_sub_le_mem_nhds (F : Type) [Field F] [NumberField F]
    (y₀ : (AdeleRing (𝓞 F) F)ˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) (δ : HeightOneSpectrum (𝓞 F) → ℤ) :
    {y : (AdeleRing (𝓞 F) F)ˣ |
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ T →
        Valued.v ((((y * y₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) v) = 1) ∧
      ∀ v ∈ T, Valued.v (((y : AdeleRing (𝓞 F) F).2) v - ((y₀ : AdeleRing (𝓞 F) F).2) v) ≤ WithZero.exp (δ v)}
      ∈ 𝓝 y₀ :=
  Filter.mem_of_superset (T1F2_setOf_valued_eq_one_and_valued_sub_le_mem_nhds F y₀ T δ)
    fun _ hy => ⟨fun v _ => hy.1 v, hy.2⟩

private theorem T1F4_snd_mul_apply (F : Type) [Field F] [NumberField F] (x y : AdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) : (x * y).2 v = x.2 v * y.2 v := rfl

private theorem T1F4_snd_apply_ne_zero (F : Type) [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) : (U : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  have h : (U : AdeleRing (𝓞 F) F).2 v * ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
    have := congrArg Prod.snd (Units.mul_inv U)
    exact congrFun (congrArg DFunLike.coe this) v
  exact left_ne_zero_of_mul_eq_one h

private theorem T1F4_continuous_finprod (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (thr : HeightOneSpectrum (𝓞 F) → ℤ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hΦd : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w))
    (hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (hΦlc : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w₀ : v.adicCompletion F), w₀ ≠ 0 → ∃ δ : ℤ,
      ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s)
    (a x₀ : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) :
    Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (p.2 : AdeleRing (𝓞 F) F)
        * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) p.1 := by
  classical
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨s₀, y₀⟩ := p₀

  set U₀ : (AdeleRing (𝓞 F) F)ˣ := x₀ * y₀ * a⁻¹ with hU₀
  set w₀ : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F := fun v => (U₀ : AdeleRing (𝓞 F) F).2 v with hw₀
  have hw₀v : ∀ v, w₀ v = (x₀ : AdeleRing (𝓞 F) F).2 v * (y₀ : AdeleRing (𝓞 F) F).2 v
      * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v := by
    intro v
    simp only [hw₀, hU₀, Units.val_mul]
    rfl
  have hw₀ne : ∀ v, w₀ v ≠ 0 := fun v => T1F4_snd_apply_ne_zero F U₀ v

  have hfin := T1F2_finite_setOf_valued_ne_one F U₀
  set T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hfin.toFinset with hT
  have hT1 : ∀ v ∉ T, v ∉ S ∧ Valued.v (w₀ v) = 1 := by
    intro v hv
    rw [hT, Finset.mem_union, not_or] at hv
    refine ⟨hv.1, ?_⟩
    by_contra h
    exact hv.2 (hfin.mem_toFinset.2 h)

  choose δ hδ using fun v => hΦlc j v (w₀ v) (hw₀ne v)
  set c : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F :=
    fun v => (x₀ : AdeleRing (𝓞 F) F).2 v * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v with hc
  have hcne : ∀ v, Valued.v (c v) ≠ 0 := fun v =>
    (Valuation.ne_zero_iff _).2 (mul_ne_zero (T1F4_snd_apply_ne_zero F x₀ v) (T1F4_snd_apply_ne_zero F a⁻¹ v))
  set δ' : HeightOneSpectrum (𝓞 F) → ℤ := fun v => δ v - WithZero.log (Valued.v (c v)) with hδ'

  have hN := T1F2_setOf_valued_eq_one_and_valued_sub_le_mem_nhds F y₀ T δ'
  have hgc : Continuous fun s : ℂ => ∏ v ∈ T, Φ j v (w₀ v) s :=
    continuous_finsetProd T fun v _ => (hΦd j v (w₀ v)).continuous
  refine ((hgc.comp continuous_fst).continuousAt (x := (s₀, y₀))).congr_of_eventuallyEq ?_
  refine Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem hN) ?_
  rintro ⟨s, y⟩ ⟨-, hy1, hy2⟩
  show (∏ᶠ v : HeightOneSpectrum (𝓞 F), Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)
        * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s) = ∏ v ∈ T, Φ j v (w₀ v) s

  have hy : (y : AdeleRing (𝓞 F) F) = ((y * y₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (y₀ : AdeleRing (𝓞 F) F) := by
    rw [← Units.val_mul, inv_mul_cancel_right]
  have hW : ∀ v, (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)
      * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v)
      = ((y * y₀⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v * w₀ v := by
    intro v
    rw [T1F4_snd_mul_apply, T1F4_snd_mul_apply, hw₀v, hy, T1F4_snd_mul_apply]
    ring
  have hWsub : ∀ v, (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)
      * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) - w₀ v
      = c v * ((y : AdeleRing (𝓞 F) F).2 v - (y₀ : AdeleRing (𝓞 F) F).2 v) := by
    intro v
    rw [T1F4_snd_mul_apply, T1F4_snd_mul_apply, hw₀v]
    simp only [hc]
    ring
  have hpt : ∀ v, Φ j v (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)
      * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s = Φ j v (w₀ v) s := by
    intro v
    by_cases hv : v ∈ T
    · refine hδ v _ s ?_
      rw [hWsub, map_mul]
      calc Valued.v (c v) * Valued.v ((y : AdeleRing (𝓞 F) F).2 v - (y₀ : AdeleRing (𝓞 F) F).2 v)
          ≤ Valued.v (c v) * WithZero.exp (δ' v) := mul_le_mul_right (hy2 v hv) _
        _ = WithZero.exp (δ v) := by
            conv_lhs => rw [← WithZero.exp_log (hcne v)]
            rw [← WithZero.exp_add, hδ']
            simp
    · obtain ⟨hvS, hv1⟩ := hT1 v hv
      have hval : Valued.v (((x₀ : AdeleRing (𝓞 F) F) * (y : AdeleRing (𝓞 F) F)
          * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) = 1 := by
        rw [hW, map_mul, hy1 v, one_mul, hv1]
      rw [hΦ1 j v hvS _ s hval, hΦ1 j v hvS _ s hv1]
  rw [finprod_congr hpt]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvT
  obtain ⟨hvS, hv1⟩ := hT1 v hvT
  exact hv (hΦ1 j v hvS _ s hv1)

end FinCont

section FinBound

open IsDedekindDomain NumberField Filter

private theorem T1F3_finite_setOf_valued_ne_one (F : Type) [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v (((U : AdeleRing (𝓞 F) F).2) v) ≠ 1}.Finite := by
  have hmul : (U : AdeleRing (𝓞 F) F).2 * ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv U)
  have hmul' : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * (U : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul U)
  have hu : IsUnit ((U : AdeleRing (𝓞 F) F).2) := ⟨⟨_, _, hmul, hmul'⟩, rfl⟩
  exact Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp hu).2

private theorem T1F3_exists_fractionalIdeal_ne_zero_mem_of_forall_valued_le (F : Type) [Field F] [NumberField F]
    (N : HeightOneSpectrum (𝓞 F) → ℤ) (hN : (Function.support N).Finite) :
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F, I ≠ 0 ∧ ∀ ξ : F,
      (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ξ ≤ WithZero.exp (N v)) → ξ ∈ I := by
  have hJ : (∏ v ∈ hN.toFinset, v.asIdeal ^ (N v).toNat) ≠ ⊥ :=
    Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  obtain ⟨d, hdJ, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hd0
  refine ⟨FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (algebraMap (𝓞 F) F d)⁻¹,
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hdF), fun ξ hξ => ?_⟩
  have hdvd : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ (N v).toNat ∣ Ideal.span {d} := by
    intro v
    by_cases hv : v ∈ hN.toFinset
    · exact (Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ (N v).toNat) hv).trans
        (Ideal.dvd_span_singleton.mpr hdJ)
    · have h0 : N v = 0 := by
        by_contra h
        exact hv (hN.mem_toFinset.mpr (Function.mem_support.mpr h))
      rw [h0, Int.toNat_zero, pow_zero]
      exact one_dvd _
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (algebraMap (𝓞 F) F d * ξ) ≤ 1 := by
    intro v
    have h1 : v.valuation F (algebraMap (𝓞 F) F d) = v.intValuation d := v.valuation_of_algebraMap d
    have h2 : v.intValuation d ≤ WithZero.exp (-((N v).toNat : ℤ)) :=
      (v.intValuation_le_pow_iff_dvd d _).mpr (hdvd v)
    calc v.valuation F (algebraMap (𝓞 F) F d * ξ)
        = v.intValuation d * v.valuation F ξ := by rw [Valuation.map_mul, h1]
      _ ≤ WithZero.exp (-((N v).toNat : ℤ)) * WithZero.exp (N v) := mul_le_mul' h2 (hξ v)
      _ = WithZero.exp (-((N v).toNat : ℤ) + N v) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      _ = 1 := WithZero.exp_zero
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp
    (IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hint)
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨z, ?_⟩
  rw [Algebra.smul_def, hz, mul_comm (algebraMap (𝓞 F) F d) ξ, mul_inv_cancel_right₀ hdF]

private theorem T1F3_exists_pos_finprod_absNorm_pow_toNat_neg_le_mul_abs_norm (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : F, ξ ∈ I → ξ ≠ 0 → ∀ e : HeightOneSpectrum (𝓞 F) → ℤ,
      (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ξ = WithZero.exp (e v)) →
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat
        ≤ c₀ * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
  obtain ⟨a, aI, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have haF : algebraMap (𝓞 F) F a ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hNa : (0 : ℚ) < |Algebra.norm ℚ (algebraMap (𝓞 F) F a)| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr haF)
  refine ⟨((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ), Rat.cast_pos.mpr hNa,
    fun ξ hξ hξ0 e he => ?_⟩
  rw [hI, FractionalIdeal.mem_singleton_mul] at hξ
  obtain ⟨y, hy, hξy⟩ := hξ
  obtain ⟨b, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
  have hab : algebraMap (𝓞 F) F a * ξ = algebraMap (𝓞 F) F b := by
    rw [hξy, mul_inv_cancel_left₀ haF]
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero haF hξ0 hab
  have hdvd : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ (-(e v)).toNat ∣ Ideal.span {b} := by
    intro v
    by_cases hv : 0 ≤ e v
    · rw [Int.toNat_eq_zero.mpr (by omega), pow_zero]
      exact one_dvd _
    · have h1 : v.valuation F (algebraMap (𝓞 F) F b) = v.intValuation b := v.valuation_of_algebraMap b
      have h2 : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a := v.valuation_of_algebraMap a
      have h3 : v.intValuation b ≤ WithZero.exp (e v) := by
        rw [← h1, ← hab, Valuation.map_mul, h2, he v]
        exact mul_le_of_le_one_left' (v.intValuation_le_one a)
      refine (v.intValuation_le_pow_iff_dvd b _).mp ?_
      rwa [Int.toNat_of_nonneg (by omega), neg_neg]
  have hNb : Algebra.norm ℚ (algebraMap (𝓞 F) F b) = ((Algebra.norm ℤ b : ℤ) : ℚ) :=
    (Algebra.coe_norm_int b).symm
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat
        ≤ ((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
    intro T
    have hT : (∏ v ∈ T, v.asIdeal ^ (-(e v)).toNat) ∣ Ideal.span {b} :=
      Finset.prod_dvd_of_coprime
        (fun v _ w _ hvw => IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne v w hvw _ _)
        (fun v _ => hdvd v)
    have hT' := map_dvd (Ideal.absNorm (S := 𝓞 F)) hT
    simp only [map_prod, map_pow, Ideal.absNorm_span_singleton] at hT'
    have hle : (∏ v ∈ T, Ideal.absNorm v.asIdeal ^ (-(e v)).toNat) ≤ (Algebra.norm ℤ b).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hb0)) hT'
    have hcast : (∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat)
        = ((∏ v ∈ T, Ideal.absNorm v.asIdeal ^ (-(e v)).toNat : ℕ) : ℝ) := by
      simp only [Nat.cast_prod, Nat.cast_pow]
    have hR : (((Algebra.norm ℤ b).natAbs : ℕ) : ℝ)
        = ((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
      rw [Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, ← hNb, ← hab, map_mul, abs_mul, Rat.cast_mul]
    rw [hcast, ← hR]
    exact Nat.cast_le.mpr hle
  by_cases hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat
  · rw [finprod_eq_prod _ hfin]
    exact key _
  · rw [finprod_of_infinite_mulSupport hfin]
    have h := key ∅
    rwa [Finset.prod_empty] at h

private theorem T1F3_prod_le_finprod {ι : Type} (g : ι → ℝ) (hg1 : ∀ i, 1 ≤ g i)
    (hfin : (Function.mulSupport g).Finite) (T : Finset ι) :
    ∏ i ∈ T, g i ≤ ∏ᶠ i, g i := by
  classical
  rw [finprod_eq_prod_of_mulSupport_subset g (s := T ∪ hfin.toFinset)
    (fun i hi => by simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hi)]
  rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
  have h1 : (1 : ℝ) ≤ ∏ i ∈ hfin.toFinset \ T, g i := by
    rw [← Finset.prod_const_one (s := hfin.toFinset \ T)]
    exact Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => hg1 i
  have h0 : 0 ≤ ∏ i ∈ T, g i := Finset.prod_nonneg fun i _ => zero_le_one.trans (hg1 i)
  exact le_mul_of_one_le_right h0 h1

private theorem T1F3_one_le_absNorm (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr h

private theorem T1F3_valued_freq (F : Type) [Field F] [NumberField F] (ξ : F) (uf : (AdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (uf : AdeleRing (𝓞 F) F)).2 v)
      = v.valuation F ξ * Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ξ, ← map_mul]
  rfl

open scoped Classical in

private theorem T1F3_finBound (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ)
    (thr : HeightOneSpectrum (𝓞 F) → ℤ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hthr : ∀ v ∉ S, thr v = 0)
    (hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (hΦ0 : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F) (s : ℂ),
      w ≠ 0 → WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0)
    (hΦb : ∀ R : ℝ, ∃ (M : ℝ) (κ : ℕ), 0 ≤ M ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F))
      (w : v.adicCompletion F) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
      ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ)
    (L : HeightOneSpectrum (𝓞 F) → ℤ) (hLfin : (Function.support L).Finite) (hL0 : ∀ v, 0 ≤ L v) (R : ℝ) :
    ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (c : ℝ), 0 ≤ c ∧
      ∀ (j : Fin n) (s : ℂ), ‖s‖ ≤ R → ∀ (uf : (AdeleRing (𝓞 F) F)ˣ),
        (∀ v : HeightOneSpectrum (𝓞 F), WithZero.exp (-(L v)) ≤ Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) ∧
          Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) ≤ WithZero.exp (L v)) →
        ∀ (ξ : {ξ : F // ξ ≠ 0}),
          ((ξ : F) ∉ I → ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (uf : AdeleRing (𝓞 F) F)).2 v) s = 0) ∧
          ‖∏ᶠ v : HeightOneSpectrum (𝓞 F),
            Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (uf : AdeleRing (𝓞 F) F)).2 v) s‖
            ≤ c * (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k := by

  set Nf : HeightOneSpectrum (𝓞 F) → ℤ := fun v => thr v + L v with hNf
  have hNfin : (Function.support Nf).Finite := by
    refine (S.finite_toSet.union hLfin).subset fun v hv => ?_
    by_contra hv'
    simp only [Set.mem_union, Finset.mem_coe, Function.mem_support, not_or, not_not] at hv'
    exact hv (by simp only [hNf, hthr v hv'.1, hv'.2, add_zero])
  obtain ⟨I, -, hI⟩ := T1F3_exists_fractionalIdeal_ne_zero_mem_of_forall_valued_le F Nf hNfin
  obtain ⟨c₀, hc₀, hc₀I⟩ := T1F3_exists_pos_finprod_absNorm_pow_toNat_neg_le_mul_abs_norm F I
  obtain ⟨M, κ, hM, hb⟩ := hΦb R

  set CL : ℝ := ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat with hCL
  have hN1 := T1F3_one_le_absNorm F
  have hCL0 : 0 ≤ CL := finprod_nonneg fun v => by positivity
  refine ⟨κ, I, M ^ S.card * (c₀ * CL) ^ κ, by positivity, fun j s hs uf huf ξ => ?_⟩

  set x : FiniteAdeleRing (𝓞 F) F := (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (uf : AdeleRing (𝓞 F) F)).2
    with hx
  have hvalξ0 : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ : F) ≠ 0 :=
    fun v => (Valuation.ne_zero_iff _).mpr ξ.2
  have hvalu0 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) ≠ 0 := by
    intro v h0
    have := (huf v).1
    rw [h0] at this
    exact WithZero.exp_ne_zero (le_zero_iff.mp this)
  set eξ : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (v.valuation F (ξ : F)) with heξ
  set eu : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (Valued.v ((uf : AdeleRing (𝓞 F) F).2 v)) with heu
  have hvalξ : ∀ v, v.valuation F (ξ : F) = WithZero.exp (eξ v) := fun v => (WithZero.exp_log (hvalξ0 v)).symm
  have hvalu : ∀ v, Valued.v ((uf : AdeleRing (𝓞 F) F).2 v) = WithZero.exp (eu v) :=
    fun v => (WithZero.exp_log (hvalu0 v)).symm
  have hvalx : ∀ v, Valued.v (x v) = WithZero.exp (eξ v + eu v) := by
    intro v
    rw [hx, T1F3_valued_freq, hvalξ, hvalu, WithZero.exp_add]
  have hx0 : ∀ v, x v ≠ 0 := by
    intro v h0
    have := hvalx v
    rw [h0, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have heuL : ∀ v, -(L v) ≤ eu v := fun v => WithZero.exp_le_exp.mp (by rw [← hvalu]; exact (huf v).1)

  have hfinx : {v : HeightOneSpectrum (𝓞 F) | Valued.v (x v) ≠ 1}.Finite := by
    have h := T1F3_finite_setOf_valued_ne_one F
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * uf)
    have hx' : (((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * uf :
        (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 = x := by
      simp [hx, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0]
    rwa [hx'] at h
  set T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hfinx.toFinset with hT
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => Φ j v (x v) s) ⊆ (T : Set _) := by
    intro v hv
    rw [hT, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    by_contra h
    simp only [not_or, not_not] at h
    exact hv (hΦ1 j v h.1 (x v) s h.2)
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), Φ j v (x v) s = ∏ v ∈ T, Φ j v (x v) s :=
    finprod_eq_prod_of_mulSupport_subset _ hsupp

  have hvan : (ξ : F) ∉ I → ∏ᶠ v : HeightOneSpectrum (𝓞 F), Φ j v (x v) s = 0 := by
    intro hξI
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : HeightOneSpectrum (𝓞 F), ¬ v₀.valuation F (ξ : F) ≤ WithZero.exp (Nf v₀) :=
      not_forall.mp fun hall => hξI (hI (ξ : F) hall)
    rw [not_le, hvalξ, WithZero.exp_lt_exp] at hv₀
    have hlt : WithZero.exp (thr v₀) < Valued.v (x v₀) := by
      rw [hvalx, WithZero.exp_lt_exp]
      have := heuL v₀
      simp only [hNf] at hv₀
      omega
    have hzero : Φ j v₀ (x v₀) s = 0 := hΦ0 j v₀ (x v₀) s (hx0 v₀) hlt
    have hv₀T : v₀ ∈ T := by
      by_contra h
      have h1 : Φ j v₀ (x v₀) s = 1 := by
        by_contra h1
        exact h (hsupp h1)
      rw [hzero] at h1
      exact zero_ne_one h1
    rw [hprod]
    exact Finset.prod_eq_zero hv₀T hzero
  refine ⟨hvan, ?_⟩

  by_cases hξI : (ξ : F) ∈ I
  swap
  · rw [hvan hξI, norm_zero]
    positivity

  have hplace : ∀ v ∈ T, ‖Φ j v (x v) s‖ ≤ (if v ∈ S then M else 1)
      * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat) ^ κ := by
    intro v _
    refine (hb j v (x v) (eξ v + eu v) s hs (hvalx v)).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ κ) ?_
    · rw [← pow_add]
      refine pow_le_pow_right₀ (hN1 v) ?_
      have := heuL v
      omega
    · split_ifs
      · exact hM
      · exact zero_le_one

  have hST : S ⊆ T := Finset.subset_union_left
  have hMprod : ∏ v ∈ T, (if v ∈ S then M else (1 : ℝ)) = M ^ S.card := by
    rw [← Finset.prod_subset hST (fun v _ hvS => if_neg hvS)]
    rw [Finset.prod_congr rfl (fun v hv => if_pos hv), Finset.prod_const]

  have hfin1 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat).Finite := by
    have h := T1F3_finite_setOf_valued_ne_one F
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2))
    refine h.subset fun v hv => ?_
    rw [Set.mem_setOf_eq]
    intro h1
    apply hv
    have h1' : v.valuation F (ξ : F) = 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ : F)]
      simpa [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0] using h1
    show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat = 1
    rw [heξ]
    simp only [h1', WithZero.log_one, neg_zero, Int.toNat_zero, pow_zero]
  have hfin2 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat).Finite := by
    refine hLfin.subset fun v hv => ?_
    rw [Function.mem_support]
    intro h0
    apply hv
    show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat = 1
    rw [h0, Int.toNat_zero, pow_zero]
  have hle1 : ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat
      ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat :=
    T1F3_prod_le_finprod _ (fun v => one_le_pow₀ (hN1 v)) hfin1 T
  have hle2 : ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat ≤ CL :=
    T1F3_prod_le_finprod _ (fun v => one_le_pow₀ (hN1 v)) hfin2 T
  have hc₀' := hc₀I (ξ : F) hξI ξ.2 eξ hvalξ
  have hNξ0 : 0 ≤ ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg _

  rw [hprod]
  calc ‖∏ v ∈ T, Φ j v (x v) s‖ = ∏ v ∈ T, ‖Φ j v (x v) s‖ := norm_prod _ _
    _ ≤ ∏ v ∈ T, ((if v ∈ S then M else 1)
        * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat) ^ κ) :=
        Finset.prod_le_prod (fun v _ => norm_nonneg _) hplace
    _ = M ^ S.card * ((∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(eξ v)).toNat)
        * ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (L v).toNat) ^ κ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_mul_distrib, hMprod]
    _ ≤ M ^ S.card * ((c₀ * ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) * CL) ^ κ := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ κ) (by positivity)
        exact mul_le_mul (hle1.trans hc₀') hle2 (Finset.prod_nonneg fun v _ => by positivity) (by positivity)
    _ ≤ M ^ S.card * ((c₀ * CL) * max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ κ := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ κ) (by positivity)
        calc c₀ * ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) * CL = (c₀ * CL) * ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) := by
              ring
          _ ≤ (c₀ * CL) * max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ) :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    _ = M ^ S.card * (c₀ * CL) ^ κ * (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ κ := by
        rw [mul_pow]; ring

end FinBound

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

private theorem T1F5_dilation_bound_of_polyDecay (j : ℂ → ℝ → ℂ) (K : Set ℂ) (N : ℕ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hj : ∀ w ∈ K, ∀ t : ℝ, ‖j w t‖ ≤ C₀ * (1 + |t|) ^ (-(N : ℝ)))
    (θ : ℝ) (hθ : θ ≠ 0) (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ (r x m : ℝ), 0 < r → c₁ ≤ |m| →
      ‖j w (-(θ * (r * (x * m))))‖ ≤ C * (1 + r * |x|) ^ (-(N : ℝ)) := by
  have hθc : 0 < |θ| * c₁ := mul_pos (abs_pos.2 hθ) hc₁
  refine ⟨C₀ * (min 1 (|θ| * c₁)) ^ (-(N : ℝ)), mul_pos hC₀ (Real.rpow_pos_of_pos (lt_min one_pos hθc) _), ?_⟩
  intro w hw r x m hr hm
  have h := hj w hw (-(θ * (r * (x * m))))
  have hrx : 0 ≤ r * |x| := mul_nonneg hr.le (abs_nonneg x)
  have ht₀ : |(-(θ * (r * (x * m))))| = |θ| * (r * |x|) * |m| := by
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos hr]
    ring
  have hge : |θ| * c₁ * (r * |x|) ≤ |(-(θ * (r * (x * m))))| := by
    rw [ht₀]
    calc |θ| * c₁ * (r * |x|) = |θ| * (r * |x|) * c₁ := by ring
      _ ≤ |θ| * (r * |x|) * |m| := mul_le_mul_of_nonneg_left hm (mul_nonneg (abs_nonneg θ) hrx)
  have h1 : (1 + |(-(θ * (r * (x * m))))|) ^ (-(N : ℝ)) ≤ (1 + |θ| * c₁ * (r * |x|)) ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
  have h2 := T1F5_one_add_mul_rpow_neg_le (|θ| * c₁) (r * |x|) N hθc hrx (Nat.cast_nonneg N)
  calc _ ≤ C₀ * (1 + |(-(θ * (r * (x * m))))|) ^ (-(N : ℝ)) := h
    _ ≤ C₀ * ((min 1 (|θ| * c₁)) ^ (-(N : ℝ)) * (1 + r * |x|) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hC₀.le
    _ = C₀ * (min 1 (|θ| * c₁)) ^ (-(N : ℝ)) * (1 + r * |x|) ^ (-(N : ℝ)) := by ring

private theorem T1F5_dilation_bound_of_polyDecay_complex (j : ℂ → ℂ → ℂ) (K : Set ℂ) (N : ℕ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hj : ∀ w ∈ K, ∀ ζ : ℂ, ‖j w ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ (-(N : ℝ)))
    (θ : ℂ) (hθ : θ ≠ 0) (c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ (r : ℝ) (x m : ℂ), 0 < r → c₁ ≤ ‖m‖ →
      ‖j w (-(θ * ((r : ℂ) * (x * m))))‖ ≤ C * (1 + r * ‖x‖) ^ (-(N : ℝ)) := by
  have hθc : 0 < ‖θ‖ * c₁ := mul_pos (norm_pos_iff.2 hθ) hc₁
  refine ⟨C₀ * (min 1 (‖θ‖ * c₁)) ^ (-(N : ℝ)), mul_pos hC₀ (Real.rpow_pos_of_pos (lt_min one_pos hθc) _), ?_⟩
  intro w hw r x m hr hm
  have h := hj w hw (-(θ * ((r : ℂ) * (x * m))))
  have hrx : 0 ≤ r * ‖x‖ := mul_nonneg hr.le (norm_nonneg x)
  have hζ₀ : ‖(-(θ * ((r : ℂ) * (x * m))))‖ = ‖θ‖ * (r * ‖x‖) * ‖m‖ := by
    rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    ring
  have hge : ‖θ‖ * c₁ * (r * ‖x‖) ≤ ‖(-(θ * ((r : ℂ) * (x * m))))‖ := by
    rw [hζ₀]
    calc ‖θ‖ * c₁ * (r * ‖x‖) = ‖θ‖ * (r * ‖x‖) * c₁ := by ring
      _ ≤ ‖θ‖ * (r * ‖x‖) * ‖m‖ := mul_le_mul_of_nonneg_left hm (mul_nonneg (norm_nonneg θ) hrx)
  have h1 : (1 + ‖(-(θ * ((r : ℂ) * (x * m))))‖) ^ (-(N : ℝ)) ≤ (1 + ‖θ‖ * c₁ * (r * ‖x‖)) ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
  have h2 := T1F5_one_add_mul_rpow_neg_le (‖θ‖ * c₁) (r * ‖x‖) N hθc hrx (Nat.cast_nonneg N)
  calc _ ≤ C₀ * (1 + ‖(-(θ * ((r : ℂ) * (x * m))))‖) ^ (-(N : ℝ)) := h
    _ ≤ C₀ * ((min 1 (‖θ‖ * c₁)) ^ (-(N : ℝ)) * (1 + r * ‖x‖) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hC₀.le
    _ = C₀ * (min 1 (‖θ‖ * c₁)) ^ (-(N : ℝ)) * (1 + r * ‖x‖) ^ (-(N : ℝ)) := by ring

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

section TorusChi

open NumberField NumberField.AdelicLevel AutomorphicForm

private theorem T1U_apply_adelicWeyl_mul_unipotentGL2_mul_diagOne (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [MeasurableSpace (AdeleRing R K)]
    {χ₁ χ₂ : (AdeleRing R K)ˣ →* ℂˣ} {φ : AdelicGL2 R K → ℂ} (hφ : IsInducedSection R K χ₁ χ₂ φ)
    (y : (AdeleRing R K)ˣ) (x : AdeleRing R K) :
    φ (adelicWeyl R K * unipotentGL2 x * diagOne y)
      = ((χ₂ y : ℂˣ) : ℂ) * φ (adelicWeyl R K * unipotentGL2 (((y⁻¹ : (AdeleRing R K)ˣ) : AdeleRing R K) * x) * 1) := by
  rw [mul_one, T1Helpers.adelicWeyl_mul_unipotentGL2_mul_diagOne R K y x,
    hφ _ (T1Helpers.centralScalar_mul_diagOne_inv_mem_adelicBorel R K y),
    T1Helpers.borelDiagFst_centralScalar_mul_diagOne_inv, T1Helpers.borelDiagSnd_centralScalar_mul_diagOne_inv,
    map_one, Units.val_one, one_mul]

variable (F : Type) [Field F] [NumberField F]

private theorem T1U_continuous_diagOne : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (diagOne y : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![(y : AdeleRing (𝓞 F) F), 0; 0, 1] := fun y => T1Helpers.diagOne_val y
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_val
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, (((diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, 1] := fun y => T1Helpers.diagOne_inv_val y
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((diagOne y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_coe_inv
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const

private theorem T1U_continuous_centralScalar :
    Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![(y : AdeleRing (𝓞 F) F), 0; 0, (y : AdeleRing (𝓞 F) F)] := fun y => T1Helpers.centralScalar_val (𝓞 F) F y
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_val
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_val
  · have h : ∀ y : (AdeleRing (𝓞 F) F)ˣ, (((centralScalar (𝓞 F) F y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        = !![((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, ((y⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)] :=
      fun y => by rw [← map_inv]; exact T1Helpers.centralScalar_val (𝓞 F) F y⁻¹
    show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((centralScalar (𝓞 F) F y)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_coe_inv
    · exact continuous_const
    · exact continuous_const
    · exact Units.continuous_coe_inv

private theorem T1U_borelDiagFst_diagOne (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨diagOne y, T1Helpers.diagOne_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = y
  rw [T1Helpers.diagOne_val]
  simp

private theorem T1U_borelDiagSnd_diagOne (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨diagOne y, T1Helpers.diagOne_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = 1 := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((diagOne y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = 1
  rw [T1Helpers.diagOne_val]
  simp

private theorem T1U_borelDiagFst_centralScalar (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagFst (⟨centralScalar (𝓞 F) F y, centralScalar_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagFst_apply_val]
  show ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = y
  rw [T1Helpers.centralScalar_val]
  simp

private theorem T1U_borelDiagSnd_centralScalar (y : (AdeleRing (𝓞 F) F)ˣ) :
    borelDiagSnd (⟨centralScalar (𝓞 F) F y, centralScalar_mem_adelicBorel (𝓞 F) F y⟩ : ↥(adelicBorel (𝓞 F) F)) = y := by
  apply Units.ext
  rw [borelDiagSnd_apply_val]
  show ((centralScalar (𝓞 F) F y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = y
  rw [T1Helpers.centralScalar_val]
  simp

private theorem T1U_continuous_monoidHom_units_of_continuous_val (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h : Continuous fun y => ((χ y : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  show Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((χ y)⁻¹ : ℂˣ) : ℂ)
  simp_rw [← map_inv]
  exact h.comp continuous_inv

private theorem T1U_continuous_chars_of_isInducedSection (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((α y : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
    (hφjc : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)
    (hne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0) :
    Continuous μ ∧ Continuous ν := by
  obtain ⟨s₀, g₀, h0⟩ := hne
  have hφc : Continuous (φ s₀) := hφjc.comp (continuous_const.prodMk continuous_id)
  have hαC : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((((α y : ℝˣ) : ℝ)) : ℂ) := Complex.continuous_ofReal.comp hαc
  have hα0 : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((((α y : ℝˣ) : ℝ)) : ℂ) ≠ 0 := fun y => Complex.ofReal_ne_zero.mpr (hα y).ne'
  have hcp : ∀ t : ℂ, Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((cpowChar α hα t y : ℂˣ) : ℂ) := by
    intro t
    simp only [cpowChar_apply_val]
    exact hαC.cpow continuous_const fun y => Complex.ofReal_mem_slitPlane.mpr (hα y)
  have hcp0 : ∀ (t : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ), ((cpowChar α hα t y : ℂˣ) : ℂ) ≠ 0 := fun t y => (cpowChar α hα t y).ne_zero

  have hμval : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((μ y : ℂˣ) : ℂ)
      = φ s₀ (diagOne y * g₀) / (((cpowChar α hα (s₀ + 1 / 2) y : ℂˣ) : ℂ) * φ s₀ g₀) := by
    intro y
    have h := hφ s₀ _ (T1Helpers.diagOne_mem_adelicBorel (𝓞 F) F y) g₀
    rw [T1U_borelDiagFst_diagOne, T1U_borelDiagSnd_diagOne, map_one, Units.val_one, mul_one, etaFst_apply,
      Units.val_mul] at h
    rw [h, eq_div_iff (mul_ne_zero (hcp0 _ y) h0)]
    ring
  have hμc' : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((μ y : ℂˣ) : ℂ) := by
    simp_rw [hμval]
    exact (hφc.comp ((T1U_continuous_diagOne F).mul continuous_const)).div ((hcp _).mul continuous_const)
      fun y => mul_ne_zero (hcp0 _ y) h0

  have hμνval : ∀ y : (AdeleRing (𝓞 F) F)ˣ, ((ν y : ℂˣ) : ℂ)
      = φ s₀ (centralScalar (𝓞 F) F y * g₀) /
        (((μ y : ℂˣ) : ℂ) * ((cpowChar α hα (s₀ + 1 / 2) y : ℂˣ) : ℂ) * ((cpowChar α hα (-(s₀ + 1 / 2)) y : ℂˣ) : ℂ)
          * φ s₀ g₀) := by
    intro y
    have h := hφ s₀ _ (centralScalar_mem_adelicBorel (𝓞 F) F y) g₀
    rw [T1U_borelDiagFst_centralScalar, T1U_borelDiagSnd_centralScalar, etaFst_apply, etaSnd_apply, Units.val_mul,
      Units.val_mul] at h
    rw [h, eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (μ y).ne_zero (hcp0 _ y)) (hcp0 _ y)) h0)]
    ring
  have hνc' : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((ν y : ℂˣ) : ℂ) := by
    simp_rw [hμνval]
    refine (hφc.comp ((T1U_continuous_centralScalar F).mul continuous_const)).div
      (((hμc'.mul (hcp _)).mul (hcp _)).mul continuous_const) fun y => ?_
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (μ y).ne_zero (hcp0 _ y)) (hcp0 _ y)) h0
  exact ⟨T1U_continuous_monoidHom_units_of_continuous_val F μ hμc',
    T1U_continuous_monoidHom_units_of_continuous_val F ν hνc'⟩

end TorusChi

namespace WhitEntire

theorem one_add_mul_rpow_neg_le (c x N : ℝ) (hc : 0 < c) (hx : 0 ≤ x) (hN : 0 ≤ N) :
    (1 + c * x) ^ (-N) ≤ (min 1 c) ^ (-N) * (1 + x) ^ (-N) := by
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hle : min 1 c * (1 + x) ≤ 1 + c * x := by
    have h1 : min 1 c ≤ 1 := min_le_left _ _
    have h2 : min 1 c * x ≤ c * x := mul_le_mul_of_nonneg_right (min_le_right _ _) hx
    linarith
  calc (1 + c * x) ^ (-N) ≤ (min 1 c * (1 + x)) ^ (-N) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hm0 (by linarith)) hle (by linarith)
    _ = (min 1 c) ^ (-N) * (1 + x) ^ (-N) := Real.mul_rpow hm0.le (by linarith)

theorem max_one_inv_le {t κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) (h : κ * a ≤ |t|) :
    max 1 |t|⁻¹ ≤ max 1 κ⁻¹ * max 1 a⁻¹ := by
  refine max_le ?_ ?_
  · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  · calc |t|⁻¹ ≤ (κ * a)⁻¹ := inv_anti₀ (mul_pos hκ ha) h
      _ = κ⁻¹ * a⁻¹ := by rw [mul_inv]
      _ ≤ max 1 κ⁻¹ * max 1 a⁻¹ :=
          mul_le_mul (le_max_right _ _) (le_max_right _ _) (inv_nonneg.2 ha.le)
            (le_trans zero_le_one (le_max_left _ _))

theorem dilation_bound_real (J : ℂ → ℝ → ℂ) (K : Set ℂ) (A N : ℕ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hJ : ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖J w t‖ ≤ C₀ * (max 1 |t|⁻¹) ^ A * (1 + |t|) ^ (-(N : ℝ)))
    (θ : ℝ) (hθ : θ ≠ 0) (c₁ r₀ : ℝ) (hc₁ : 0 < c₁) (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ (r x m : ℝ), r₀ ≤ r → x ≠ 0 → c₁ ≤ |m| →
      ‖J w (-(θ * (r * (x * m))))‖ ≤ C * (max 1 |x|⁻¹) ^ A * (1 + r * |x|) ^ (-(N : ℝ)) := by
  have hθp : 0 < |θ| := abs_pos.2 hθ
  have hθc : 0 < |θ| * c₁ := mul_pos hθp hc₁
  have hκ : 0 < |θ| * r₀ * c₁ := by positivity
  have hM1 : (1 : ℝ) ≤ max 1 (|θ| * r₀ * c₁)⁻¹ := le_max_left _ _
  refine ⟨C₀ * (max 1 (|θ| * r₀ * c₁)⁻¹) ^ A * (min 1 (|θ| * c₁)) ^ (-(N : ℝ)),
    mul_pos (mul_pos hC₀ (pow_pos (lt_of_lt_of_le one_pos hM1) A))
      (Real.rpow_pos_of_pos (lt_min one_pos hθc) _), ?_⟩
  intro w hw r x m hr hx hm
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hxpos : 0 < |x| := abs_pos.2 hx
  have hm0 : m ≠ 0 := fun h0 => by rw [h0, abs_zero] at hm; exact absurd hm (not_le.2 hc₁)
  have htne : -(θ * (r * (x * m))) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero hθ (mul_ne_zero hr0.ne' (mul_ne_zero hx hm0)))
  have h := hJ w hw _ htne
  have hrx : 0 ≤ r * |x| := mul_nonneg hr0.le (abs_nonneg x)
  have ht₀ : |(-(θ * (r * (x * m))))| = |θ| * (r * |x|) * |m| := by
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_of_pos hr0]
    ring
  have hge : |θ| * c₁ * (r * |x|) ≤ |(-(θ * (r * (x * m))))| := by
    rw [ht₀]
    calc |θ| * c₁ * (r * |x|) = |θ| * (r * |x|) * c₁ := by ring
      _ ≤ |θ| * (r * |x|) * |m| := mul_le_mul_of_nonneg_left hm (mul_nonneg (abs_nonneg θ) hrx)
  have hge' : |θ| * r₀ * c₁ * |x| ≤ |(-(θ * (r * (x * m))))| := by
    refine le_trans ?_ hge
    have : r₀ * |x| ≤ r * |x| := mul_le_mul_of_nonneg_right hr (abs_nonneg x)
    nlinarith
  have hmax : (max 1 |(-(θ * (r * (x * m))))|⁻¹) ^ A ≤ (max 1 (|θ| * r₀ * c₁)⁻¹ * max 1 |x|⁻¹) ^ A :=
    pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) (max_one_inv_le hκ hxpos hge') A
  have h1 : (1 + |(-(θ * (r * (x * m))))|) ^ (-(N : ℝ)) ≤ (1 + |θ| * c₁ * (r * |x|)) ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
  have h2 := one_add_mul_rpow_neg_le (|θ| * c₁) (r * |x|) N hθc hrx (Nat.cast_nonneg N)
  calc _ ≤ C₀ * (max 1 |(-(θ * (r * (x * m))))|⁻¹) ^ A * (1 + |(-(θ * (r * (x * m))))|) ^ (-(N : ℝ)) := h
    _ ≤ C₀ * (max 1 (|θ| * r₀ * c₁)⁻¹ * max 1 |x|⁻¹) ^ A *
          ((min 1 (|θ| * c₁)) ^ (-(N : ℝ)) * (1 + r * |x|) ^ (-(N : ℝ))) := by
        gcongr
        exact h1.trans h2
    _ = C₀ * (max 1 (|θ| * r₀ * c₁)⁻¹) ^ A * (min 1 (|θ| * c₁)) ^ (-(N : ℝ)) *
          (max 1 |x|⁻¹) ^ A * (1 + r * |x|) ^ (-(N : ℝ)) := by
        rw [mul_pow]; ring

theorem dilation_bound_complex (J : ℂ → ℂ → ℂ) (K : Set ℂ) (A N : ℕ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hJ : ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖J w ζ‖ ≤ C₀ * (max 1 ‖ζ‖⁻¹) ^ A * (1 + ‖ζ‖) ^ (-(N : ℝ)))
    (θ : ℂ) (hθ : θ ≠ 0) (c₁ r₀ : ℝ) (hc₁ : 0 < c₁) (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ (r : ℝ) (x m : ℂ), r₀ ≤ r → x ≠ 0 → c₁ ≤ ‖m‖ →
      ‖J w (-(θ * ((r : ℂ) * (x * m))))‖ ≤ C * (max 1 ‖x‖⁻¹) ^ A * (1 + r * ‖x‖) ^ (-(N : ℝ)) := by
  have hθp : 0 < ‖θ‖ := norm_pos_iff.2 hθ
  have hθc : 0 < ‖θ‖ * c₁ := mul_pos hθp hc₁
  have hκ : 0 < ‖θ‖ * r₀ * c₁ := by positivity
  have hM1 : (1 : ℝ) ≤ max 1 (‖θ‖ * r₀ * c₁)⁻¹ := le_max_left _ _
  refine ⟨C₀ * (max 1 (‖θ‖ * r₀ * c₁)⁻¹) ^ A * (min 1 (‖θ‖ * c₁)) ^ (-(N : ℝ)),
    mul_pos (mul_pos hC₀ (pow_pos (lt_of_lt_of_le one_pos hM1) A))
      (Real.rpow_pos_of_pos (lt_min one_pos hθc) _), ?_⟩
  intro w hw r x m hr hx hm
  have hr0 : 0 < r := lt_of_lt_of_le hr₀ hr
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hm0 : m ≠ 0 := fun h0 => by rw [h0, norm_zero] at hm; exact absurd hm (not_le.2 hc₁)
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have htne : -(θ * ((r : ℂ) * (x * m))) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero hθ (mul_ne_zero hrc (mul_ne_zero hx hm0)))
  have h := hJ w hw _ htne
  have hrx : 0 ≤ r * ‖x‖ := mul_nonneg hr0.le (norm_nonneg x)
  have hζ₀ : ‖(-(θ * ((r : ℂ) * (x * m))))‖ = ‖θ‖ * (r * ‖x‖) * ‖m‖ := by
    rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    ring
  have hge : ‖θ‖ * c₁ * (r * ‖x‖) ≤ ‖(-(θ * ((r : ℂ) * (x * m))))‖ := by
    rw [hζ₀]
    calc ‖θ‖ * c₁ * (r * ‖x‖) = ‖θ‖ * (r * ‖x‖) * c₁ := by ring
      _ ≤ ‖θ‖ * (r * ‖x‖) * ‖m‖ := mul_le_mul_of_nonneg_left hm (mul_nonneg (norm_nonneg θ) hrx)
  have hge' : ‖θ‖ * r₀ * c₁ * ‖x‖ ≤ |‖(-(θ * ((r : ℂ) * (x * m))))‖| := by
    rw [abs_of_nonneg (norm_nonneg _)]
    refine le_trans ?_ hge
    have : r₀ * ‖x‖ ≤ r * ‖x‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg x)
    nlinarith
  have hmax : (max 1 ‖(-(θ * ((r : ℂ) * (x * m))))‖⁻¹) ^ A ≤ (max 1 (‖θ‖ * r₀ * c₁)⁻¹ * max 1 ‖x‖⁻¹) ^ A := by
    have := max_one_inv_le hκ hxpos hge'
    rw [abs_of_nonneg (norm_nonneg _)] at this
    exact pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) this A
  have h1 : (1 + ‖(-(θ * ((r : ℂ) * (x * m))))‖) ^ (-(N : ℝ)) ≤ (1 + ‖θ‖ * c₁ * (r * ‖x‖)) ^ (-(N : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
  have h2 := one_add_mul_rpow_neg_le (‖θ‖ * c₁) (r * ‖x‖) N hθc hrx (Nat.cast_nonneg N)
  calc _ ≤ C₀ * (max 1 ‖(-(θ * ((r : ℂ) * (x * m))))‖⁻¹) ^ A *
        (1 + ‖(-(θ * ((r : ℂ) * (x * m))))‖) ^ (-(N : ℝ)) := h
    _ ≤ C₀ * (max 1 (‖θ‖ * r₀ * c₁)⁻¹ * max 1 ‖x‖⁻¹) ^ A *
          ((min 1 (‖θ‖ * c₁)) ^ (-(N : ℝ)) * (1 + r * ‖x‖) ^ (-(N : ℝ))) := by
        gcongr
        exact h1.trans h2
    _ = C₀ * (max 1 (‖θ‖ * r₀ * c₁)⁻¹) ^ A * (min 1 (‖θ‖ * c₁)) ^ (-(N : ℝ)) *
          (max 1 ‖x‖⁻¹) ^ A * (1 + r * ‖x‖) ^ (-(N : ℝ)) := by
        rw [mul_pow]; ring

end WhitEntire

section WhitN4
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

namespace WhitEntire

theorem exists_pos_le_abs_norm_of_mem (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :
    ∃ n₀ : ℝ, 0 < n₀ ∧ ∀ ξ : F, ξ ∈ I → ξ ≠ 0 → n₀ ≤ ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
  obtain ⟨a, aI, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have haF : algebraMap (𝓞 F) F a ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hNa : (0 : ℚ) < |Algebra.norm ℚ (algebraMap (𝓞 F) F a)| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr haF)
  have hNaR : (0 : ℝ) < ((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) := Rat.cast_pos.mpr hNa
  refine ⟨(((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ))⁻¹, inv_pos.2 hNaR, fun ξ hξ hξ0 => ?_⟩
  rw [hI, FractionalIdeal.mem_singleton_mul] at hξ
  obtain ⟨y, hy, hξy⟩ := hξ
  obtain ⟨b, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
  have hab : algebraMap (𝓞 F) F a * ξ = algebraMap (𝓞 F) F b := by
    rw [hξy, mul_inv_cancel_left₀ haF]
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero haF hξ0 hab
  have hNb : Algebra.norm ℚ (algebraMap (𝓞 F) F b) = ((Algebra.norm ℤ b : ℤ) : ℚ) :=
    (Algebra.coe_norm_int b).symm
  have h1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
    rw [← Rat.cast_mul, ← abs_mul, ← map_mul, hab, hNb, ← Int.cast_abs]
    have : (1 : ℤ) ≤ |Algebra.norm ℤ b| := Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hb0)
    exact_mod_cast this
  calc (((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ))⁻¹
      = (((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ))⁻¹ * 1 := (mul_one _).symm
    _ ≤ (((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ))⁻¹ *
          (((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hNaR.le)
    _ = ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by rw [← mul_assoc, inv_mul_cancel₀ hNaR.ne', one_mul]

theorem max_one_inv_le_inv_mul {a m r : ℝ} (ha : 0 < a) (hm : 0 < m) (hm1 : m ≤ 1) (hmr : m ≤ r) :
    max 1 a⁻¹ ≤ a⁻¹ * (m⁻¹ * (1 + r * a)) := by
  have hr : 0 ≤ r := hm.le.trans hmr
  have key : a ≤ m⁻¹ * (1 + r * a) := by
    rw [le_inv_mul_iff₀ hm]
    nlinarith
  refine max_le ?_ ?_
  · calc (1 : ℝ) = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
      _ ≤ a⁻¹ * (m⁻¹ * (1 + r * a)) := mul_le_mul_of_nonneg_left key (inv_nonneg.2 ha.le)
  · calc a⁻¹ = a⁻¹ * 1 := (mul_one _).symm
      _ ≤ a⁻¹ * (m⁻¹ * (1 + r * a)) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha.le)
          rw [le_inv_mul_iff₀ hm]
          nlinarith

theorem prod_max_inv_pow_le (F : Type) [Field F] [NumberField F] (A : ℕ) (n₀ r₀ : ℝ) (hn₀ : 0 < n₀) (hr₀ : 0 < r₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ξ : F), ξ ≠ 0 → n₀ ≤ ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) → ∀ r : ℝ, r₀ ≤ r →
      (∏ i : {w : InfinitePlace F // w.IsReal}, (max 1 |(mixedEmbedding F ξ).1 i|⁻¹) ^ A) *
        (∏ w : {w : InfinitePlace F // w.IsComplex}, (max 1 ‖(mixedEmbedding F ξ).2 w‖⁻¹) ^ A)
      ≤ c * (∏ i : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F ξ).1 i|) ^ (A : ℝ)) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (1 + r * ‖(mixedEmbedding F ξ).2 w‖) ^ ((2 * A : ℕ) : ℝ) := by
  classical
  set m : ℝ := min 1 r₀ with hm
  have hm0 : 0 < m := lt_min one_pos hr₀
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmr₀ : m ≤ r₀ := min_le_right _ _
  set n₁ : ℕ := Fintype.card {w : InfinitePlace F // w.IsReal} with hn₁
  set n₂ : ℕ := Fintype.card {w : InfinitePlace F // w.IsComplex} with hn₂
  refine ⟨(n₀⁻¹) ^ A * ((m⁻¹) ^ A) ^ n₁ * (((m⁻¹) ^ 2) ^ A) ^ n₂, by positivity, ?_⟩
  intro ξ hξ hN r hr
  have hmr : m ≤ r := hmr₀.trans hr
  set x := mixedEmbedding F ξ with hx
  set a : {w : InfinitePlace F // w.IsReal} → ℝ := fun i => |x.1 i| with ha
  set b : {w : InfinitePlace F // w.IsComplex} → ℝ := fun w => ‖x.2 w‖ with hb

  have hnorm : (∏ i, a i) * ∏ w, b w ^ 2 = ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
    have h := NumberField.mixedEmbedding.norm_eq_norm ξ
    rw [NumberField.mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod] at h
    rw [← h]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal i.2, Real.norm_eq_abs]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [mult_isComplex, normAtPlace_apply_of_isComplex w.2]
  have hPpos : 0 < (∏ i, a i) * ∏ w, b w ^ 2 := by rw [hnorm]; exact hn₀.trans_le hN
  have hPa : 0 < ∏ i, a i := by
    rcases (mul_pos_iff.1 hPpos) with h | h
    · exact h.1
    · exact absurd h.1 (not_lt.2 (Finset.prod_nonneg fun i _ => abs_nonneg _))
  have hPb : 0 < ∏ w, b w ^ 2 := by
    rcases (mul_pos_iff.1 hPpos) with h | h
    · exact h.2
    · exact absurd h.1 (not_lt.2 (Finset.prod_nonneg fun i _ => abs_nonneg _))
  have ha0 : ∀ i, 0 < a i := fun i =>
    lt_of_le_of_ne (abs_nonneg _) fun h0 => by
      have := Finset.prod_eq_zero (f := a) (Finset.mem_univ i) h0.symm
      rw [this] at hPa; exact lt_irrefl _ hPa
  have hb0 : ∀ w, 0 < b w := fun w =>
    lt_of_le_of_ne (norm_nonneg _) fun h0 => by
      have := Finset.prod_eq_zero (f := fun w => b w ^ 2) (Finset.mem_univ w) (show b w ^ 2 = 0 by rw [← h0]; ring)
      rw [this] at hPb; exact lt_irrefl _ hPb

  have hR : ∀ i, max 1 (a i)⁻¹ ≤ (a i)⁻¹ * (m⁻¹ * (1 + r * a i)) := fun i =>
    max_one_inv_le_inv_mul (ha0 i) hm0 hm1 hmr
  have hC : ∀ w, max 1 (b w)⁻¹ ≤ (b w ^ 2)⁻¹ * ((m⁻¹) ^ 2 * (1 + r * b w) ^ 2) := by
    intro w
    have h1 := max_one_inv_le_inv_mul (hb0 w) hm0 hm1 hmr
    have hq1 : (1 : ℝ) ≤ max 1 (b w)⁻¹ := le_max_left _ _
    calc max 1 (b w)⁻¹ ≤ (max 1 (b w)⁻¹) ^ 2 := by nlinarith
      _ ≤ ((b w)⁻¹ * (m⁻¹ * (1 + r * b w))) ^ 2 := pow_le_pow_left₀ (zero_le_one.trans hq1) h1 2
      _ = (b w ^ 2)⁻¹ * ((m⁻¹) ^ 2 * (1 + r * b w) ^ 2) := by rw [mul_pow, mul_pow, inv_pow]

  have hPR : ∏ i, (max 1 (a i)⁻¹) ^ A ≤ ∏ i, ((a i)⁻¹ * (m⁻¹ * (1 + r * a i))) ^ A :=
    Finset.prod_le_prod (fun i _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) A)
      (fun i _ => pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (hR i) A)
  have hPC : ∏ w, (max 1 (b w)⁻¹) ^ A ≤ ∏ w, ((b w ^ 2)⁻¹ * ((m⁻¹) ^ 2 * (1 + r * b w) ^ 2)) ^ A :=
    Finset.prod_le_prod (fun w _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) A)
      (fun w _ => pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (hC w) A)
  have eR : ∏ i, ((a i)⁻¹ * (m⁻¹ * (1 + r * a i))) ^ A =
      ((∏ i, a i) ^ A)⁻¹ * (((m⁻¹) ^ A) ^ n₁ * (∏ i, (1 + r * a i)) ^ A) := by
    rw [show (fun i => ((a i)⁻¹ * (m⁻¹ * (1 + r * a i))) ^ A) =
        fun i => ((a i) ^ A)⁻¹ * ((m⁻¹) ^ A * (1 + r * a i) ^ A) from
      funext fun i => by rw [mul_pow, mul_pow, inv_pow]]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_const, Finset.card_univ,
      ← hn₁]
    simp only [Finset.prod_pow]
  have eC : ∏ w, ((b w ^ 2)⁻¹ * ((m⁻¹) ^ 2 * (1 + r * b w) ^ 2)) ^ A =
      ((∏ w, b w ^ 2) ^ A)⁻¹ * ((((m⁻¹) ^ 2) ^ A) ^ n₂ * (∏ w, (1 + r * b w) ^ 2) ^ A) := by
    rw [show (fun w => ((b w ^ 2)⁻¹ * ((m⁻¹) ^ 2 * (1 + r * b w) ^ 2)) ^ A) =
        fun w => ((b w ^ 2) ^ A)⁻¹ * (((m⁻¹) ^ 2) ^ A * ((1 + r * b w) ^ 2) ^ A) from
      funext fun w => by rw [mul_pow, mul_pow, inv_pow]]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_const, Finset.card_univ,
      ← hn₂]
    simp only [Finset.prod_pow]

  have hfloor : ((∏ i, a i) ^ A)⁻¹ * ((∏ w, b w ^ 2) ^ A)⁻¹ ≤ (n₀⁻¹) ^ A := by
    rw [← mul_inv, ← mul_pow, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hPpos.le) ((inv_le_inv₀ hPpos hn₀).2 (hnorm ▸ hN)) A

  show (∏ i, (max 1 (a i)⁻¹) ^ A) * (∏ w, (max 1 (b w)⁻¹) ^ A) ≤
    (n₀⁻¹) ^ A * ((m⁻¹) ^ A) ^ n₁ * (((m⁻¹) ^ 2) ^ A) ^ n₂ *
      (∏ i, (1 + r * a i) ^ (A : ℝ)) * ∏ w, (1 + r * b w) ^ ((2 * A : ℕ) : ℝ)
  have hrhs : (n₀⁻¹) ^ A * ((m⁻¹) ^ A) ^ n₁ * (((m⁻¹) ^ 2) ^ A) ^ n₂ *
      (∏ i, (1 + r * a i) ^ (A : ℝ)) * ∏ w, (1 + r * b w) ^ ((2 * A : ℕ) : ℝ) =
      (n₀⁻¹) ^ A * ((m⁻¹) ^ A) ^ n₁ * (((m⁻¹) ^ 2) ^ A) ^ n₂ *
      (∏ i, (1 + r * a i)) ^ A * (∏ w, (1 + r * b w) ^ 2) ^ A := by
    have e1 : (∏ i, (1 + r * a i) ^ (A : ℝ)) = (∏ i, (1 + r * a i)) ^ A := by
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => Real.rpow_natCast _ _
    have e2 : (∏ w, (1 + r * b w) ^ ((2 * A : ℕ) : ℝ)) = (∏ w, (1 + r * b w) ^ 2) ^ A := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [Real.rpow_natCast, pow_mul]
    rw [e1, e2]
  rw [hrhs]
  have hr0' : 0 ≤ r := hm0.le.trans hmr
  have hmi : 0 ≤ m⁻¹ := inv_nonneg.2 hm0.le
  have hA1 : 0 ≤ ∏ i, (1 + r * a i) :=
    Finset.prod_nonneg fun i _ => add_nonneg zero_le_one (mul_nonneg hr0' (ha0 i).le)
  have hB1 : 0 ≤ ∏ w, (1 + r * b w) ^ 2 := Finset.prod_nonneg fun w _ => sq_nonneg _
  have hnn : 0 ≤ ((m⁻¹) ^ A) ^ n₁ * (∏ i, (1 + r * a i)) ^ A *
      ((((m⁻¹) ^ 2) ^ A) ^ n₂ * (∏ w, (1 + r * b w) ^ 2) ^ A) :=
    mul_nonneg (mul_nonneg (pow_nonneg (pow_nonneg hmi _) _) (pow_nonneg hA1 _))
      (mul_nonneg (pow_nonneg (pow_nonneg (pow_nonneg hmi _) _) _) (pow_nonneg hB1 _))
  calc (∏ i, (max 1 (a i)⁻¹) ^ A) * (∏ w, (max 1 (b w)⁻¹) ^ A)
      ≤ (((∏ i, a i) ^ A)⁻¹ * (((m⁻¹) ^ A) ^ n₁ * (∏ i, (1 + r * a i)) ^ A)) *
        (((∏ w, b w ^ 2) ^ A)⁻¹ * ((((m⁻¹) ^ 2) ^ A) ^ n₂ * (∏ w, (1 + r * b w) ^ 2) ^ A)) := by
        rw [← eR, ← eC]
        exact mul_le_mul hPR hPC
          (Finset.prod_nonneg fun w _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) A)
          (Finset.prod_nonneg fun i _ => pow_nonneg (mul_nonneg (inv_nonneg.2 (ha0 i).le)
            (mul_nonneg hmi (add_nonneg zero_le_one (mul_nonneg hr0' (ha0 i).le)))) A)
    _ = (((∏ i, a i) ^ A)⁻¹ * ((∏ w, b w ^ 2) ^ A)⁻¹) *
        (((m⁻¹) ^ A) ^ n₁ * (∏ i, (1 + r * a i)) ^ A *
          ((((m⁻¹) ^ 2) ^ A) ^ n₂ * (∏ w, (1 + r * b w) ^ 2) ^ A)) := by ring
    _ ≤ (n₀⁻¹) ^ A *
        (((m⁻¹) ^ A) ^ n₁ * (∏ i, (1 + r * a i)) ^ A *
          ((((m⁻¹) ^ 2) ^ A) ^ n₂ * (∏ w, (1 + r * b w) ^ 2) ^ A)) :=
        mul_le_mul_of_nonneg_right hfloor hnn
    _ = (n₀⁻¹) ^ A * ((m⁻¹) ^ A) ^ n₁ * (((m⁻¹) ^ 2) ^ A) ^ n₂ *
        (∏ i, (1 + r * a i)) ^ A * (∏ w, (1 + r * b w) ^ 2) ^ A := by ring

end WhitEntire

end WhitN4

section T1Main

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.InfinitePlace AutomorphicForm
open AutomorphicForm.WindowedSiegel Filter Topology
open NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private noncomputable def T1jR (k : ℤ) (w : ℂ) (t : ℝ) : ℂ := ∫ x : ℝ,
  ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
      * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))

private noncomputable def T1jC (a b : ℕ) (w ζ : ℂ) : ℂ := ∫ z : ℂ,
  z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))

private theorem T1jR_spec (k : ℤ) :
    ContinuousOn (fun q : ℂ × ℝ => T1jR k q.1 q.2) ({w : ℂ | 1 / 2 < w.re} ×ˢ Set.univ) ∧
    (∀ t : ℝ, DifferentiableOn ℂ (fun w : ℂ => T1jR k w t) {w : ℂ | 1 / 2 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | 1 / 2 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ t : ℝ, ‖T1jR k w t‖ ≤ C * (1 + |t|) ^ (-(N : ℝ))) :=
  AutomorphicForm.RealIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral k

private theorem T1jC_spec (a b : ℕ) :
    ContinuousOn (fun q : ℂ × ℂ => T1jC a b q.1 q.2) ({w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} ×ˢ Set.univ) ∧
    (∀ ζ : ℂ, DifferentiableOn ℂ (fun w : ℂ => T1jC a b w ζ) {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ ζ : ℂ, ‖T1jC a b w ζ‖ ≤ C * (1 + ‖ζ‖) ^ (-(N : ℝ))) :=
  AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral a b

private theorem T1JR_exists (k : ℤ) : ∃ J : ℂ → ℝ → ℂ,
    (∀ t : ℝ, t ≠ 0 → AnalyticOnNhd ℂ (fun w : ℂ => J w t) Set.univ) ∧
    (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 → J w t = T1jR k w t) ∧
    ContinuousOn (fun p : ℂ × ℝ => J p.1 p.2) (Set.univ ×ˢ {t : ℝ | t ≠ 0}) ∧
    (∀ K : Set ℂ, IsCompact K → ∃ A : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖J w t‖ ≤ C * (max 1 |t|⁻¹) ^ A * (1 + |t|) ^ (-(N : ℝ))) :=
  AutomorphicForm.RealIwasawa.exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero k

private noncomputable def T1JR (k : ℤ) : ℂ → ℝ → ℂ := (T1JR_exists k).choose

private theorem T1JR_spec (k : ℤ) :
    (∀ t : ℝ, t ≠ 0 → AnalyticOnNhd ℂ (fun w : ℂ => T1JR k w t) Set.univ) ∧
    (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 → T1JR k w t = T1jR k w t) ∧
    ContinuousOn (fun p : ℂ × ℝ => T1JR k p.1 p.2) (Set.univ ×ˢ {t : ℝ | t ≠ 0}) ∧
    (∀ K : Set ℂ, IsCompact K → ∃ A : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ t : ℝ, t ≠ 0 → ‖T1JR k w t‖ ≤ C * (max 1 |t|⁻¹) ^ A * (1 + |t|) ^ (-(N : ℝ))) :=
  (T1JR_exists k).choose_spec

private theorem T1JC_exists (a b : ℕ) : ∃ J : ℂ → ℂ → ℂ,
    (∀ ζ : ℂ, ζ ≠ 0 → AnalyticOnNhd ℂ (fun w : ℂ => J w ζ) Set.univ) ∧
    (∀ (w : ℂ) (ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 → J w ζ = T1jC a b w ζ) ∧
    ContinuousOn (fun p : ℂ × ℂ => J p.1 p.2) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) ∧
    (∀ K : Set ℂ, IsCompact K → ∃ A : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖J w ζ‖ ≤ C * (max 1 ‖ζ‖⁻¹) ^ A * (1 + ‖ζ‖) ^ (-(N : ℝ))) :=
  AutomorphicForm.ComplexIwasawa.exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero a b

private noncomputable def T1JC (a b : ℕ) : ℂ → ℂ → ℂ := (T1JC_exists a b).choose

private theorem T1JC_spec (a b : ℕ) :
    (∀ ζ : ℂ, ζ ≠ 0 → AnalyticOnNhd ℂ (fun w : ℂ => T1JC a b w ζ) Set.univ) ∧
    (∀ (w : ℂ) (ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 → T1JC a b w ζ = T1jC a b w ζ) ∧
    ContinuousOn (fun p : ℂ × ℂ => T1JC a b p.1 p.2) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) ∧
    (∀ K : Set ℂ, IsCompact K → ∃ A : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖T1JC a b w ζ‖ ≤ C * (max 1 ‖ζ‖⁻¹) ^ A * (1 + ‖ζ‖) ^ (-(N : ℝ))) :=
  (T1JC_exists a b).choose_spec

variable (F : Type) [Field F] [NumberField F]

private noncomputable def T1frq (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F :=
  algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (y : AdeleRing (𝓞 F) F)

private noncomputable def T1Kc (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (a : (AdeleRing (𝓞 F) F)ˣ)
    (u x : AdeleRing (𝓞 F) F) : ℂ :=
  (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
    * ((((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (x * u))

open scoped Classical in

private noncomputable def T1AR (n : ℕ) (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ) (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ i : {w : InfinitePlace F // w.IsReal}, T1JR (kdat j i) (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)
    (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i))

open scoped Classical in

private noncomputable def T1AC (n : ℕ) (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ w : {w : InfinitePlace F // w.IsComplex}, T1JC (abm j w).1 (abm j w).2.1
    (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)
    (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w))

private noncomputable def T1Eu (S : Finset (HeightOneSpectrum (𝓞 F))) (zE : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ)
    (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - zE v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))

private noncomputable def T1Fi (n : ℕ) (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), Φ j v ((x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s

private noncomputable def T1J (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ((ν y : ℂˣ) : ℂ) * ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ)
    * ∑ j : Fin n, C j s * T1Kc F ψ a u (T1frq F ξ y) * T1AR F n kdat τr θr a j s (T1frq F ξ y)
        * T1AC F n abm τc θc a j s (T1frq F ξ y) * T1Fi F n Φ a j s (T1frq F ξ y)

open scoped Classical in

private noncomputable def T1ARo (n : ℕ) (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
    (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ) (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ i : {w : InfinitePlace F // w.IsReal}, T1jR (kdat j i) (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)
    (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i))

open scoped Classical in

private noncomputable def T1ACo (n : ℕ) (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (j : Fin n) (s : ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  ∏ w : {w : InfinitePlace F // w.IsComplex}, T1jC (abm j w).1 (abm j w).2.1
    (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)
    (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w))

private noncomputable def T1Jo (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (zE : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  ((ν y : ℂˣ) : ℂ) * ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ)
    * ∑ j : Fin n, C j s * T1Kc F ψ a u (T1frq F ξ y) * T1ARo F n kdat τr θr a j s (T1frq F ξ y)
        * T1ACo F n abm τc θc a j s (T1frq F ξ y) * (T1Eu F S zE s * T1Fi F n Φ a j s (T1frq F ξ y))

variable {F}

private theorem T1frq_mul_eq_val (a : (AdeleRing (𝓞 F) F)ˣ) (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ) :
    T1frq F ξ y * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = ((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * y * a⁻¹ :
          (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
  simp only [T1frq, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0]

open scoped Classical in

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

private theorem T1frq_freqR_ne_zero (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ)
    (i : {w : InfinitePlace F // w.IsReal}) :
    -(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (T1frq F ξ y * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i) ≠ 0 := by
  rw [T1frq_mul_eq_val a ξ y]
  refine neg_ne_zero.mpr (mul_ne_zero (hθr i) fun h => ?_)
  have h2 := T1Helpers.norm_ringEquiv_mixedSpace_fst F
    (((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * y * a⁻¹ :
      (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1) i
  rw [h, abs_zero] at h2
  exact T1U_idele_fst_ne_zero _ _ (norm_eq_zero.mp h2.symm)

private theorem T1frq_freqC_ne_zero (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ)
    (w : {w : InfinitePlace F // w.IsComplex}) :
    -(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
      (T1frq F ξ y * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w) ≠ 0 := by
  rw [T1frq_mul_eq_val a ξ y]
  refine neg_ne_zero.mpr (mul_ne_zero (hθc w) fun h => ?_)
  have h2 := T1Helpers.norm_ringEquiv_mixedSpace_snd F
    (((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * y * a⁻¹ :
      (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1) w
  rw [h, norm_zero] at h2
  exact T1U_idele_fst_ne_zero _ _ (norm_eq_zero.mp h2.symm)

open scoped Classical in

private theorem T1J_analyticOnNhd (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hC : ∀ j, Differentiable ℂ (C j))
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (hΦd : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w))
    (hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ) :
    AnalyticOnNhd ℂ (fun s => T1J F α hα ν ψ n C kdat τr abm τc θr θc a u Φ ξ s y) Set.univ := by
  classical
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
  set x : AdeleRing (𝓞 F) F := T1frq F ξ y with hx
  set Ux : (AdeleRing (𝓞 F) F)ˣ :=
    Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * y * a⁻¹ with hUx
  have hUx' : (Ux : AdeleRing (𝓞 F) F) = x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) :=
    (T1frq_mul_eq_val a ξ y).symm
  have hcp : Differentiable ℂ (fun s : ℂ => ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ)) := by
    simp only [cpowChar_apply_val]
    exact Differentiable.const_cpow ((differentiable_const _).sub differentiable_id)
      (Or.inl (Complex.ofReal_ne_zero.mpr (hα y).ne'))
  have hKc : DifferentiableOn ℂ (fun s : ℂ => T1Kc F ψ a u x) Set.univ := differentiableOn_const _
  have hAR : ∀ j, DifferentiableOn ℂ (fun s => T1AR F n kdat τr θr a j s x) Set.univ := by
    intro j
    simp only [T1AR]
    refine DifferentiableOn.fun_finsetProd fun i _ => ?_
    obtain ⟨hR1, -, -, -⟩ := T1JR_spec (kdat j i)
    have hg : Differentiable ℂ (fun s : ℂ => s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2) :=
      (differentiable_id.add_const _).add_const _
    exact ((hR1 _ (T1frq_freqR_ne_zero θr hθr a ξ y i)).differentiableOn).comp hg.differentiableOn
      (Set.mapsTo_univ _ _)
  have hAC : ∀ j, DifferentiableOn ℂ (fun s => T1AC F n abm τc θc a j s x) Set.univ := by
    intro j
    simp only [T1AC]
    refine DifferentiableOn.fun_finsetProd fun w _ => ?_
    obtain ⟨hC1, -, -, -⟩ := T1JC_spec (abm j w).1 (abm j w).2.1
    have hg : Differentiable ℂ (fun s : ℂ =>
        2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2) :=
      (((differentiable_id.const_mul _).add_const _).add_const _).add_const _
    exact ((hC1 _ (T1frq_freqC_ne_zero θc hθc a ξ y w)).differentiableOn).comp hg.differentiableOn
      (Set.mapsTo_univ _ _)
  have hFi : ∀ j, DifferentiableOn ℂ (fun s => T1Fi F n Φ a j s x) Set.univ := by
    intro j
    have hprod : DifferentiableOn ℂ (fun s => ∏ v ∈ S ∪ (T1U_idele_valued_ne_one_finite Ux).toFinset,
        Φ j v ((x * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s) Set.univ :=
      DifferentiableOn.fun_finsetProd fun v _ => (hΦd j v _).differentiableOn
    exact hprod.congr fun s _ => T1Fi_eq_prod S n Φ hΦ1 a j s x Ux hUx'
  simp only [T1J]
  refine ((differentiableOn_const _).mul hcp.differentiableOn).mul (DifferentiableOn.fun_sum fun j _ => ?_)
  exact ((((hC j).differentiableOn.mul hKc).mul (hAR j)).mul (hAC j)).mul (hFi j)

open scoped Classical in

private theorem T1J_continuousOn (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((α y : ℝˣ) : ℝ) : ℂ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hνc : Continuous ν)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F) (thr : HeightOneSpectrum (𝓞 F) → ℤ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hC : ∀ j, Differentiable ℂ (C j))
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (hΦd : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w))
    (hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (hΦlc : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w₀ : v.adicCompletion F), w₀ ≠ 0 → ∃ δ : ℤ,
      ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s)
    (ξ : {ξ : F // ξ ≠ 0}) :
    ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1J F α hα ν ψ n C kdat τr abm τc θr θc a u Φ ξ p.1 p.2)
      (Set.univ ×ˢ Set.univ) := by
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

  have hAR : ∀ j, ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1AR F n kdat τr θr a j p.1 (T1frq F ξ p.2))
      (Set.univ ×ˢ (Set.univ : Set (AdeleRing (𝓞 F) F)ˣ)) := by
    intro j
    simp only [T1AR]
    refine continuousOn_finsetProd _ fun i _ => ?_
    obtain ⟨-, -, hR1, -⟩ := T1JR_spec (kdat j i)
    have hg : Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ =>
        ((p.1 + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2 : ℂ),
          -(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
            (T1frq F ξ p.2 * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i)) :=
      (((continuous_fst.add continuous_const).add continuous_const)).prodMk
        ((continuous_const.mul ((T1U_continuous_mixedSpace_fst i).comp (continuous_fst.comp hfrqc))).neg)
    have hmaps : Set.MapsTo (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ =>
        ((p.1 + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2 : ℂ),
          -(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
            (T1frq F ξ p.2 * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i)))
        (Set.univ ×ˢ (Set.univ : Set (AdeleRing (𝓞 F) F)ˣ)) (Set.univ ×ˢ {t : ℝ | t ≠ 0}) := by
      intro p _
      exact ⟨Set.mem_univ _, T1frq_freqR_ne_zero θr hθr a ξ p.2 i⟩
    have hcomp := hR1.comp hg.continuousOn hmaps
    simpa only [Function.comp_def] using hcomp
  have hAC : ∀ j, ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1AC F n abm τc θc a j p.1 (T1frq F ξ p.2))
      (Set.univ ×ˢ (Set.univ : Set (AdeleRing (𝓞 F) F)ˣ)) := by
    intro j
    simp only [T1AC]
    refine continuousOn_finsetProd _ fun w _ => ?_
    obtain ⟨-, -, hC1, -⟩ := T1JC_spec (abm j w).1 (abm j w).2.1
    have hg : Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ =>
        ((2 * p.1 + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2 : ℂ),
          -(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
            (T1frq F ξ p.2 * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w)) :=
      ((((continuous_const.mul continuous_fst).add continuous_const).add continuous_const).add
        continuous_const).prodMk
        ((continuous_const.mul ((T1U_continuous_mixedSpace_snd w).comp (continuous_fst.comp hfrqc))).neg)
    have hmaps : Set.MapsTo (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ =>
        ((2 * p.1 + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2 : ℂ),
          -(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
            (T1frq F ξ p.2 * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w)))
        (Set.univ ×ˢ (Set.univ : Set (AdeleRing (𝓞 F) F)ˣ)) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) := by
      intro p _
      exact ⟨Set.mem_univ _, T1frq_freqC_ne_zero θc hθc a ξ p.2 w⟩
    have hcomp := hC1.comp hg.continuousOn hmaps
    simpa only [Function.comp_def] using hcomp

  have hFi : ∀ j, Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => T1Fi F n Φ a j p.1 (T1frq F ξ p.2) := by
    intro j
    have h := T1F4_continuous_finprod F S n thr Φ hΦd hΦ1 hΦlc a x₀ j
    refine h.congr fun p => ?_
    simp only [T1Fi, hfrq]

  have hνc' : Continuous fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((ν p.2 : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (hνc.comp continuous_snd)
  simp only [T1J]
  refine ((hνc'.continuousOn.mul hcp.continuousOn).mul (continuousOn_finsetSum _ fun j _ => ?_))
  exact ((((((hC j).continuous.comp continuous_fst).continuousOn.mul hKc.continuousOn).mul (hAR j)).mul
    (hAC j)).mul (hFi j).continuousOn)

open scoped Classical in

open scoped Classical in

private theorem T1AR_dilation_bound (n : ℕ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (C₀ : Set ℂ) (hC₀ : IsCompact C₀)
    (c₁ r₀ : ℝ) (hc₁ : 0 < c₁) (hr₀ : 0 < r₀) :
    ∃ A : ℕ, ∀ N : ℕ, ∃ D : Fin n → ℝ, (∀ j, 0 ≤ D j) ∧ ∀ (j : Fin n), ∀ s ∈ C₀,
      ∀ (z uu : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), r₀ ≤ r →
      (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
      (∀ i : {w : InfinitePlace F // w.IsReal},
        c₁ ≤ |(InfiniteAdeleRing.ringEquiv_mixedSpace F ((uu * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i|) →
      ∀ ξ : {ξ : F // ξ ≠ 0}, ‖T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu))‖
        ≤ D j * ∏ i : {w : InfinitePlace F // w.IsReal},
            ((max 1 |(mixedEmbedding F (ξ : F)).1 i|⁻¹) ^ A *
              (1 + r * |(mixedEmbedding F (ξ : F)).1 i|) ^ (-(N : ℝ))) := by
  classical
  have hKr : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}),
      IsCompact ((fun s : ℂ => s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2) '' C₀) :=
    fun j i => hC₀.image ((continuous_id.add continuous_const).add continuous_const)
  choose AR hAR using fun (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) =>
    (T1JR_spec (kdat j i)).2.2.2 _ (hKr j i)
  refine ⟨Finset.univ.sup (fun p : Fin n × {w : InfinitePlace F // w.IsReal} => AR p.1 p.2), fun N => ?_⟩
  have hAle : ∀ j i, AR j i ≤ Finset.univ.sup (fun p : Fin n × {w : InfinitePlace F // w.IsReal} => AR p.1 p.2) :=
    fun j i => Finset.le_sup (f := fun p : Fin n × {w : InfinitePlace F // w.IsReal} => AR p.1 p.2)
      (Finset.mem_univ (j, i))
  choose CR hCR0 hCR using fun (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) => hAR j i N
  choose DR hDR0 hDR using fun (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) =>
    WhitEntire.dilation_bound_real (T1JR (kdat j i)) _ (AR j i) N (CR j i) (hCR0 j i) (hCR j i) (θr i) (hθr i)
      c₁ r₀ hc₁ hr₀
  refine ⟨fun j => ∏ i, DR j i, fun j => Finset.prod_nonneg fun i _ => (hDR0 j i).le,
    fun j s hs z uu r hrle hz1 hufc ξ => ?_⟩
  have hr : 0 < r := lt_of_lt_of_le hr₀ hrle
  have hcoR : ∀ i : {w : InfinitePlace F // w.IsReal},
      (InfiniteAdeleRing.ringEquiv_mixedSpace F
        (T1frq F ξ (z * uu) * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i
        = r * ((mixedEmbedding F (ξ : F)).1 i
          * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((uu * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i) := by
    intro i
    simp only [T1frq]
    rw [T1Helpers.ringEquiv_mixedSpace_fst_mul_dilation_mul F z uu r hz1, mul_assoc (algebraMap F _ (ξ : F)),
      ← Units.val_mul, (T1F5_mixedSpace_algebraMap_mul F (ξ : F) _).1 i]
  have hxi : ∀ i : {w : InfinitePlace F // w.IsReal}, (mixedEmbedding F (ξ : F)).1 i ≠ 0 := fun i => by
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
    exact (map_ne_zero _).mpr ξ.2
  simp only [T1AR]
  rw [norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [hcoR i]
  refine (hDR j i _ ⟨s, hs, rfl⟩ r _ _ hrle (hxi i) (hufc i)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hDR0 j i).le
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) (hAle j i))
    (Real.rpow_nonneg (by positivity) _)

open scoped Classical in

private theorem T1AC_dilation_bound (n : ℕ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (C₀ : Set ℂ) (hC₀ : IsCompact C₀)
    (c₁ r₀ : ℝ) (hc₁ : 0 < c₁) (hr₀ : 0 < r₀) :
    ∃ A : ℕ, ∀ N : ℕ, ∃ D : Fin n → ℝ, (∀ j, 0 ≤ D j) ∧ ∀ (j : Fin n), ∀ s ∈ C₀,
      ∀ (z uu : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), r₀ ≤ r →
      (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
      (∀ w : {w : InfinitePlace F // w.IsComplex},
        c₁ ≤ ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F ((uu * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w‖) →
      ∀ ξ : {ξ : F // ξ ≠ 0}, ‖T1AC F n abm τc θc a j s (T1frq F ξ (z * uu))‖
        ≤ D j * ∏ w : {w : InfinitePlace F // w.IsComplex},
          ((max 1 ‖(mixedEmbedding F (ξ : F)).2 w‖⁻¹) ^ A *
            (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(N : ℝ))) := by
  classical
  have hKc : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
      IsCompact ((fun s : ℂ => 2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2) '' C₀) :=
    fun j w => hC₀.image ((((continuous_const.mul continuous_id).add continuous_const).add
      continuous_const).add continuous_const)
  choose AC hAC using fun (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) =>
    (T1JC_spec (abm j w).1 (abm j w).2.1).2.2.2 _ (hKc j w)
  refine ⟨Finset.univ.sup (fun p : Fin n × {w : InfinitePlace F // w.IsComplex} => AC p.1 p.2), fun N => ?_⟩
  have hAle : ∀ j w, AC j w ≤ Finset.univ.sup (fun p : Fin n × {w : InfinitePlace F // w.IsComplex} => AC p.1 p.2) :=
    fun j w => Finset.le_sup (f := fun p : Fin n × {w : InfinitePlace F // w.IsComplex} => AC p.1 p.2)
      (Finset.mem_univ (j, w))
  choose CC hCC0 hCC using fun (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) => hAC j w N
  choose DC hDC0 hDC using fun (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) =>
    WhitEntire.dilation_bound_complex (T1JC (abm j w).1 (abm j w).2.1) _ (AC j w) N (CC j w) (hCC0 j w) (hCC j w)
      (θc w) (hθc w) c₁ r₀ hc₁ hr₀
  refine ⟨fun j => ∏ w, DC j w, fun j => Finset.prod_nonneg fun w _ => (hDC0 j w).le,
    fun j s hs z uu r hrle hz1 hufc ξ => ?_⟩
  have hr : 0 < r := lt_of_lt_of_le hr₀ hrle
  have hcoC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      (InfiniteAdeleRing.ringEquiv_mixedSpace F
        (T1frq F ξ (z * uu) * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w
        = (r : ℂ) * ((mixedEmbedding F (ξ : F)).2 w
          * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((uu * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w) := by
    intro w
    simp only [T1frq]
    rw [T1Helpers.ringEquiv_mixedSpace_snd_mul_dilation_mul F z uu r hz1, mul_assoc (algebraMap F _ (ξ : F)),
      ← Units.val_mul, (T1F5_mixedSpace_algebraMap_mul F (ξ : F) _).2 w]
  have hxw : ∀ w : {w : InfinitePlace F // w.IsComplex}, (mixedEmbedding F (ξ : F)).2 w ≠ 0 := fun w => by
    rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
    exact (map_ne_zero _).mpr ξ.2
  simp only [T1AC]
  rw [norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => norm_nonneg _) fun w _ => ?_
  rw [hcoC w]
  refine (hDC j w _ ⟨s, hs, rfl⟩ r _ _ hrle (hxw w) (hufc w)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hDC0 j w).le
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) (hAle j w))
    (Real.rpow_nonneg (by positivity) _)

private theorem T1Kc_norm_le (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ x : AdeleRing (𝓞 F) F, ‖T1Kc F ψ a u x‖ ≤ K0 := by
  refine ⟨‖T1Kc F ψ a u 0‖, norm_nonneg _, fun x => le_of_eq ?_⟩
  simp only [T1Kc, norm_mul, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ]

private theorem WE_absorb {ιR ιC : Type} [Fintype ιR] [Fintype ιC] (xR : ιR → ℝ) (xC : ιC → ℝ)
    (hxR : ∀ i, 0 ≤ xR i) (hxC : ∀ w, 0 ≤ xC w)
    (A AR AC N : ℕ) (hAR : AR ≤ A) (hAC : AC ≤ A) (r cabs : ℝ) (hr : 0 < r)
    (habs : (∏ i, (max 1 (xR i)⁻¹) ^ A) * (∏ w, (max 1 (xC w)⁻¹) ^ A)
      ≤ cabs * (∏ i, (1 + r * xR i) ^ (A : ℝ)) * ∏ w, (1 + r * xC w) ^ ((2 * A : ℕ) : ℝ)) :
    (∏ i, ((max 1 (xR i)⁻¹) ^ AR * (1 + r * xR i) ^ (-((N + A : ℕ) : ℝ)))) *
      (∏ w, ((max 1 (xC w)⁻¹) ^ AC * (1 + r * xC w) ^ (-((2 * N + 2 * A : ℕ) : ℝ))))
      ≤ cabs * (∏ i, (1 + r * xR i) ^ (-(N : ℝ))) * ∏ w, (1 + r * xC w) ^ (-(2 * N : ℝ)) := by
  have hpR : ∀ i, 0 < 1 + r * xR i := fun i => by have := mul_nonneg hr.le (hxR i); linarith
  have hpC : ∀ w, 0 < 1 + r * xC w := fun w => by have := mul_nonneg hr.le (hxC w); linarith
  have hm1 : ∀ (x : ℝ), 1 ≤ max 1 x⁻¹ := fun x => le_max_left _ _

  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

  have hR1 : (∏ i, (max 1 (xR i)⁻¹) ^ AR) ≤ ∏ i, (max 1 (xR i)⁻¹) ^ A :=
    Finset.prod_le_prod (fun i _ => pow_nonneg (le_trans zero_le_one (hm1 _)) _)
      fun i _ => pow_le_pow_right₀ (hm1 _) hAR
  have hC1 : (∏ w, (max 1 (xC w)⁻¹) ^ AC) ≤ ∏ w, (max 1 (xC w)⁻¹) ^ A :=
    Finset.prod_le_prod (fun w _ => pow_nonneg (le_trans zero_le_one (hm1 _)) _)
      fun w _ => pow_le_pow_right₀ (hm1 _) hAC
  have hdR0 : 0 ≤ ∏ i, (1 + r * xR i) ^ (-((N + A : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hpR i).le _
  have hdC0 : 0 ≤ ∏ w, (1 + r * xC w) ^ (-((2 * N + 2 * A : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun w _ => Real.rpow_nonneg (hpC w).le _
  have hmC0 : 0 ≤ ∏ w, (max 1 (xC w)⁻¹) ^ AC :=
    Finset.prod_nonneg fun w _ => pow_nonneg (le_trans zero_le_one (hm1 _)) _
  have hmRA0 : 0 ≤ ∏ i, (max 1 (xR i)⁻¹) ^ A :=
    Finset.prod_nonneg fun i _ => pow_nonneg (le_trans zero_le_one (hm1 _)) _

  have hkeyR : ∀ i, (1 + r * xR i) ^ (A : ℝ) * (1 + r * xR i) ^ (-((N + A : ℕ) : ℝ))
      = (1 + r * xR i) ^ (-(N : ℝ)) := by
    intro i
    rw [← Real.rpow_add (hpR i)]
    congr 1
    push_cast
    ring
  have hkeyC : ∀ w, (1 + r * xC w) ^ ((2 * A : ℕ) : ℝ) * (1 + r * xC w) ^ (-((2 * N + 2 * A : ℕ) : ℝ))
      = (1 + r * xC w) ^ (-(2 * N : ℝ)) := by
    intro w
    rw [← Real.rpow_add (hpC w)]
    congr 1
    push_cast
    ring
  calc (∏ i, (max 1 (xR i)⁻¹) ^ AR) * (∏ i, (1 + r * xR i) ^ (-((N + A : ℕ) : ℝ)))
        * ((∏ w, (max 1 (xC w)⁻¹) ^ AC) * ∏ w, (1 + r * xC w) ^ (-((2 * N + 2 * A : ℕ) : ℝ)))
      = ((∏ i, (max 1 (xR i)⁻¹) ^ AR) * ∏ w, (max 1 (xC w)⁻¹) ^ AC)
        * ((∏ i, (1 + r * xR i) ^ (-((N + A : ℕ) : ℝ))) * ∏ w, (1 + r * xC w) ^ (-((2 * N + 2 * A : ℕ) : ℝ))) := by
          ring
    _ ≤ ((∏ i, (max 1 (xR i)⁻¹) ^ A) * ∏ w, (max 1 (xC w)⁻¹) ^ A)
        * ((∏ i, (1 + r * xR i) ^ (-((N + A : ℕ) : ℝ))) * ∏ w, (1 + r * xC w) ^ (-((2 * N + 2 * A : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hR1 hC1 hmC0 hmRA0) (mul_nonneg hdR0 hdC0)
    _ ≤ (cabs * (∏ i, (1 + r * xR i) ^ (A : ℝ)) * ∏ w, (1 + r * xC w) ^ ((2 * A : ℕ) : ℝ))
        * ((∏ i, (1 + r * xR i) ^ (-((N + A : ℕ) : ℝ))) * ∏ w, (1 + r * xC w) ^ (-((2 * N + 2 * A : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right habs (mul_nonneg hdR0 hdC0)
    _ = cabs * ((∏ i, ((1 + r * xR i) ^ (A : ℝ) * (1 + r * xR i) ^ (-((N + A : ℕ) : ℝ))))
        * ∏ w, ((1 + r * xC w) ^ ((2 * A : ℕ) : ℝ) * (1 + r * xC w) ^ (-((2 * N + 2 * A : ℕ) : ℝ)))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          ring
    _ = cabs * (∏ i, (1 + r * xR i) ^ (-(N : ℝ))) * ∏ w, (1 + r * xC w) ^ (-(2 * N : ℝ)) := by
          simp only [hkeyR, hkeyC]
          ring

open scoped Classical in

private theorem T1J_bound (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hν : IsUnitaryChar (𝓞 F) F ν)
    (hαz : ∀ (s : ℂ) (z uu : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r → (z : AdeleRing (𝓞 F) F).2 = 1 →
      (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
      ‖((cpowChar α hα (1 / 2 - s) (z * uu) : ℂˣ) : ℂ)‖
        = r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) * ((α uu : ℝˣ) : ℝ) ^ (1 / 2 - s.re))
    (hαc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((α y : ℝˣ) : ℝ))
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hθc : ∀ w, θc w ≠ 0)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F) (thr : HeightOneSpectrum (𝓞 F) → ℤ)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (hC : ∀ j, Differentiable ℂ (C j))
    (habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2)
    (hthr : ∀ v ∉ S, thr v = 0)
    (hΦ1 : ∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1)
    (hΦ0 : ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F) (s : ℂ), w ≠ 0 →
      WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0)
    (hΦb : ∀ R : ℝ, ∃ (M : ℝ) (κ : ℕ), 0 ≤ M ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F))
      (w : v.adicCompletion F) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
        ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ)
    (C₀ : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ) (r₀ : ℝ) (hC₀ : IsCompact C₀) (hU : IsCompact U) (hr₀ : 0 < r₀) :
    ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), ∀ N : ℕ, ∃ c : ℝ,
      ∀ s ∈ C₀, ∀ uu ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), r₀ ≤ r → (z : AdeleRing (𝓞 F) F).2 = 1 →
        (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
        ∀ ξ : {ξ : F // ξ ≠ 0},
          ((ξ : F) ∉ I → T1J F α hα ν ψ n C kdat τr abm τc θr θc a u Φ ξ s (z * uu) = 0) ∧
          ‖T1J F α hα ν ψ n C kdat τr abm τc θr θc a u Φ ξ s (z * uu)‖
            ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
              (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
              (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
              ∏ w : {w : InfinitePlace F // w.IsComplex},
                (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ)) := by
  classical

  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn continuousOn_id

  have hUa : IsCompact ((fun uu : (AdeleRing (𝓞 F) F)ˣ => uu * a⁻¹) '' U) :=
    hU.image (continuous_id.mul continuous_const)
  obtain ⟨L, hLfin, hL0, hL⟩ := T1Helpers.exists_finite_support_valuation_bounds_of_isCompact F _ hUa
  obtain ⟨c₁, c₂, hc₁, hcoord⟩ := T1Helpers.exists_mixedSpace_coord_bounds_of_isCompact F _ hUa

  obtain ⟨k, I, cF, hcF0, hF⟩ := T1F3_finBound F S n thr Φ hthr hΦ1 hΦ0 hΦb L hLfin hL0 R
  refine ⟨k, I, ?_⟩

  obtain ⟨n₀, hn₀, hnI⟩ := WhitEntire.exists_pos_le_abs_norm_of_mem F I
  obtain ⟨AR, hARall⟩ := T1AR_dilation_bound n kdat τr θr hθr a C₀ hC₀ c₁ r₀ hc₁ hr₀
  obtain ⟨AC, hACall⟩ := T1AC_dilation_bound n abm τc θc hθc a C₀ hC₀ c₁ r₀ hc₁ hr₀
  obtain ⟨cabs, hcabs0, hcabs⟩ := WhitEntire.prod_max_inv_pow_le F (max AR AC) n₀ r₀ hn₀ hr₀
  intro N

  obtain ⟨DR, hDR0, hDR⟩ := hARall (N + max AR AC)
  obtain ⟨DC, hDC0, hDC⟩ := hACall (2 * N + 2 * max AR AC)

  choose BC hBC using fun j : Fin n => hC₀.exists_bound_of_continuousOn (hC j).continuous.continuousOn
  have hcontA : ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => ((α p.2 : ℝˣ) : ℝ) ^ (1 / 2 - p.1.re))
      (C₀ ×ˢ U) := by
    refine Continuous.continuousOn ?_
    exact (hαc.comp continuous_snd).rpow (continuous_const.sub (Complex.continuous_re.comp continuous_fst))
      fun p => Or.inl (hα p.2).ne'
  obtain ⟨BA, hBA⟩ := (hC₀.prod hU).exists_bound_of_continuousOn hcontA
  obtain ⟨K0, hK00, hK0⟩ := T1Kc_norm_le ψ hψ a u

  set c : ℝ := |BA| * ∑ j : Fin n, |BC j| * K0 * DR j * DC j * cF * cabs with hc
  refine ⟨c, fun s hs uu huu z r hrle hz2 hz1 ξ => ?_⟩
  have hr : 0 < r := lt_of_lt_of_le hr₀ hrle
  have hsR : ‖s‖ ≤ R := hR s hs
  set uf : (AdeleRing (𝓞 F) F)ˣ := uu * a⁻¹ with huf
  have hufmem : uf ∈ (fun uu : (AdeleRing (𝓞 F) F)ˣ => uu * a⁻¹) '' U := ⟨uu, huu, rfl⟩
  have hufv := hL uf hufmem
  have hufc := hcoord uf hufmem

  have hFi : ∀ j, T1Fi F n Φ a j s (T1frq F ξ (z * uu))
      = ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (uf : AdeleRing (𝓞 F) F)).2 v) s := by
    intro j
    simp only [T1Fi, T1frq]
    refine finprod_congr fun v => ?_
    rw [T1Helpers.snd_mul_dilation_mul_apply F z uu hz2, huf, Units.val_mul, mul_assoc]
  have hFj := fun j => hF j s hsR uf hufv ξ
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
    set MR : ℝ := ∏ i : {w : InfinitePlace F // w.IsReal},
        ((max 1 |(mixedEmbedding F (ξ : F)).1 i|⁻¹) ^ AR *
          (1 + r * |(mixedEmbedding F (ξ : F)).1 i|) ^ (-((N + max AR AC : ℕ) : ℝ))) with hMR
    set MC : ℝ := ∏ w : {w : InfinitePlace F // w.IsComplex},
        ((max 1 ‖(mixedEmbedding F (ξ : F)).2 w‖⁻¹) ^ AC *
          (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-((2 * N + 2 * max AR AC : ℕ) : ℝ))) with hMC
    have hPR0 : 0 ≤ PR := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
    have hPC0 : 0 ≤ PC := Finset.prod_nonneg fun w _ => Real.rpow_nonneg (by positivity) _
    have hMX0 : 0 ≤ MX := pow_nonneg (le_trans zero_le_one (le_max_left _ _)) k
    have hMR0 : 0 ≤ MR := Finset.prod_nonneg fun i _ =>
      mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
        (Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg hr.le (abs_nonneg _))) _)
    have hMC0 : 0 ≤ MC := Finset.prod_nonneg fun w _ =>
      mul_nonneg (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
        (Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg hr.le (norm_nonneg _))) _)

    by_cases hξI : (ξ : F) ∈ I
    swap
    · have hzero : ∀ j, T1Fi F n Φ a j s (T1frq F ξ (z * uu)) = 0 := fun j => by
        rw [hFi j]
        exact (hFj j).1 hξI
      have hc0 : 0 ≤ c := by
        rw [hc]
        refine mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun j _ => ?_)
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hK00) (hDR0 j)) (hDC0 j))
          hcF0) hcabs0.le
      simp only [T1J, hzero, mul_zero, Finset.sum_const_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc0 (Real.rpow_nonneg hr.le _)) hMX0) hPR0) hPC0
    have habsorb : MR * MC ≤ cabs * PR * PC :=
      WE_absorb (fun i => |(mixedEmbedding F (ξ : F)).1 i|) (fun w => ‖(mixedEmbedding F (ξ : F)).2 w‖)
        (fun i => abs_nonneg _) (fun w => norm_nonneg _) (max AR AC) AR AC N (le_max_left _ _) (le_max_right _ _)
        r cabs hr (hcabs (ξ : F) ξ.2 (hnI _ hξI ξ.2) r hrle)
    have hARb : ∀ j, ‖T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu))‖ ≤ DR j * MR :=
      fun j => hDR j s hs z uu r hrle hz1 (fun i => (hufc.1 i).1) ξ
    have hACb : ∀ j, ‖T1AC F n abm τc θc a j s (T1frq F ξ (z * uu))‖ ≤ DC j * MC :=
      fun j => hDC j s hs z uu r hrle hz1 (fun w => (hufc.2 w).1) ξ
    have hKcb : ‖T1Kc F ψ a u (T1frq F ξ (z * uu))‖ ≤ K0 := hK0 _
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
        * T1AC F n abm τc θc a j s (T1frq F ξ (z * uu)) * T1Fi F n Φ a j s (T1frq F ξ (z * uu))‖
        ≤ (|BC j| * K0 * DR j * DC j * cF * cabs) * (PR * PC * MX) := by
      intro j
      rw [norm_mul, norm_mul, norm_mul, norm_mul]
      have n1 : 0 ≤ |BC j| * K0 := mul_nonneg (abs_nonneg _) hK00
      have n2 : 0 ≤ |BC j| * K0 * (DR j * MR) := mul_nonneg n1 (mul_nonneg (hDR0 j) hMR0)
      have n3 : 0 ≤ |BC j| * K0 * (DR j * MR) * (DC j * MC) := mul_nonneg n2 (mul_nonneg (hDC0 j) hMC0)
      have n4 : 0 ≤ |BC j| * K0 * DR j * DC j * cF :=
        mul_nonneg (mul_nonneg (mul_nonneg n1 (hDR0 j)) (hDC0 j)) hcF0
      have h1 := mul_le_mul (hCb j) hKcb (norm_nonneg _) (abs_nonneg _)
      have h2 := mul_le_mul h1 (hARb j) (norm_nonneg _) n1
      have h3 := mul_le_mul h2 (hACb j) (norm_nonneg _) n2
      have h4 := mul_le_mul h3 (hFib j) (norm_nonneg _) n3
      refine h4.trans ?_
      have hre : |BC j| * K0 * (DR j * MR) * (DC j * MC) * (cF * MX)
          = (|BC j| * K0 * DR j * DC j * cF) * (MR * MC) * MX := by ring
      rw [hre]
      calc (|BC j| * K0 * DR j * DC j * cF) * (MR * MC) * MX
          ≤ (|BC j| * K0 * DR j * DC j * cF) * (cabs * PR * PC) * MX :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habsorb n4) hMX0
        _ = (|BC j| * K0 * DR j * DC j * cF * cabs) * (PR * PC * MX) := by ring

    have hJ : T1J F α hα ν ψ n C kdat τr abm τc θr θc a u Φ ξ s (z * uu)
        = ((ν (z * uu) : ℂˣ) : ℂ) * ((cpowChar α hα (1 / 2 - s) (z * uu) : ℂˣ) : ℂ)
          * ∑ j : Fin n, C j s * T1Kc F ψ a u (T1frq F ξ (z * uu))
          * T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu)) * T1AC F n abm τc θc a j s (T1frq F ξ (z * uu))
          * T1Fi F n Φ a j s (T1frq F ξ (z * uu)) := rfl
    rw [hJ, norm_mul, norm_mul, hν (z * uu), one_mul]
    have hsum : ‖∑ j : Fin n, C j s * T1Kc F ψ a u (T1frq F ξ (z * uu))
          * T1AR F n kdat τr θr a j s (T1frq F ξ (z * uu)) * T1AC F n abm τc θc a j s (T1frq F ξ (z * uu))
          * T1Fi F n Φ a j s (T1frq F ξ (z * uu))‖
        ≤ ∑ j : Fin n, (|BC j| * K0 * DR j * DC j * cF * cabs) * (PR * PC * MX) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    have hsum0 : 0 ≤ ∑ j : Fin n, (|BC j| * K0 * DR j * DC j * cF * cabs) * (PR * PC * MX) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (abs_nonneg _) hK00) (hDR0 j)) (hDC0 j)) hcF0) hcabs0.le) (mul_nonneg (mul_nonneg hPR0 hPC0) hMX0)
    refine (mul_le_mul hcpb hsum (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg hr.le _) (abs_nonneg _))).trans
      (le_of_eq ?_)
    rw [← Finset.sum_mul, hc]
    ring

private theorem T1J_principal (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
    (hαp : ∀ (t : ℂ) (η : Fˣ), cpowChar α hα t (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η) = 1)
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hνF : IsIdeleClassChar (𝓞 F) F ν)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (n : ℕ) (C : Fin n → ℂ → ℂ)
    (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ) (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
    (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ)
    (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ) :
    T1J F α hα ν ψ n C kdat τr abm τc θr θc a u Φ ξ s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
      = T1J F α hα ν ψ n C kdat τr abm τc θr θc a u Φ ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y := by
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
          φ s k = φ s' k)
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    ∃ 𝒥 : {ξ : F // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ,
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ),
        AnalyticOnNhd ℂ (fun s => 𝒥 ξ s y) Set.univ) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)),
        ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ), 1 < s.re →
          whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) (diagOne y)
            = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                  * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * 𝒥 ξ s y) ∧
      (∀ ξ : {ξ : F // ξ ≠ 0}, Continuous (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => 𝒥 ξ p.1 p.2)) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ),
        𝒥 ξ s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
          = 𝒥 ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y) ∧
      (∀ (C : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ) (r₀ : ℝ), IsCompact C → IsCompact U → 0 < r₀ →
        ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), ∀ N : ℕ, ∃ c : ℝ,
          ∀ s ∈ C, ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), r₀ ≤ r →
            (z : AdeleRing (𝓞 F) F).2 = 1 →
            (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
            ∀ ξ : {ξ : F // ξ ≠ 0},
              ((ξ : F) ∉ I → 𝒥 ξ s (z * u) = 0) ∧
              ‖𝒥 ξ s (z * u)‖ ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
                (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                ∏ w : {w : InfinitePlace F // w.IsComplex},
                  (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ))) := by
  intro α hα μ ν hμ hν hμF hνF ψ hψ φ hφ hφK hφf hφjc hφhol hφflat ϖ hϖ E
  classical
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F

  by_cases hne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0
  swap
  · push Not at hne
    refine ⟨fun _ _ _ => 0, fun _ _ => analyticOnNhd_const, ⟨∅, ?_⟩, fun _ => continuous_const,
      fun _ _ _ _ => rfl, ?_⟩
    · intro ξ s y _
      have hE : E s = fun _ => (0 : ℂ) := by
        funext g
        simp only [E, hne, tsum_zero, add_zero]
      rw [hE, whittakerCoefficient_zero, mul_zero]
    · intro C U r₀ _ _ _
      refine ⟨0, 1, fun N => ⟨0, fun s _ u _ z r _ _ _ ξ => ⟨fun _ => rfl, ?_⟩⟩⟩
      simp only [norm_zero, zero_mul, le_refl]

  obtain ⟨ψv, nψ, θr, θc, hψv, hψv', hnψfin, hψfin, hθr, hθc, hψarch⟩ :=
    AutomorphicForm.exists_localComponents_of_isGlobalAddChar F ψ hψ
  have hψarch' : ∀ p : mixedEmbedding.mixedSpace F,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
            Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
            Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)) := by
    intro p
    rw [hψarch p, finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]
  obtain ⟨S, n, C, kdat, τr, abm, τc, a, u, thr, Φ, hC, habm, hthr, hΦd, hΦ1, hΦ0, hΦb, hΦlc, hform⟩ :=
    AutomorphicForm.whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family_of_unitary F hα μ ν hμ hν hμF hνF ψ hψ ψv nψ hnψfin hψv hψv'
      hψfin θr hθr θc hθc hψarch' ϖ hϖ φ hφ hφK hφf hφjc hφhol hφflat hne
  obtain ⟨-, hνc⟩ := T1U_continuous_chars_of_isInducedSection F α hα
    (NumberField.TateGlobal.continuous_ideleNorm F) μ ν φ hφ hφjc hne
  have hαc : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => (((α y : ℝˣ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F)
  set zE : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ :=
    fun v => ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ) with hzdef
  refine ⟨T1J F α hα ν ψ n C kdat τr abm τc θr θc a u Φ, ?_, ⟨S, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro ξ y
    exact T1J_analyticOnNhd α hα ν ψ S n C kdat τr abm τc θr hθr θc hθc a u Φ hC habm hΦd hΦ1 ξ y
  ·
    intro ξ s y hs
    have hJo : whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) (diagOne y)
        = T1Jo F α hα ν ψ S zE n C kdat τr abm τc θr θc a u Φ ξ s y := by
      rw [hform s hs ξ.1 ξ.2 y]
      simp only [T1Jo, T1Kc, T1ARo, T1ACo, T1Eu, T1Fi, T1frq, T1jR, T1jC]
      rfl
    have hs0 : 0 < s.re := by linarith
    have hARe : ∀ j, T1ARo F n kdat τr θr a j s (T1frq F ξ y) = T1AR F n kdat τr θr a j s (T1frq F ξ y) := by
      intro j
      simp only [T1ARo, T1AR]
      refine Finset.prod_congr rfl fun i _ => ?_
      obtain ⟨-, hR2, -, -⟩ := T1JR_spec (kdat j i)
      refine (hR2 _ _ ?_ (T1frq_freqR_ne_zero θr hθr a ξ y i)).symm
      have h1 : (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2).re = s.re + 1 / 2 := by
        norm_num [Complex.mul_re]
      rw [h1]
      linarith
    have hACe : ∀ j, T1ACo F n abm τc θc a j s (T1frq F ξ y) = T1AC F n abm τc θc a j s (T1frq F ξ y) := by
      intro j
      simp only [T1ACo, T1AC]
      refine Finset.prod_congr rfl fun w _ => ?_
      obtain ⟨-, hC2, -, -⟩ := T1JC_spec (abm j w).1 (abm j w).2.1
      refine (hC2 _ _ ?_ (T1frq_freqC_ne_zero θc hθc a ξ y w)).symm
      have h1 : (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2).re
          = 2 * s.re + 1 + ((abm j w).2.2 : ℝ) / 2 := by
        norm_num [Complex.mul_re]
      have h2 : (((abm j w).1 + (abm j w).2.1 : ℕ) : ℝ) ≤ ((abm j w).2.2 : ℝ) := by exact_mod_cast habm j w
      rw [h1]
      linarith
    rw [hJo]
    have key : ∀ (P ny cp : ℂ) (f g : Fin n → ℂ), (∀ j, f j = g j * P) →
        ny * cp * ∑ j, f j = P * (ny * cp * ∑ j, g j) := by
      intro P ny cp f g h
      simp only [h, ← Finset.sum_mul]
      ring
    simp only [T1Jo, T1J, T1Eu, hARe, hACe]
    exact key _ _ _ _ _ fun j => by ring
  ·
    intro ξ
    have h := T1J_continuousOn α hα hαc ν hνc ψ hψ S n C kdat τr abm τc θr hθr θc hθc a u thr Φ hC habm hΦd hΦ1
      hΦlc ξ
    rw [Set.univ_prod_univ, continuousOn_univ] at h
    exact h
  ·
    intro ξ η s y
    exact T1J_principal α hα (T1Helpers.cpowChar_modulus_principal F hα) ν hνF ψ n C kdat τr abm τc θr θc a u Φ
      ξ η s y
  ·
    intro C₀ U r₀ hC₀ hU hr₀
    have hαz := fun (s : ℂ) (z uu : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ) (hr : 0 < r)
        (hz2 : (z : AdeleRing (𝓞 F) F).2 = 1)
        (hz1 : ∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) =>
      T1Helpers.norm_cpowChar_dilation_mul F z uu r hr hz2 hz1 s hα
    have hαc' : Continuous fun y : (AdeleRing (𝓞 F) F)ˣ => ((α y : ℝˣ) : ℝ) :=
      NumberField.TateGlobal.continuous_ideleNorm F
    exact T1J_bound α hα ν hν hαz hαc' ψ hψ S n C kdat τr abm τc θr hθr θc hθc a u thr Φ hC habm hthr hΦ1 hΦ0 hΦb
      C₀ U r₀ hC₀ hU hr₀

end T1Main

end S_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary
end P2MW
export P2MW.S_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary (solution)
