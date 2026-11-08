-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSSquareRootMachine
-- name    : QEC_Coding_ExpanderCodes_LPSSquareRootMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:54:15.301972+00:00
-- url     : https://prove2.me/theorems/66b254f1-c20c-4abc-bf9a-133745bc7bf9
-- title:
--   LPSSquare Root Machine
-- statement:
--   Definitions and structural lemmas for LPSSquare Root Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSquareRootMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootInput
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_q_le_two_mul_card_psl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiLambertTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalNeighbor_horizontalNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLaurentEvalOne_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_C_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiPowerSeriesEvalOne_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_blockLength_eq_card
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_incidence_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_mem_variableSupport_iff_mem_region
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheck_globalOperator_eq_extendLocalToRegister
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.firstRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_firstZeroExtension
attribute [local simp] QEC.Coding.LiftedProduct.secondRestriction_secondZeroExtension
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.horizontalNeighbor_horizontalNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiLaurentEvalOne_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_C_T
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiPowerSeriesEvalOne_X
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsEffectiveResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_conj
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.blockLength_eq_card
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.incidence_iff_mem_region
attribute [local simp] QEC.QLDPC.FiniteQuditCheckPresentation.mem_variableSupport_iff_mem_region
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open Turing StateTransition
variable {p : ℕ}
theorem lpsDegree_target_lt (a : LPSResiduePrime p) : p<a.q := by
  have := a.large
  omega
theorem lpsDegree_numericRoot_exists (a : LPSResiduePrime p) :
    ∃ n, n<a.q ∧ (n*n)%a.q=p := by
  obtain ⟨n,hn,hs⟩ := exists_lpsDegreeRootCandidate a
  refine ⟨n,hn,?_⟩
  apply (ModularTrial.product_eq_iff n n p a.q a.prime.pos (lpsDegree_target_lt a)).mpr
  simpa only [pow_two] using hs
theorem lpsDegree_numericRoot_index (a : LPSResiduePrime p) :
    SquareRoot.index p a.q (lpsDegree_numericRoot_exists a)=lpsEffectiveDegreeRootIndex a := by
  unfold SquareRoot.index lpsEffectiveDegreeRootIndex
  apply Nat.find_congr'
  intro n
  constructor
  · intro ⟨hn,hs⟩
    refine ⟨hn,?_⟩
    simpa only [pow_two] using
      (ModularTrial.product_eq_iff n n p a.q a.prime.pos (lpsDegree_target_lt a)).mp hs
  · intro ⟨hn,hs⟩
    refine ⟨hn,?_⟩
    apply (ModularTrial.product_eq_iff n n p a.q a.prime.pos (lpsDegree_target_lt a)).mpr
    simpa only [pow_two] using hs
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct.LPSDegreeRootMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct
open Turing StateTransition
def machine (p : ℕ) : Machine := Composition.machine (SquareRootInput.machine p) SquareRoot.machine
noncomputable def size (p : ℕ) : Polynomial ℕ := Polynomial.X+Polynomial.C (p+3)
noncomputable def time (p : ℕ) : Polynomial ℕ :=
  SquareRoot.time.comp (size p)+Polynomial.C 2*size p+Polynomial.X+Polynomial.C 3
noncomputable def polyExec {p : ℕ} (a : LPSResiduePrime p) :
    EvalsToInTime (TM2.step (machine p).program) ((machine p).init (unary a.q))
      (some ((machine p).halt (unary (lpsEffectiveDegreeRootIndex a))))
      ((time p).eval (unary a.q).length) := by
  have hB := SquareRoot.polyExec p a.q a.prime.pos (lpsDegree_numericRoot_exists a)
  rw [lpsDegree_numericRoot_index] at hB
  have h := Composition.executes (SquareRootInput.machine p) SquareRoot.machine
    _ _ _ _ _ (SquareRootInput.exec p a.q) hB
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simp only [SquareRootAdvance.record_length,unary_length,time,size,Polynomial.eval_add,
    Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  have he : p+2*0+a.q+3=a.q+(p+3) := by omega
  rw [he]
  omega
noncomputable def outputsInTime {p : ℕ} (a : LPSResiduePrime p) :
    TM2OutputsInTime (machine p).toFinTM2 (unary a.q)
      (some (unary (lpsEffectiveDegreeRootIndex a))) ((time p).eval (unary a.q).length) :=
  Machine.outputsInTime (machine p) _ _ _ (polyExec a)
noncomputable def computableInPolyTime (p : ℕ) :
    TM2ComputableInPolyTime (fun a:LPSResiduePrime p => unary a.q) unary lpsEffectiveDegreeRootIndex where
  tm := (machine p).toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time p
  outputsFun := fun a => by
    change TM2OutputsInTime (machine p).toFinTM2 (List.map id (unary a.q))
      (some (List.map id (unary (lpsEffectiveDegreeRootIndex a)))) ((time p).eval (unary a.q).length)
    have h := outputsInTime a
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
open scoped MatrixGroups
noncomputable def blockExec {p : ℕ} (a : LPSResiduePrime p) :
    EvalsToInTime (TM2.step (machine p).program) ((machine p).init (unary a.q))
      (some ((machine p).halt (unary (lpsEffectiveDegreeRootIndex a))))
      ((time p).eval (2*Fintype.card PSL(2,ZMod a.q))) := by
  have h := polyExec a
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  rw [unary_length]
  exact Composition.polynomial_eval_monotone (time p) a.q_le_two_mul_card_psl
noncomputable def blockOutputsInTime {p : ℕ} (a : LPSResiduePrime p) :
    TM2OutputsInTime (machine p).toFinTM2 (unary a.q) (some (unary (lpsEffectiveDegreeRootIndex a)))
      ((time p).eval (2*Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime (machine p) _ _ _ (blockExec a)
end QEC.Coding.TannerLiftedProduct.LPSDegreeRootMachine
namespace QEC.Coding.TannerLiftedProduct
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
variable {p : ℕ}
theorem lpsMinusRoot_natCast (a : LPSResiduePrime p) :
    ((a.q-1:ℕ):ZMod a.q)=(-1:ZMod a.q) := by
  let : NeZero a.q := ⟨a.prime.ne_zero⟩
  rw [Nat.cast_sub (by have := a.prime.pos;omega)]
  simp
theorem lpsMinusRoot_numeric_exists (a : LPSResiduePrime p) :
    ∃ n, n<a.q ∧ (n*n)%a.q=a.q-1 := by
  let : NeZero a.q := ⟨a.prime.ne_zero⟩
  have hsq : IsSquare (-1:ZMod a.q) :=
    ZMod.exists_sq_eq_neg_one_iff.mpr (by have := a.modFour;omega)
  obtain ⟨t,ht⟩ := hsq
  refine ⟨t.val,ZMod.val_lt t,?_⟩
  apply (ModularTrial.product_eq_iff t.val t.val (a.q-1) a.q a.prime.pos (by have := a.prime.pos;omega)).mpr
  rw [ZMod.natCast_zmod_val,lpsMinusRoot_natCast]
  exact ht.symm
theorem lpsMinusRoot_pair_index (a : LPSResiduePrime p) :
    SquareRoot.index (a.q-1) a.q (lpsMinusRoot_numeric_exists a)=
      lpsEffectiveResiduePairIndex a.q := by
  let : NeZero a.q := ⟨a.prime.ne_zero⟩
  let j := SquareRoot.index (a.q-1) a.q (lpsMinusRoot_numeric_exists a)
  have hj := SquareRoot.index_lt (a.q-1) a.q (lpsMinusRoot_numeric_exists a)
  have hjsq : (j:ZMod a.q)^2=(-1:ZMod a.q) := by
    rw [←lpsMinusRoot_natCast a]
    have hmod := SquareRoot.index_residue (a.q-1) a.q (lpsMinusRoot_numeric_exists a)
    simpa only [pow_two] using
      (ModularTrial.product_eq_iff j j (a.q-1) a.q a.prime.pos
        (by have := a.prime.pos;omega)).mp hmod
  have hjCandidate : lpsResiduePairCandidate a.q j := by
    refine ⟨?_,?_⟩
    · have := a.prime.two_le
      dsimp only [j]
      nlinarith
    · rw [Nat.div_eq_of_lt hj,Nat.mod_eq_of_lt hj]
      simp only [Nat.cast_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add]
      change (j:ZMod a.q)^2+1=0
      simp [hjsq]
  have hpj : lpsEffectiveResiduePairIndex a.q≤j := Nat.find_min' (exists_lpsResiduePairCandidate a.q) hjCandidate
  have hpLt : lpsEffectiveResiduePairIndex a.q<a.q := hpj.trans_lt hj
  apply Nat.le_antisymm ?_ hpj
  apply Nat.find_min'
  refine ⟨hpLt,?_⟩
  have hs := (Nat.find_spec (exists_lpsResiduePairCandidate a.q)).2
  change ((lpsEffectiveResiduePairIndex a.q/a.q:ℕ):ZMod a.q)^2+
    ((lpsEffectiveResiduePairIndex a.q%a.q:ℕ):ZMod a.q)^2+1=0 at hs
  rw [Nat.div_eq_of_lt hpLt,Nat.mod_eq_of_lt hpLt] at hs
  have hz : (lpsEffectiveResiduePairIndex a.q:ZMod a.q)^2=((a.q-1:ℕ):ZMod a.q) := by
    rw [lpsMinusRoot_natCast]
    norm_num only [Nat.cast_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add] at hs
    linear_combination hs
  apply (ModularTrial.product_eq_iff _ _ (a.q-1) a.q a.prime.pos
    (by have := a.prime.pos;omega)).mpr
  simpa only [pow_two] using hz
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct.LPSResidueRootMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct
open Turing StateTransition
def machine : Machine := Composition.machine (RetainedInput.machine MinusSquareRootInput.machine)
  SquareRoot.machine
noncomputable def size : Polynomial ℕ := Polynomial.C 2*Polynomial.X+Polynomial.C 3
noncomputable def time : Polynomial ℕ :=
  SquareRoot.time.comp size+Polynomial.C 2*size+Polynomial.C 6*Polynomial.X+Polynomial.C 13
noncomputable def polyExec {p : ℕ} (a : LPSResiduePrime p) :
    EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
      (some (machine.halt (unary (lpsEffectiveResiduePairIndex a.q))))
      (time.eval (unary a.q).length) := by
  have hB := SquareRoot.polyExec (a.q-1) a.q a.prime.pos (lpsMinusRoot_numeric_exists a)
  rw [lpsMinusRoot_pair_index] at hB
  have h := Composition.executes (RetainedInput.machine MinusSquareRootInput.machine) SquareRoot.machine
    _ _ _ _ _ (MinusSquareRootInput.retainedExec a.q a.prime.pos) hB
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hL : (SquareRootAdvance.record (a.q-1) 0 a.q).length≤2*a.q+3 := by
    rw [SquareRootAdvance.record_length]
    omega
  have hp := Composition.polynomial_eval_monotone SquareRoot.time hL
  change SquareRoot.time.eval (SquareRootAdvance.record (a.q-1) 0 a.q).length≤
    SquareRoot.time.eval (2*a.q+3) at hp
  simp only [time,size,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,unary_length]
  omega
noncomputable def outputsInTime {p : ℕ} (a : LPSResiduePrime p) :
    TM2OutputsInTime machine.toFinTM2 (unary a.q)
      (some (unary (lpsEffectiveResiduePairIndex a.q))) (time.eval (unary a.q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec a)
noncomputable def computableInPolyTime (p : ℕ) :
    TM2ComputableInPolyTime (fun a:LPSResiduePrime p => unary a.q) unary
      (fun a => lpsEffectiveResiduePairIndex a.q) where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun a => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (unary a.q))
      (some (List.map id (unary (lpsEffectiveResiduePairIndex a.q)))) (time.eval (unary a.q).length)
    have h := outputsInTime a
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
open scoped MatrixGroups
noncomputable def blockExec {p : ℕ} (a : LPSResiduePrime p) :
    EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
      (some (machine.halt (unary (lpsEffectiveResiduePairIndex a.q))))
      (time.eval (2*Fintype.card PSL(2,ZMod a.q))) := by
  have h := polyExec a
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  rw [unary_length]
  exact Composition.polynomial_eval_monotone time a.q_le_two_mul_card_psl
noncomputable def blockOutputsInTime {p : ℕ} (a : LPSResiduePrime p) :
    TM2OutputsInTime machine.toFinTM2 (unary a.q) (some (unary (lpsEffectiveResiduePairIndex a.q)))
      (time.eval (2*Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime machine _ _ _ (blockExec a)
end QEC.Coding.TannerLiftedProduct.LPSResidueRootMachine


