-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLEqualityMachine
-- name    : QEC_Coding_ExpanderCodes_LPSPSLEqualityMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:00:00.14024+00:00
-- url     : https://prove2.me/theorems/ea956d13-dc01-4685-868b-a9afafcc308a
-- title:
--   LPSPSLEquality Machine
-- statement:
--   Definitions and structural lemmas for LPSPSLEquality Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPSLEqualityMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryPSLComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
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
namespace QEC.Coding.TannerLiftedProduct.LPSPSLEqualityMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic
open QEC.Coding.TannerLiftedProduct Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_54787d7fc4_22 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
def input (q:ℕ) (A B:SL(2,ZMod q)) : List Bool :=
  stream (LPSMatrixProductMachine.fields q A.val++LPSMatrixProductMachine.fields q B.val++[q])
def output (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) : List Bool :=
  letI:=lpsPSLDecidableEq q
  [decide ((QuotientGroup.mk A:PSL(2,ZMod q))=QuotientGroup.mk B)]
theorem entries_eq (q:ℕ) (A B:SL(2,ZMod q)) :
    A=B ↔ A.val 0 0=B.val 0 0 ∧ A.val 0 1=B.val 0 1 ∧
      A.val 1 0=B.val 1 0 ∧ A.val 1 1=B.val 1 1 :=by
  constructor
  · rintro rfl;simp
  · rintro ⟨h00,h01,h10,h11⟩
    apply Subtype.ext
    ext i j;fin_cases i <;> fin_cases j <;> assumption
theorem result_eq_source (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) :
    [QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.result (A.val 0 0).val (A.val 0 1).val (A.val 1 0).val (A.val 1 1).val
      (B.val 0 0).val (B.val 0 1).val (B.val 1 0).val (B.val 1 1).val q]=output q A B :=by
  let : NeZero q:=⟨(Fact.out:q.Prime).ne_zero⟩
  let :=lpsPSLDecidableEq q
  have hn (z:ZMod q):ModularNegation.output z.val q=(-z).val :=by
    rw [ModularNegation.output_eq_neg _ _ (Fact.out:q.Prime).pos (ZMod.val_lt _),ZMod.natCast_zmod_val]
  simp only [QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.result,hn,Function.Injective.eq_iff (ZMod.val_injective q),
    ←Bool.decide_and,←Bool.decide_or,output]
  simp only [List.cons.injEq, and_true]
  apply Bool.decide_congr
  rw [lpsPSLMk_eq_iff,entries_eq q A B,entries_eq q (-A) B]
  simp [and_comm,or_comm]
noncomputable def exec (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) :
    EvalsToInTime (TM2.step QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.program)
      (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.init (input q A B))
      (some (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.halt (output q A B)))
      (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time.eval (input q A B).length) :=by
  let : NeZero q:=⟨(Fact.out:q.Prime).ne_zero⟩
  have h:=QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.polyExec (A.val 0 0).val (A.val 0 1).val (A.val 1 0).val (A.val 1 1).val
    (B.val 0 0).val (B.val 0 1).val (B.val 1 0).val (B.val 1 1).val q
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
  rw [result_eq_source q A B] at h
  simpa only [input,LPSMatrixProductMachine.fields,List.cons_append,List.nil_append] using h
noncomputable def outputsInTime (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) :
    TM2OutputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.toFinTM2 (input q A B)
      (some (output q A B)) (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time.eval (input q A B).length) :=
  Machine.outputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine _ _ _ (exec q A B)
noncomputable def computableInPolyTime (q:ℕ) [Fact q.Prime] :
    TM2ComputableInPolyTime (fun x:SL(2,ZMod q)×SL(2,ZMod q)=>input q x.1 x.2)
      id (fun x=>output q x.1 x.2) where
  tm:=QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time
  outputsFun:=fun x=>by
    change TM2OutputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.toFinTM2
      (List.map id (input q x.1 x.2)) (some (List.map id (output q x.1 x.2)))
      (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time.eval (input q x.1 x.2).length)
    have h:=outputsInTime q x.1 x.2
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
noncomputable def carrierTime : Polynomial ℕ := QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time.comp
  (Polynomial.C 18*Polynomial.X+Polynomial.C 9)
noncomputable def carrierExec {p:ℕ} (a:LPSResiduePrime p) (A B:SL(2,ZMod a.q)) :
    EvalsToInTime (TM2.step QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.program)
      (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.init (input a.q A B))
      (some (QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.halt (output a.q A B)))
      (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))) :=by
  have h:=exec a.q A B
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  let : NeZero a.q:=⟨a.prime.pos.ne'⟩
  have hbound:(input a.q A B).length≤18*Fintype.card PSL(2,ZMod a.q)+9 :=by
    have hq:=a.q_le_two_mul_card_psl
    have h00:=ZMod.val_lt (A.val 0 0)
    have h01:=ZMod.val_lt (A.val 0 1)
    have h10:=ZMod.val_lt (A.val 1 0)
    have h11:=ZMod.val_lt (A.val 1 1)
    have h20:=ZMod.val_lt (B.val 0 0)
    have h21:=ZMod.val_lt (B.val 0 1)
    have h30:=ZMod.val_lt (B.val 1 0)
    have h31:=ZMod.val_lt (B.val 1 1)
    simp only [input,LPSMatrixProductMachine.fields,List.cons_append,List.nil_append,
      stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  simp only [carrierTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  exact Composition.polynomial_eval_monotone QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.time hbound
noncomputable def carrierOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (A B:SL(2,ZMod a.q)) :
    TM2OutputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine.toFinTM2 (input a.q A B)
      (some (output a.q A B)) (carrierTime.eval (Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime QEC.Coding.BitTuring.UnaryArithmetic.PSLComparison.predicateMachine _ _ _ (carrierExec a A B)
end QEC.Coding.TannerLiftedProduct.LPSPSLEqualityMachine


