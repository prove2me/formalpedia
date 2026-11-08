-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterRowMachine
-- name    : QEC_Coding_ExpanderCodes_LPSSparseEmitterRowMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:04:56.948606+00:00
-- url     : https://prove2.me/theorems/b79263d2-3c9a-4f22-8a3d-b2152bc2a1e8
-- title:
--   LPSSparse Emitter Row Machine
-- statement:
--   Definitions and structural lemmas for LPSSparse Emitter Row Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterRowMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_UnarySparseEmitterArithmetic
import Definitions.Def_QEC_Coding_BitTuring_SuffixJoin
import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLGroupOperationsMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SparseEmitterRowCount_rowCount_four
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSPSLSearchMachine_mapped_original_representatives
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
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
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCardinality
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open LPSPSLSearchMachine
open scoped MatrixGroups
local instance _p2m_local_instance_8f991ae56e_26:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
abbrev Input:=LPSOriginalPSLListMachine.Input
instance (a:Input):Fact a.val.Prime:=⟨a.property⟩
def fields (a:Input):List ℕ:=(representatives a.val (lpsSLList a.val)).flatMap (coords a.val)
def output (a:Input):List Bool:=unary (lpsPSLList a.val).length
theorem count_rows (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)) (w:List Bool):
 SparseEmitterRowCount.rowCount 0 (stream (R.flatMap (coords q))++w)=R.length+SparseEmitterRowCount.rowCount 0 w:=by
 induction R with
 | nil=>simp [stream]
 | cons A R ih=>
  rw [List.flatMap_cons,MatrixListQuery.stream_append,List.append_assoc]
  change SparseEmitterRowCount.rowCount 0
   (stream [(A.val 0 0).val,(A.val 0 1).val,(A.val 1 0).val,(A.val 1 1).val]++(stream (R.flatMap (coords q))++w))=_
  rw [SparseEmitterRowCount.rowCount_four,ih]
  simp only [List.length_cons]
  omega
theorem fields_length (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)):
 (R.flatMap (coords q)).length=4*R.length:=by
 induction R with
 | nil=>simp
 | cons A R ih=>
  simp only [List.flatMap_cons,List.length_append,coords,LPSMatrixProductMachine.fields,List.length_cons,List.length_nil]
  rw [ih]
  omega
theorem source_length (a:Input):(representatives a.val (lpsSLList a.val)).length=(lpsPSLList a.val).length:=by
 simpa only [List.length_map] using congrArg List.length (mapped_original_representatives a.val)
theorem fields_nonempty (a:Input):fields a≠[]:=by
 intro h
 have hlen:=fields_length a.val (representatives a.val (lpsSLList a.val))
 change (fields a).length=4*(representatives a.val (lpsSLList a.val)).length at hlen
 rw [h,List.length_nil,source_length] at hlen
 have hpos:0<(lpsPSLList a.val).length:=Nat.zero_lt_of_lt (lpsPSLIndexOne a.val).isLt
 omega
theorem count_source (a:Input):SparseEmitterRowCount.rowCount 0 (stream (fields a))=(lpsPSLList a.val).length:=by
 have h:=count_rows a.val (representatives a.val (lpsSLList a.val)) []
 simpa only [List.append_nil,SparseEmitterRowCount.rowCount,Nat.add_zero,source_length,fields] using h
def marked:=Composition.machine LPSOriginalPSLListMachine.machine BitDelimiter.machine
noncomputable def markedTime:Polynomial ℕ:=Composition.timePolynomial LPSOriginalPSLListMachine.machine LPSOriginalPSLListMachine.time
 (Polynomial.C 2*Polynomial.X+Polynomial.C 3)
noncomputable def markedExec (a:Input):EvalsToInTime (TM2.step marked.program) (marked.init (unary a.val))
 (some (marked.halt (stream (fields a)))) (markedTime.eval (unary a.val).length):=by
 have h:=BitDelimiter.exec (LPSOriginalPSLListMachine.output a.val)
 have he:LPSOriginalPSLListMachine.output a.val++[false]=stream (fields a):=
  MatrixListQuery.delimiter_raw _ (fields_nonempty a)
 rw [he] at h
 exact RetainedFieldComputation.composeRuns LPSOriginalPSLListMachine.machine BitDelimiter.machine _ _ _
  LPSOriginalPSLListMachine.time (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (LPSOriginalPSLListMachine.exec a)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using h)
def machine:=Composition.machine marked SparseEmitterRowCount.machine
noncomputable def time:Polynomial ℕ:=Composition.timePolynomial marked markedTime SparseEmitterRowCount.time
noncomputable def exec (a:Input):EvalsToInTime (TM2.step machine.program) (machine.init (unary a.val))
 (some (machine.halt (output a))) (time.eval (unary a.val).length):=by
 have h:=SparseEmitterRowCount.exec (stream (fields a))
 rw [count_source] at h
 have hb:EvalsToInTime (TM2.step SparseEmitterRowCount.machine.program) (SparseEmitterRowCount.machine.init (stream (fields a)))
  (some (SparseEmitterRowCount.machine.halt (output a))) (SparseEmitterRowCount.time.eval (stream (fields a)).length):=by
  simpa only [SparseEmitterRowCount.time,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,output] using h
 exact RetainedFieldComputation.composeRuns marked SparseEmitterRowCount.machine _ _ _ markedTime SparseEmitterRowCount.time (markedExec a) hb
noncomputable def outputsInTime (a:Input):TM2OutputsInTime machine.toFinTM2 (unary a.val) (some (output a)) (time.eval (unary a.val).length):=
 Machine.outputsInTime machine _ _ _ (exec a)
noncomputable def computableInPolyTime:TM2ComputableInPolyTime (fun a:Input=>unary a.val) id output where
 tm:=machine.toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time
 outputsFun:=fun a=>by
  change TM2OutputsInTime machine.toFinTM2 (List.map id (unary a.val)) (some (List.map id (output a))) (time.eval (unary a.val).length)
  have h:=outputsInTime a
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def blockTime:Polynomial ℕ:=time.comp (Polynomial.C 2*Polynomial.X)
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p):EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
 (some (machine.halt (output ⟨a.q,a.prime⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨a.q,a.prime⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p):TM2OutputsInTime machine.toFinTM2 (unary a.q)
 (some (output ⟨a.q,a.prime⟩)) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a)
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterCardinality
namespace QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterSwap
open QEC.Coding.BitTuring Turing StateTransition FieldProjection
local instance _p2m_local_instance_8f991ae56e_110:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def copy:=ModularAdjugate.retainedUnary 2 (ModulusQuery.mask 2)
noncomputable def copyTime:=ModularAdjugate.stageTime
noncomputable def copyExec (a b q:ℕ):
 EvalsToInTime (TM2.step copy.program) (copy.init (stream [a,b,q]))
 (some (copy.halt (stream [q,a,b,q]))) (copyTime.eval (stream [a,b,q]).length):=by
 exact ModularAdjugate.unaryStageExec 2 (ModulusQuery.mask 2) [a,b,q] (by rfl) q
  (MatrixListQuery.selectLast 2 0 [a,b] q (by rfl))
def mask (k:Fin 4):Bool:=decide (k.val<3)
def reversed:=RetainedFieldComputation.projectedReverse 3 mask
noncomputable def reversedTime:=RetainedFieldComputation.projectedReverseTime 3 mask
theorem raw_reverse (a b q:ℕ):(raw [q,a,b]).reverse=raw [b,a,q]:=by
 change (raw ([q,a]++[b])).reverse=raw ([b,a]++[q])
 rw [raw_append_last,raw_append_last]
 simp [stream,List.reverse_append,unary,List.append_assoc]
noncomputable def reversedExec (a b q:ℕ):
 EvalsToInTime (TM2.step reversed.program) (reversed.init (stream [q,a,b,q]))
 (some (reversed.halt (raw [b,a,q]))) (reversedTime.eval (stream [q,a,b,q]).length):=by
 have h:=RetainedFieldComputation.projectedReverseExec 3 mask [q,a,b,q] (by rfl)
 have hf:fields 3 mask 0 [q,a,b,q]=[q,a,b]:=by simp [fields,maskAt,mask]
 rw [hf,raw_reverse] at h
 exact h
def swapRaw:=Composition.machine copy reversed
noncomputable def swapRawTime:=Composition.timePolynomial copy copyTime reversedTime
noncomputable def swapRawExec (a b q:ℕ):
 EvalsToInTime (TM2.step swapRaw.program) (swapRaw.init (stream [a,b,q]))
 (some (swapRaw.halt (raw [b,a,q]))) (swapRawTime.eval (stream [a,b,q]).length):=
 RetainedFieldComputation.composeRuns copy reversed _ _ _ copyTime reversedTime (copyExec a b q) (reversedExec a b q)
def machine:=RetainedFieldComputation.marked swapRaw
noncomputable def time:=RetainedFieldComputation.markedTime swapRaw swapRawTime
noncomputable def exec (a b q:ℕ):
 EvalsToInTime (TM2.step machine.program) (machine.init (stream [a,b,q]))
 (some (machine.halt (stream [b,a,q]))) (time.eval (stream [a,b,q]).length):=
 RetainedFieldComputation.markedExec swapRaw _ [b,a,q] (by simp) swapRawTime (swapRawExec a b q)
end QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterSwap
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_8f991ae56e_149:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
open LPSOriginalGeneratorIndexMachine
abbrev Index {p:ℕ} (a:LPSResiduePrime p):=LPSSparseGroupIndex a.q
def voltage {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):Index a:=
 lpsSparseVoltage (fun k=>result a (g k)) side j
def query {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):=
 RetainedFieldComputation.machine 1 (ModulusQuery.mask 1) (Voltage.entryMachine g side j)
noncomputable def queryTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):=
 RetainedFieldComputation.time 1 (ModulusQuery.mask 1) (Voltage.entryMachine g side j) (Voltage.entryTime g side j)
noncomputable def queryExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (i:Index a):
 EvalsToInTime (TM2.step (query g side j).program) ((query g side j).init (stream [i.val,a.q]))
 (some ((query g side j).halt (stream [(voltage a g side j).val,i.val,a.q])))
 ((queryTime g side j).eval (stream [i.val,a.q]).length):=by
 have hf:fields 1 (ModulusQuery.mask 1) 0 [i.val,a.q]=[a.q]:=by
  simpa only [List.cons_append,List.nil_append] using MatrixListQuery.selectLast 1 0 [i.val] a.q (by rfl)
 have hr (n:ℕ):raw [n]=unary n:=by
  simpa only [stream,List.nil_append] using raw_append_last [] n
 have hb:EvalsToInTime (TM2.step (Voltage.entryMachine g side j).program)
  ((Voltage.entryMachine g side j).init (raw (fields 1 (ModulusQuery.mask 1) 0 [i.val,a.q])))
  (some ((Voltage.entryMachine g side j).halt (raw [(voltage a g side j).val])))
  ((Voltage.entryTime g side j).eval (raw (fields 1 (ModulusQuery.mask 1) 0 [i.val,a.q])).length):=by
  rw [hf,hr,hr]
  exact Voltage.entryExec a g side j
 have h:=RetainedFieldComputation.exec 1 (ModulusQuery.mask 1) (Voltage.entryMachine g side j)
  [i.val,a.q] [(voltage a g side j).val] (by rfl) (by simp) (Voltage.entryTime g side j) hb
 rw [←MatrixListQuery.stream_append] at h
 exact h
def inverseRaw:=Composition.machine BitDelimiter.machine LPSOriginalPSLGroupOperationsMachine.Inverse.machine
noncomputable def delimiterTime:Polynomial ℕ:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
noncomputable def inverseRawTime:=Composition.timePolynomial BitDelimiter.machine delimiterTime LPSOriginalPSLGroupOperationsMachine.Inverse.time
noncomputable def inverseRawExec {q:ℕ} [Fact q.Prime] (hq:q.Prime) (v:LPSSparseGroupIndex q):
 EvalsToInTime (TM2.step inverseRaw.program) (inverseRaw.init (raw [v.val,q]))
 (some (inverseRaw.halt (raw [(lpsPSLIndexInv q v).val]))) (inverseRawTime.eval (raw [v.val,q]).length):=by
 have hd:=BitDelimiter.exec (raw [v.val,q])
 rw [MatrixListQuery.delimiter_raw _ (by simp)] at hd
 have hb:=LPSOriginalPSLGroupOperationsMachine.Inverse.exec ⟨⟨q,hq⟩,v⟩
 dsimp only [LPSOriginalPSLGroupOperationsMachine.Inverse.input] at hb
 have h:=RetainedFieldComputation.composeRuns BitDelimiter.machine LPSOriginalPSLGroupOperationsMachine.Inverse.machine
  _ _ _ delimiterTime LPSOriginalPSLGroupOperationsMachine.Inverse.time
  (by simpa only [delimiterTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using hd) hb
 have hr:raw [(lpsPSLIndexInv q v).val]=unary (lpsPSLIndexInv q v).val:=by
  simpa only [stream,List.nil_append] using raw_append_last [] (lpsPSLIndexInv q v).val
 rw [hr]
 exact h
def inverseMask (k:Fin 3):Bool:=decide (k.val=0∨k.val=2)
def inverseQuery:=RetainedFieldComputation.machine 2 inverseMask inverseRaw
noncomputable def inverseQueryTime:=RetainedFieldComputation.time 2 inverseMask inverseRaw inverseRawTime
noncomputable def inverseQueryExec {q:ℕ} [Fact q.Prime] (v i:LPSSparseGroupIndex q):
 EvalsToInTime (TM2.step inverseQuery.program) (inverseQuery.init (stream [v.val,i.val,q]))
 (some (inverseQuery.halt (stream [(lpsPSLIndexInv q v).val,v.val,i.val,q])))
 (inverseQueryTime.eval (stream [v.val,i.val,q]).length):=by
 have hf:fields 2 inverseMask 0 [v.val,i.val,q]=[v.val,q]:=by simp [fields,maskAt,inverseMask]
 have hb:EvalsToInTime (TM2.step inverseRaw.program) (inverseRaw.init (raw (fields 2 inverseMask 0 [v.val,i.val,q])))
  (some (inverseRaw.halt (raw [(lpsPSLIndexInv q v).val]))) (inverseRawTime.eval (raw (fields 2 inverseMask 0 [v.val,i.val,q])).length):=by
  rw [hf]
  exact inverseRawExec (Fact.out:q.Prime) v
 have h:=RetainedFieldComputation.exec 2 inverseMask inverseRaw [v.val,i.val,q] [(lpsPSLIndexInv q v).val]
  (by rfl) (by simp) inverseRawTime hb
 rw [←MatrixListQuery.stream_append] at h
 exact h
def removeOldMask (k:Fin 4):Bool:=decide (k.val≠1)
def removeOld:=RetainedFieldComputation.projectedMarked 3 removeOldMask
noncomputable def removeOldTime:=RetainedFieldComputation.projectedMarkedTime 3 removeOldMask
noncomputable def removeOldExec (u v i q:ℕ):
 EvalsToInTime (TM2.step removeOld.program) (removeOld.init (stream [u,v,i,q]))
 (some (removeOld.halt (stream [u,i,q]))) (removeOldTime.eval (stream [u,v,i,q]).length):=by
 have hf:fields 3 removeOldMask 0 [u,v,i,q]=[u,i,q]:=by simp [fields,maskAt,removeOldMask]
 have h:=RetainedFieldComputation.projectedMarkedExec 3 removeOldMask [u,v,i,q] (by rfl) (by rw [hf];simp)
 rw [hf] at h
 exact h
def inverted:=Composition.machine inverseQuery removeOld
noncomputable def invertedTime:=Composition.timePolynomial inverseQuery inverseQueryTime removeOldTime
noncomputable def invertedExec {q:ℕ} [Fact q.Prime] (v i:LPSSparseGroupIndex q):
 EvalsToInTime (TM2.step inverted.program) (inverted.init (stream [v.val,i.val,q]))
 (some (inverted.halt (stream [(lpsPSLIndexInv q v).val,i.val,q]))) (invertedTime.eval (stream [v.val,i.val,q]).length):=
 RetainedFieldComputation.composeRuns inverseQuery removeOld _ _ _ inverseQueryTime removeOldTime
  (inverseQueryExec v i) (removeOldExec _ _ _ _)
def applyInv (inv:Bool):=if inv then inverted else MatrixListQuery.identityMachine
noncomputable def applyInvTime (inv:Bool):=if inv then invertedTime else Polynomial.C 4*Polynomial.X+Polynomial.C 4
def transformed {q:ℕ} [Fact q.Prime] (inv:Bool) (v:LPSSparseGroupIndex q):=if inv then lpsPSLIndexInv q v else v
noncomputable def applyInvExec {q:ℕ} [Fact q.Prime] (inv:Bool) (v i:LPSSparseGroupIndex q):
 EvalsToInTime (TM2.step (applyInv inv).program) ((applyInv inv).init (stream [v.val,i.val,q]))
 (some ((applyInv inv).halt (stream [(transformed inv v).val,i.val,q])))
 ((applyInvTime inv).eval (stream [v.val,i.val,q]).length):=by
 cases inv with
 | true=>exact invertedExec v i
 | false=>
  have hm:applyInv false=MatrixListQuery.identityMachine:=rfl
  rw [hm]
  simpa only [applyInvTime,transformed,Bool.false_eq_true,↓reduceIte,
   Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using MatrixListQuery.identityExec (stream [v.val,i.val,q])
def orient (right:Bool):=if right then SparseEmitterSwap.machine else MatrixListQuery.identityMachine
noncomputable def orientTime (right:Bool):=if right then SparseEmitterSwap.time else Polynomial.C 4*Polynomial.X+Polynomial.C 4
def operands (right:Bool) (u i q:ℕ):List ℕ:=if right then [i,u,q] else [u,i,q]
noncomputable def orientExec (right:Bool) (u i q:ℕ):
 EvalsToInTime (TM2.step (orient right).program) ((orient right).init (stream [u,i,q]))
 (some ((orient right).halt (stream (operands right u i q)))) ((orientTime right).eval (stream [u,i,q]).length):=by
 cases right with
 | true=>exact SparseEmitterSwap.exec u i q
 | false=>
  have hm:orient false=MatrixListQuery.identityMachine:=rfl
  rw [hm]
  simpa only [orientTime,operands,Bool.false_eq_true,↓reduceIte,
   Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using MatrixListQuery.identityExec (stream [u,i,q])
def product {q:ℕ} [Fact q.Prime] (inv right:Bool) (v i:LPSSparseGroupIndex q):=
 if right then lpsPSLIndexMul q i (transformed inv v) else lpsPSLIndexMul q (transformed inv v) i
noncomputable def multiplyExec {q:ℕ} [Fact q.Prime] (inv right:Bool) (v i:LPSSparseGroupIndex q):
 EvalsToInTime (TM2.step LPSOriginalPSLGroupOperationsMachine.Multiply.machine.program)
 (LPSOriginalPSLGroupOperationsMachine.Multiply.machine.init (stream (operands right (transformed inv v).val i.val q)))
 (some (LPSOriginalPSLGroupOperationsMachine.Multiply.machine.halt (unary (product inv right v i).val)))
 (LPSOriginalPSLGroupOperationsMachine.Multiply.time.eval (stream (operands right (transformed inv v).val i.val q)).length):=by
 cases right with
 | false=>exact LPSOriginalPSLGroupOperationsMachine.Multiply.exec ⟨⟨q,Fact.out⟩,transformed inv v,i⟩
 | true=>exact LPSOriginalPSLGroupOperationsMachine.Multiply.exec ⟨⟨q,Fact.out⟩,i,transformed inv v⟩
def orientedProduct (right:Bool):=Composition.machine (orient right) LPSOriginalPSLGroupOperationsMachine.Multiply.machine
noncomputable def orientedProductTime (right:Bool):=Composition.timePolynomial (orient right) (orientTime right) LPSOriginalPSLGroupOperationsMachine.Multiply.time
def invProduct (inv right:Bool):=Composition.machine (applyInv inv) (orientedProduct right)
noncomputable def invProductTime (inv right:Bool):=Composition.timePolynomial (applyInv inv) (applyInvTime inv) (orientedProductTime right)
noncomputable def invProductExec {q:ℕ} [Fact q.Prime] (inv right:Bool) (v i:LPSSparseGroupIndex q):
 EvalsToInTime (TM2.step (invProduct inv right).program) ((invProduct inv right).init (stream [v.val,i.val,q]))
 (some ((invProduct inv right).halt (unary (product inv right v i).val)))
 ((invProductTime inv right).eval (stream [v.val,i.val,q]).length):=by
 have h:=RetainedFieldComputation.composeRuns (orient right) LPSOriginalPSLGroupOperationsMachine.Multiply.machine
  _ _ _ (orientTime right) LPSOriginalPSLGroupOperationsMachine.Multiply.time
  (orientExec right (transformed inv v).val i.val q) (multiplyExec inv right v i)
 exact RetainedFieldComputation.composeRuns (applyInv inv) (orientedProduct right) _ _ _ (applyInvTime inv) (orientedProductTime right)
  (applyInvExec inv v i) h
def machine {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool):=
 Composition.machine (query g side j) (invProduct inv right)
noncomputable def time {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool):=
 Composition.timePolynomial (query g side j) (queryTime g side j) (invProductTime inv right)
noncomputable def exec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool) (i:Index a):
 EvalsToInTime (TM2.step (machine g side j inv right).program) ((machine g side j inv right).init (stream [i.val,a.q]))
 (some ((machine g side j inv right).halt (unary (product inv right (voltage a g side j) i).val)))
 ((time g side j inv right).eval (stream [i.val,a.q]).length):=
 RetainedFieldComputation.composeRuns (query g side j) (invProduct inv right) _ _ _ (queryTime g side j) (invProductTime inv right)
  (queryExec a g side j i) (invProductExec inv right (voltage a g side j) i)
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterAction
namespace QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterOffset
open QEC.Coding.BitTuring Turing StateTransition FieldProjection
local instance _p2m_local_instance_8f991ae56e_296:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def multiply (c:ℕ):=Composition.machine (FixedLiteral.prefixMachine (unary c++[false])) multiplicationMachine
noncomputable def multiplyTime (c:ℕ):=Composition.timePolynomial (FixedLiteral.prefixMachine (unary c++[false]))
 (FixedLiteral.prefixTime (unary c++[false])) multiplicationTime
noncomputable def multiplyExec (c N:ℕ):
 EvalsToInTime (TM2.step (multiply c).program) ((multiply c).init (unary N))
 (some ((multiply c).halt (unary (c*N)))) ((multiplyTime c).eval (unary N).length):=by
 have h:=FixedLiteral.prefixExec (unary c++[false]) (unary N)
 have he:(unary c++[false])++unary N=pairInput c N:=by simp only [pairInput,List.append_assoc,List.singleton_append]
 rw [he] at h
 exact RetainedFieldComputation.composeRuns (FixedLiteral.prefixMachine (unary c++[false])) multiplicationMachine _ _ _
  (FixedLiteral.prefixTime (unary c++[false])) multiplicationTime h (multiplicationPolyExec c N)
def productQuery (c:ℕ):=RetainedFieldComputation.machine 1 (ModulusQuery.mask 1) (multiply c)
noncomputable def productQueryTime (c:ℕ):=RetainedFieldComputation.time 1 (ModulusQuery.mask 1) (multiply c) (multiplyTime c)
noncomputable def productQueryExec (c u N:ℕ):
 EvalsToInTime (TM2.step (productQuery c).program) ((productQuery c).init (stream [u,N]))
 (some ((productQuery c).halt (stream [c*N,u,N]))) ((productQueryTime c).eval (stream [u,N]).length):=by
 have hf:fields 1 (ModulusQuery.mask 1) 0 [u,N]=[N]:=by
  simpa only [List.cons_append,List.nil_append] using MatrixListQuery.selectLast 1 0 [u] N (by rfl)
 have hr (n:ℕ):raw [n]=unary n:=by simpa only [stream,List.nil_append] using raw_append_last [] n
 have hb:EvalsToInTime (TM2.step (multiply c).program)
  ((multiply c).init (raw (fields 1 (ModulusQuery.mask 1) 0 [u,N])))
  (some ((multiply c).halt (raw [c*N]))) ((multiplyTime c).eval (raw (fields 1 (ModulusQuery.mask 1) 0 [u,N])).length):=by
  rw [hf,hr,hr]
  exact multiplyExec c N
 have h:=RetainedFieldComputation.exec 1 (ModulusQuery.mask 1) (multiply c) [u,N] [c*N] (by rfl) (by simp) (multiplyTime c) hb
 rw [←MatrixListQuery.stream_append] at h
 exact h
def sumMask:=MatrixListQuery.prefixMask 2
def project:=FieldProjection.machine 2 sumMask
theorem project_fields (v u N:ℕ):fields 2 sumMask 0 [v,u,N]=[v,u]:=by simp [fields,maskAt,sumMask,MatrixListQuery.prefixMask]
noncomputable def projectExec (v u N:ℕ):
 EvalsToInTime (TM2.step project.program) (project.init (stream [v,u,N]))
 (some (project.halt (pairInput v u))) (FieldProjection.time.eval (stream [v,u,N]).length):=by
 have h:=FieldProjection.polyExec 2 sumMask [v,u,N] (by rfl)
 rw [project_fields] at h
 have he:raw [v,u]=pairInput v u:=by
  change raw ([v]++[u])=pairInput v u
  rw [raw_append_last]
  simp only [stream,pairInput,List.append_assoc,List.singleton_append]
 rw [he] at h
 exact h
def add:=Composition.machine project SparseEmitterSum.machine
noncomputable def addTime:=Composition.timePolynomial project FieldProjection.time SparseEmitterSum.time
noncomputable def addExec (v u N:ℕ):
 EvalsToInTime (TM2.step add.program) (add.init (stream [v,u,N]))
 (some (add.halt (unary (v+u)))) (addTime.eval (stream [v,u,N]).length):=
 RetainedFieldComputation.composeRuns project SparseEmitterSum.machine _ _ _ FieldProjection.time SparseEmitterSum.time
  (projectExec v u N) (SparseEmitterSum.additionExec v u)
def machine (c:ℕ):=Composition.machine (productQuery c) add
noncomputable def time (c:ℕ):=Composition.timePolynomial (productQuery c) (productQueryTime c) addTime
noncomputable def exec (c u N:ℕ):
 EvalsToInTime (TM2.step (machine c).program) ((machine c).init (stream [u,N]))
 (some ((machine c).halt (unary (c*N+u)))) ((time c).eval (stream [u,N]).length):=
 RetainedFieldComputation.composeRuns (productQuery c) add _ _ _ (productQueryTime c) addTime (productQueryExec c u N) (addExec _ _ _)
def rawMachine (c:ℕ):=Composition.machine BitDelimiter.machine (machine c)
noncomputable def rawTime (c:ℕ):=Composition.timePolynomial BitDelimiter.machine
 (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (time c)
noncomputable def rawExec (c u N:ℕ):
 EvalsToInTime (TM2.step (rawMachine c).program) ((rawMachine c).init (raw [u,N]))
 (some ((rawMachine c).halt (unary (c*N+u)))) ((rawTime c).eval (raw [u,N]).length):=by
 have hd:=BitDelimiter.exec (raw [u,N])
 rw [MatrixListQuery.delimiter_raw _ (by simp)] at hd
 exact RetainedFieldComputation.composeRuns BitDelimiter.machine (machine c) _ _ _
  (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (time c)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using hd) (exec c u N)
end QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterOffset
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterEntry
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_8f991ae56e_367:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def actionMask (k:Fin 3):Bool:=decide (k.val≠0)
def projected:=PrefixProjection.prefixMachine 2 actionMask
noncomputable def projectedExec (N i q:ℕ) (suffix:List Bool):
 EvalsToInTime (TM2.step projected.program) (projected.init (stream [N,i,q]++suffix))
 (some (projected.halt (raw [i,q]))) (PrefixProjection.time.eval (stream [N,i,q]++suffix).length):=by
 have h:=PrefixProjection.polyExec 2 actionMask [N,i,q] (by rfl) suffix
 have hf:fields 2 actionMask 0 [N,i,q]=[i,q]:=by simp [fields,maskAt,actionMask]
 rw [hf] at h
 exact h
def actionRaw {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool):=
 Composition.machine BitDelimiter.machine (LPSSparseEmitterAction.machine g side j inv right)
noncomputable def actionRawTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool):=
 Composition.timePolynomial BitDelimiter.machine LPSSparseEmitterAction.delimiterTime (LPSSparseEmitterAction.time g side j inv right)
noncomputable def actionRawExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool) (i:LPSSparseGroupIndex a.q):
 EvalsToInTime (TM2.step (actionRaw g side j inv right).program) ((actionRaw g side j inv right).init (raw [i.val,a.q]))
 (some ((actionRaw g side j inv right).halt (unary (LPSSparseEmitterAction.product inv right (LPSSparseEmitterAction.voltage a g side j) i).val)))
 ((actionRawTime g side j inv right).eval (raw [i.val,a.q]).length):=by
 have hd:=BitDelimiter.exec (raw [i.val,a.q])
 rw [MatrixListQuery.delimiter_raw _ (by simp)] at hd
 exact RetainedFieldComputation.composeRuns BitDelimiter.machine (LPSSparseEmitterAction.machine g side j inv right)
  _ _ _ LPSSparseEmitterAction.delimiterTime (LPSSparseEmitterAction.time g side j inv right)
  (by simpa only [LPSSparseEmitterAction.delimiterTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using hd)
  (LPSSparseEmitterAction.exec a g side j inv right i)
def actionBody {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool):=
 Composition.machine projected (actionRaw g side j inv right)
noncomputable def actionBodyTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool):=
 Composition.timePolynomial projected PrefixProjection.time (actionRawTime g side j inv right)
noncomputable def actionBodyExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool)
 (N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (actionBody g side j inv right).program) ((actionBody g side j inv right).init (stream [N,i.val,a.q]++suffix))
 (some ((actionBody g side j inv right).halt (unary (LPSSparseEmitterAction.product inv right (LPSSparseEmitterAction.voltage a g side j) i).val)))
 ((actionBodyTime g side j inv right).eval (stream [N,i.val,a.q]++suffix).length):=
 RetainedFieldComputation.composeRuns projected (actionRaw g side j inv right) _ _ _ PrefixProjection.time (actionRawTime g side j inv right)
  (projectedExec N i.val a.q suffix) (actionRawExec a g side j inv right i)
def query {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool):=
 RetainedFieldComputation.retainedMarked (actionBody g side j inv right)
noncomputable def queryTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool):=
 RetainedFieldComputation.retainedMarkedTime (actionBody g side j inv right) (actionBodyTime g side j inv right)
noncomputable def queryExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool)
 (N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (query g side j inv right).program) ((query g side j inv right).init (stream [N,i.val,a.q]++suffix))
 (some ((query g side j inv right).halt (stream [(LPSSparseEmitterAction.product inv right (LPSSparseEmitterAction.voltage a g side j) i).val,N,i.val,a.q]++suffix)))
 ((queryTime g side j inv right).eval (stream [N,i.val,a.q]++suffix).length):=by
 have hr (n:ℕ):raw [n]=unary n:=by simpa only [stream,List.nil_append] using raw_append_last [] n
 have hb:=actionBodyExec a g side j inv right N i suffix
 rw [←hr] at hb
 have h:=RetainedFieldComputation.retainedMarkedExec (actionBody g side j inv right) _
  [(LPSSparseEmitterAction.product inv right (LPSSparseEmitterAction.voltage a g side j) i).val] (by simp)
  (actionBodyTime g side j inv right) hb
 rw [←List.append_assoc,←MatrixListQuery.stream_append] at h
 exact h
def offsetMask (k:Fin 4):Bool:=decide (k.val<2)
def offsetProject:=PrefixProjection.prefixMachine 3 offsetMask
noncomputable def offsetProjectExec (u N i q:ℕ) (suffix:List Bool):
 EvalsToInTime (TM2.step offsetProject.program) (offsetProject.init (stream [u,N,i,q]++suffix))
 (some (offsetProject.halt (raw [u,N]))) (PrefixProjection.time.eval (stream [u,N,i,q]++suffix).length):=by
 have hf:fields 3 offsetMask 0 [u,N,i,q]=[u,N]:=by simp [fields,maskAt,offsetMask]
 have h:=PrefixProjection.polyExec 3 offsetMask [u,N,i,q] (by rfl) suffix
 rw [hf] at h
 exact h
def offset (c:ℕ):=Composition.machine offsetProject (SparseEmitterOffset.rawMachine c)
noncomputable def offsetTime (c:ℕ):=Composition.timePolynomial offsetProject PrefixProjection.time (SparseEmitterOffset.rawTime c)
noncomputable def offsetExec (c u N i q:ℕ) (suffix:List Bool):
 EvalsToInTime (TM2.step (offset c).program) ((offset c).init (stream [u,N,i,q]++suffix))
 (some ((offset c).halt (unary (c*N+u)))) ((offsetTime c).eval (stream [u,N,i,q]++suffix).length):=
 RetainedFieldComputation.composeRuns offsetProject (SparseEmitterOffset.rawMachine c) _ _ _ PrefixProjection.time (SparseEmitterOffset.rawTime c)
  (offsetProjectExec u N i q suffix) (SparseEmitterOffset.rawExec c u N)
def positioned {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool) (c:ℕ):=
 Composition.machine (query g side j inv right) (offset c)
noncomputable def positionedTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool) (c:ℕ):=
 Composition.timePolynomial (query g side j inv right) (queryTime g side j inv right) (offsetTime c)
noncomputable def positionedExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool)
 (c N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (positioned g side j inv right c).program) ((positioned g side j inv right c).init (stream [N,i.val,a.q]++suffix))
 (some ((positioned g side j inv right c).halt (unary (c*N+(LPSSparseEmitterAction.product inv right (LPSSparseEmitterAction.voltage a g side j) i).val))))
 ((positionedTime g side j inv right c).eval (stream [N,i.val,a.q]++suffix).length):=
 RetainedFieldComputation.composeRuns (query g side j inv right) (offset c) _ _ _ (queryTime g side j inv right) (offsetTime c)
  (queryExec a g side j inv right N i suffix) (offsetExec c _ N i.val a.q suffix)
def machine {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool) (c k:ℕ):=
 Composition.machine (positioned g side j inv right c) (FixedLiteral.prefixMachine (stream [k]))
noncomputable def time {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool) (c k:ℕ):=
 Composition.timePolynomial (positioned g side j inv right c) (positionedTime g side j inv right c) (FixedLiteral.prefixTime (stream [k]))
noncomputable def exec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D) (inv right:Bool)
 (c k N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (machine g side j inv right c k).program) ((machine g side j inv right c k).init (stream [N,i.val,a.q]++suffix))
 (some ((machine g side j inv right c k).halt (raw [k,c*N+(LPSSparseEmitterAction.product inv right (LPSSparseEmitterAction.voltage a g side j) i).val])))
 ((time g side j inv right c k).eval (stream [N,i.val,a.q]++suffix).length):=by
 have h:=RetainedFieldComputation.composeRuns (positioned g side j inv right c) (FixedLiteral.prefixMachine (stream [k]))
  _ _ _ (positionedTime g side j inv right c) (FixedLiteral.prefixTime (stream [k]))
  (positionedExec a g side j inv right c N i suffix) (FixedLiteral.prefixExec (stream [k]) _)
 have he:raw [k,c*N+(LPSSparseEmitterAction.product inv right (LPSSparseEmitterAction.voltage a g side j) i).val]=
  stream [k]++unary (c*N+(LPSSparseEmitterAction.product inv right (LPSSparseEmitterAction.voltage a g side j) i).val):=by
  exact raw_append_last [k] _
 rw [he]
 exact h
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterEntry
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_8f991ae56e_469:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
structure EntrySpec (D:ℕ) where
 side:Fin 2
 direction:Fin D
 inverse:Bool
 right:Bool
 offset:ℕ
 coefficient:ℕ
def entry {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (e:EntrySpec D) (N:ℕ) (i:LPSSparseGroupIndex a.q):List ℕ:=
 [e.coefficient,e.offset*N+(LPSSparseEmitterAction.product e.inverse e.right (LPSSparseEmitterAction.voltage a g e.side e.direction) i).val]
def entries {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)) (N:ℕ) (i:LPSSparseGroupIndex a.q):=
 es.flatMap (fun e=>entry a g e N i)
theorem entries_length {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)) (N:ℕ) (i:LPSSparseGroupIndex a.q):
 (entries a g es N i).length=2*es.length:=by
 induction es with
 | nil=>rfl
 | cons e es ih=>simp only [entries,List.flatMap_cons,List.length_append,entry,List.length_cons,List.length_nil] at *;omega
def mask (m:ℕ) (k:Fin (m+3)):Bool:=decide (m≤ k.val)
theorem selected (m k:ℕ) (xs:List ℕ) (N i q:ℕ) (h:k+xs.length=m):
 fields (m+2) (mask m) k (xs++[N,i,q])=[N,i,q]:=by
 induction xs generalizing k with
 | nil=>
  have hk:k=m:=by simp only [List.length_nil,Nat.add_zero] at h;exact h
  subst k
  simp [fields,maskAt,mask,Nat.mod_eq_of_lt (show m < m + 2 + 1 by omega),
   Nat.mod_eq_of_lt (show m + 1 < m + 2 + 1 by omega),Nat.mod_eq_of_lt (show m + 1 + 1 < m + 2 + 1 by omega)]
  omega
 | cons a xs ih=>
  have hk : k < m :=by simp only [List.length_cons] at h;omega
  have ht:k+1+xs.length=m:=by simp only [List.length_cons] at h;omega
  simp only [List.cons_append,fields,maskAt,mask,Nat.mod_eq_of_lt (show k < m + 2 + 1 by omega),
   show ¬ m ≤ k by omega,decide_false,Bool.false_eq_true,↓reduceIte]
  exact ih (k+1) ht
def project (m:ℕ):=PrefixProjection.prefixMachine (m+2) (mask m)
def prepare (m:ℕ):=Composition.machine (project m) BitDelimiter.machine
noncomputable def prepareTime (m:ℕ):=Composition.timePolynomial (project m) PrefixProjection.time (Polynomial.C 2*Polynomial.X+Polynomial.C 3)
noncomputable def prepareExec (m:ℕ) (xs:List ℕ) (N i q:ℕ) (suffix:List Bool) (hx:xs.length=m):
 EvalsToInTime (TM2.step (prepare m).program) ((prepare m).init (stream (xs++[N,i,q])++suffix))
 (some ((prepare m).halt (stream [N,i,q]))) ((prepareTime m).eval (stream (xs++[N,i,q])++suffix).length):=by
 have hp:=PrefixProjection.polyExec (m+2) (mask m) (xs++[N,i,q]) (by simp [hx]) suffix
 rw [selected m 0 xs N i q (by simpa using hx)] at hp
 have hd:=BitDelimiter.exec (raw [N,i,q])
 rw [MatrixListQuery.delimiter_raw _ (by simp)] at hd
 exact RetainedFieldComputation.composeRuns (project m) BitDelimiter.machine _ _ _ PrefixProjection.time
  (Polynomial.C 2*Polynomial.X+Polynomial.C 3) hp
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using hd)
def body {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (m:ℕ) (e:EntrySpec D):=
 Composition.machine (prepare m) (LPSSparseEmitterEntry.machine g e.side e.direction e.inverse e.right e.offset e.coefficient)
noncomputable def bodyTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (m:ℕ) (e:EntrySpec D):=
 Composition.timePolynomial (prepare m) (prepareTime m) (LPSSparseEmitterEntry.time g e.side e.direction e.inverse e.right e.offset e.coefficient)
noncomputable def bodyExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (m:ℕ) (e:EntrySpec D)
 (xs:List ℕ) (N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool) (hx:xs.length=m):
 EvalsToInTime (TM2.step (body g m e).program) ((body g m e).init (stream (xs++[N,i.val,a.q])++suffix))
 (some ((body g m e).halt (raw (entry a g e N i)))) ((bodyTime g m e).eval (stream (xs++[N,i.val,a.q])++suffix).length):=by
 have he:=LPSSparseEmitterEntry.exec a g e.side e.direction e.inverse e.right e.offset e.coefficient N i []
 simp only [List.append_nil] at he
 exact RetainedFieldComputation.composeRuns (prepare m) (LPSSparseEmitterEntry.machine g e.side e.direction e.inverse e.right e.offset e.coefficient)
  _ _ _ (prepareTime m) (LPSSparseEmitterEntry.time g e.side e.direction e.inverse e.right e.offset e.coefficient) (prepareExec m xs N i.val a.q suffix hx) he
def query {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (m:ℕ) (e:EntrySpec D):=RetainedFieldComputation.retainedMarked (body g m e)
noncomputable def queryTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (m:ℕ) (e:EntrySpec D):=
 RetainedFieldComputation.retainedMarkedTime (body g m e) (bodyTime g m e)
noncomputable def queryExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (m:ℕ) (e:EntrySpec D)
 (xs:List ℕ) (N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool) (hx:xs.length=m):
 EvalsToInTime (TM2.step (query g m e).program) ((query g m e).init (stream (xs++[N,i.val,a.q])++suffix))
 (some ((query g m e).halt (stream (entry a g e N i++xs++[N,i.val,a.q])++suffix)))
 ((queryTime g m e).eval (stream (xs++[N,i.val,a.q])++suffix).length):=by
 have h:=RetainedFieldComputation.retainedMarkedExec (body g m e) _ (entry a g e N i) (by simp [entry]) (bodyTime g m e)
  (bodyExec a g m e xs N i suffix hx)
 rw [←List.append_assoc,←MatrixListQuery.stream_append,←List.append_assoc] at h
 exact h
def collector {p D:ℕ} (g:Fin D→LPSGeneratorIndex p):List (EntrySpec D)→Machine
 | []=>MatrixListQuery.identityMachine
 | e::es=>Composition.machine (collector g es) (query g (2*es.length) e)
noncomputable def collectorTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p):List (EntrySpec D)→Polynomial ℕ
 | []=>Polynomial.C 4*Polynomial.X+Polynomial.C 4
 | e::es=>Composition.timePolynomial (collector g es) (collectorTime g es) (queryTime g (2*es.length) e)
noncomputable def collectorExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D))
 (N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (collector g es).program) ((collector g es).init (stream [N,i.val,a.q]++suffix))
 (some ((collector g es).halt (stream (entries a g es N i++[N,i.val,a.q])++suffix)))
 ((collectorTime g es).eval (stream [N,i.val,a.q]++suffix).length):=by
 induction es with
 | nil=>
  have hm:collector g ([]:List (EntrySpec D))=MatrixListQuery.identityMachine:=rfl
  rw [hm]
  simpa only [collectorTime,entries,List.flatMap_nil,List.nil_append,Polynomial.eval_add,
   Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using MatrixListQuery.identityExec (stream [N,i.val,a.q]++suffix)
 | cons e es ih=>
  exact RetainedFieldComputation.composeRuns (collector g es) (query g (2*es.length) e) _ _ _
   (collectorTime g es) (queryTime g (2*es.length) e) ih (queryExec a g (2*es.length) e (entries a g es N i) N i suffix (entries_length a g es N i))
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
def machine {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)):=
 Composition.machine (collector g es) (FixedLiteral.prefixMachine (stream [es.length]))
noncomputable def time {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)):=
 Composition.timePolynomial (collector g es) (collectorTime g es) (FixedLiteral.prefixTime (stream [es.length]))
noncomputable def exec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D))
 (N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (machine g es).program) ((machine g es).init (stream [N,i.val,a.q]++suffix))
 (some ((machine g es).halt (stream (es.length::entries a g es N i++[N,i.val,a.q])++suffix)))
 ((time g es).eval (stream [N,i.val,a.q]++suffix).length):=by
 have hc:=collectorExec a g es N i suffix
 have h:=RetainedFieldComputation.composeRuns (collector g es) (FixedLiteral.prefixMachine (stream [es.length]))
  _ _ _ (collectorTime g es) (FixedLiteral.prefixTime (stream [es.length])) hc (FixedLiteral.prefixExec (stream [es.length]) _)
 rw [←List.append_assoc,←MatrixListQuery.stream_append] at h
 exact h
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow
namespace QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterReorder
open QEC.Coding.BitTuring Turing StateTransition FieldProjection
local instance _p2m_local_instance_8f991ae56e_583:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def mask (m:ℕ) (k:Fin (m+3)):Bool:=decide (k.val < m)
theorem selected (m k:ℕ) (xs:List ℕ) (N i q:ℕ) (h:k+xs.length=m):
 fields (m+2) (mask m) k (xs++[N,i,q])=xs:=by
 induction xs generalizing k with
 | nil=>
  have hk:k=m:=by simp only [List.length_nil,Nat.add_zero] at h;exact h
  subst k
  simp [fields,maskAt,mask,Nat.mod_eq_of_lt (show m < m + 2 + 1 by omega),
   Nat.mod_eq_of_lt (show m + 1 < m + 2 + 1 by omega),Nat.mod_eq_of_lt (show m + 1 + 1 < m + 2 + 1 by omega)]
  omega
 | cons a xs ih=>
  have hk : k < m :=by simp only [List.length_cons] at h;omega
  have ht:k+1+xs.length=m:=by simp only [List.length_cons] at h;omega
  simp only [List.cons_append,fields,maskAt,mask,Nat.mod_eq_of_lt (show k < m + 2 + 1 by omega),
   hk,decide_true,↓reduceIte]
  congr 1
  exact ih (k+1) ht
def remove (m:ℕ):=SuffixJoin.machine (FieldProjection.machine (m+2) (mask m))
noncomputable def removeTime:Polynomial ℕ:=Polynomial.C 4*Polynomial.X+Polynomial.C 5
noncomputable def removeExec (m:ℕ) (xs:List ℕ) (N i q:ℕ) (suffix:List Bool) (hx:xs.length=m) (hn:xs≠[]):
 EvalsToInTime (TM2.step (remove m).program) ((remove m).init (stream (xs++[N,i,q])++suffix))
 (some ((remove m).halt (stream xs++suffix))) (removeTime.eval (stream (xs++[N,i,q])++suffix).length):=by
 have hp:=PrefixProjection.partialExec (m+2) (mask m) (xs++[N,i,q]) (by simp [hx]) suffix
 have hf:=selected m 0 xs N i q (by simpa using hx)
 rw [hf] at hp
 have h:=SuffixJoin.exec (FieldProjection.machine (m+2) (mask m)) (by change (0:Fin 3)≠2;decide)
  _ suffix (raw xs) _ hp
 have he:raw xs++false::suffix=stream xs++suffix:=by
  rw [←List.singleton_append,←List.append_assoc,MatrixListQuery.delimiter_raw xs hn]
 rw [he] at h
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hs:=steps_le (m+2) (mask m) (xs++[N,i,q])
 have hy:=raw_length_le xs
 have hpref:(stream xs).length≤(stream (xs++[N,i,q])).length:=by rw [MatrixListQuery.stream_append,List.length_append];omega
 simp only [removeTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,List.length_append]
 omega
def copy (m:ℕ):=RetainedInput.machine (QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow.prepare m)
noncomputable def copyTime (m:ℕ):=RetainedInput.timePolynomial (QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow.prepare m)
 (QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow.prepareTime m)
noncomputable def copyExec (m:ℕ) (row:List ℕ) (N i q:ℕ) (suffix:List Bool) (hr:row.length=m):
 EvalsToInTime (TM2.step (copy m).program) ((copy m).init (stream (row++[N,i,q])++suffix))
 (some ((copy m).halt (stream ([N,i,q]++row++[N,i,q])++suffix)))
 ((copyTime m).eval (stream (row++[N,i,q])++suffix).length):=by
 have h:=RetainedInput.executes_polynomial (QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow.prepare m)
  (fun _:Unit=>stream (row++[N,i,q])++suffix) (fun _=>stream [N,i,q])
  (QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow.prepareTime m)
  (fun _=>QEC.Coding.TannerLiftedProduct.LPSSparseEmitterRow.prepareExec m row N i q suffix hr) ()
 rw [←List.append_assoc,←MatrixListQuery.stream_append,←List.append_assoc] at h
 exact h
def machine (m:ℕ):=Composition.machine (copy m) (remove (m+3))
noncomputable def time (m:ℕ):=Composition.timePolynomial (copy m) (copyTime m) removeTime
noncomputable def exec (m:ℕ) (row:List ℕ) (N i q:ℕ) (suffix:List Bool) (hr:row.length=m):
 EvalsToInTime (TM2.step (machine m).program) ((machine m).init (stream (row++[N,i,q])++suffix))
 (some ((machine m).halt (stream ([N,i,q]++row)++suffix)))
 ((time m).eval (stream (row++[N,i,q])++suffix).length):=by
 exact RetainedFieldComputation.composeRuns (copy m) (remove (m+3)) _ _ _ (copyTime m) removeTime
  (copyExec m row N i q suffix hr) (removeExec (m+3) ([N,i,q]++row) N i q suffix (by simp [hr]) (by simp))
end QEC.Coding.BitTuring.UnaryArithmetic.SparseEmitterReorder


