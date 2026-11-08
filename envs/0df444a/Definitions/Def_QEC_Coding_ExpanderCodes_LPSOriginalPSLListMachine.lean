-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPSLListMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:07:04.253087+00:00
-- url     : https://prove2.me/theorems/7e71a5ee-2eb7-4d75-b2c9-e769e155c5e0
-- title:
--   LPSOriginal PSLList Machine
-- statement:
--   Definitions and structural lemmas for LPSOriginal PSLList Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLListMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLSearchMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSLListMachine
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_after_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_body_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_embed_halt
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_empty_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_entry_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_parse_current_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_qword_length
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
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_e75c5360c0_15 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
def search:=retainedSearchMachine
def machine:=QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.machine search
def state (q:ℕ) (R:List SL(2,ZMod q)) (C:List Bool):=
 cfg search 0 false none (qword q++rows q R) [] [] C []
theorem search_io:search.input≠search.output:=by simp [search,retainedSearchMachine,RetainedInput.machine]
theorem input_eq (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 input q A R=qword q++rows q (A::R):=by
 simp [QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.input,header,rows_cons,stream,qword,List.append_assoc]
noncomputable def invocationExec (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q))
 (R:List SL(2,ZMod q)) (C:List Bool):
 EvalsToInTime (TM2.step machine.program) (state q (A::R) C)
  (some (state q R (pushed (found q A R) (stream (coords q A)) C)))
  (retainedSearchTime.eval (input q A R).length+4*(q+1)+(stream (coords q A)).length+2*(rows q R).length+6):=by
 let hQ:=retainedSearchExec q A R
 have hin:=input_eq q A R
 have hentry:=entry_run search search_io q (rows q (A::R)) C (by intro he;have hh:=rows_cons_nonempty q A R;simp [he] at hh)
 have hbody:=body_run search C (input q A R) (found q A R::input q A R) hQ.steps hQ.evals_in_steps
 have hparse:=parse_current_run search search_io (found q A R) q (coords q A)
  (by simp [coords,LPSMatrixProductMachine.fields]) (rows q R) C
 have hafter:=after_run search search_io (found q A R) (some false) q (rows q R)
  (pushed (found q A R) (stream (coords q A)) C)
 have hRun:(next search)^[
  (2*(rows q R).length+(q+1)+3)+((stream (coords q A)).length+(q+1)+1)+hQ.steps+(2*(q+1)+2)]
  (some (state q (A::R) C))=some (state q R (pushed (found q A R) (stream (coords q A)) C)):=by
  unfold state
  rw [Function.iterate_add_apply,hentry,Function.iterate_add_apply]
  simp only [hin] at hbody
  rw [hbody,embed_halt search search_io,Function.iterate_add_apply]
  simp only [rows_cons,←List.append_assoc]
  rw [hparse,hafter]
 refine ⟨⟨_,hRun⟩,?_⟩
 have hm:=hQ.steps_le_m
 change (2*(rows q R).length+(q+1)+3)+((stream (coords q A)).length+(q+1)+1)+hQ.steps+(2*(q+1)+2)≤_
 omega
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_e75c5360c0_62 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
def collected (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)) (C:List Bool):List Bool:=
 (rows q (representatives q R)).reverse++C
def stateSize (q:ℕ) (R:List SL(2,ZMod q)) (C:List Bool):ℕ:=(qword q++rows q R).length+C.length
theorem pushed_length (f:Bool) (w C:List Bool):(pushed f w C).length≤w.length+C.length:=by
 cases f <;>simp [pushed]
theorem stateSize_cons (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)) (C:List Bool):
 stateSize q (A::R) C=(q+1)+(stream (coords q A)).length+(rows q R).length+C.length:=by
 simp only [stateSize,rows_cons,List.length_append,qword_length,Nat.add_assoc]
theorem stateSize_next (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)) (C:List Bool):
 stateSize q R (pushed (found q A R) (stream (coords q A)) C)≤ stateSize q (A::R) C:=by
 have hc:=pushed_length (found q A R) (stream (coords q A)) C
 rw [stateSize_cons]
 simp only [stateSize,List.length_append,qword_length]
 omega
theorem collected_cons (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)) (C:List Bool):
 collected q (A::R) C=collected q R (pushed (found q A R) (stream (coords q A)) C):=by
 cases hf:found q A R <;>simp [collected,representatives,hf,pushed,rows_cons,List.reverse_append,List.append_assoc]
noncomputable def callBudget (L:ℕ):ℕ:=retainedSearchTime.eval L+10*L+10
noncomputable def executeAux (q L:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)) (C:List Bool)
 (hsize:stateSize q R C≤ L):
 EvalsToInTime (TM2.step machine.program) (state q R C)
  (some (machine.halt (collected q R C).tail.reverse)) ((R.length+1)*callBudget L):=by
 induction R generalizing C with
 |nil=>
  have hr:=empty_run search search_io q C
  have hh:EvalsToInTime (TM2.step machine.program) (state q [] C)
   (some (machine.halt (collected q [] C).tail.reverse)) (2*(q+1)+C.tail.length+4):=by
   refine ⟨⟨_,?_⟩,le_refl _⟩
   simp only [state,collected,representatives,rows,List.flatMap_nil,stream,List.append_nil,
    List.reverse_nil,List.nil_append]
   change (QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.next search)^[2*(q+1)+C.tail.length+4]
    (some (QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.cfg search 0 false none (qword q) [] [] C []))=
    some ((QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.machine search).halt C.tail.reverse)
   exact hr
  refine {hh with steps_le_m:=hh.steps_le_m.trans ?_}
  have htail:C.tail.length≤ C.length:=by simp only [List.length_tail];omega
  have hs:(q+1)+C.length≤ L:=by
   simpa only [stateSize,rows,List.flatMap_nil,stream,List.append_nil,qword_length] using hsize
  simp only [List.length_nil,Nat.zero_add,Nat.one_mul,callBudget]
  omega
 |cons A R ih=>
  have hi:=invocationExec q A R C
  have ht:=ih (pushed (found q A R) (stream (coords q A)) C) ((stateSize_next q A R C).trans hsize)
  have hs:(q+1)+(stream (coords q A)).length+(rows q R).length+C.length≤ L:=by
   rwa [stateSize_cons] at hsize
  have hin:(QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.input q A R).length≤ L:=by
   rw [input_eq,rows_cons]
   simp only [List.length_append,qword_length]
   omega
  have hm:=Composition.polynomial_eval_monotone retainedSearchTime hin
  dsimp only at hm
  have hc:EvalsToInTime (TM2.step machine.program) (state q (A::R) C)
   (some (state q R (pushed (found q A R) (stream (coords q A)) C))) (callBudget L):=by
   refine {hi with steps_le_m:=hi.steps_le_m.trans ?_}
   dsimp only [callBudget]
   omega
  have hh:=EvalsToInTime.trans (TM2.step machine.program) _ _ _ _ _ hc ht
  rw [←collected_cons] at hh
  have he:(R.length+1)*callBudget L+callBudget L=((A::R).length+1)*callBudget L:=by
   simp only [List.length_cons];ring
  rwa [he] at hh
noncomputable def time:Polynomial ℕ:=(Polynomial.X+1)*(retainedSearchTime+Polynomial.C 10*Polynomial.X+Polynomial.C 10)
noncomputable def execute (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step machine.program) (state q R [])
  (some (machine.halt (rows q (representatives q R)).reverse.tail.reverse))
  (time.eval (qword q++rows q R).length):=by
 let L:=(qword q++rows q R).length
 have h0:=executeAux q L R [] (by simp [stateSize,L])
 have h:EvalsToInTime (TM2.step machine.program) (state q R [])
  (some (machine.halt (rows q (representatives q R)).reverse.tail.reverse)) ((R.length+1)*callBudget L):=by
  simpa only [collected,List.append_nil] using h0
 have hc:R.length≤ L:=by
  have hs:=rows_count_bound q R
  dsimp [L];simp only [List.length_append];omega
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [time,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_C]
 change (R.length+1)*callBudget L≤(L+1)*callBudget L
 exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_e75c5360c0_157 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem init_eq (q:ℕ) (R:List SL(2,ZMod q)):
 machine.init (qword q++rows q R)=state q R []:=by
 simp [Machine.init,QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.machine,QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.machine,state,QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.cfg,TM2.Cfg.mk.injEq]
 funext j;cases j with
 |inl j=>by_cases hi:j=search.input <;>by_cases ho:j=search.output <;>
  simp_all [DrainInput.tapes,Function.update,search_io,eq_comm]
 |inr j=>fin_cases j <;>simp [Function.update]
theorem raw_final_output (q:ℕ) (R:List SL(2,ZMod q)):
 (rows q R).reverse.tail.reverse=raw (R.flatMap (coords q)):=by
 simp only [rows,List.tail_reverse,List.reverse_reverse,raw]
noncomputable def rawExec (q:ℕ) [Fact q.Prime] (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step machine.program) (machine.init (qword q++rows q R))
  (some (machine.halt (raw ((representatives q R).flatMap (coords q)))))
  (time.eval (qword q++rows q R).length):=by
 have h:=execute q R
 rw [←init_eq,raw_final_output] at h
 exact h
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_e75c5360c0_187 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
noncomputable def composeRuns (A B:Machine) (x y z:List Bool) (p r:Polynomial ℕ)
 (hA:EvalsToInTime (TM2.step A.program) (A.init x) (some (A.halt y)) (p.eval x.length))
 (hB:EvalsToInTime (TM2.step B.program) (B.init y) (some (B.halt z)) (r.eval y.length)):
 EvalsToInTime (TM2.step (Composition.machine A B).program) ((Composition.machine A B).init x)
  (some ((Composition.machine A B).halt z)) ((Composition.timePolynomial A p r).eval x.length):=by
 have hL:y.length≤(Composition.intermediateLengthPolynomial A p).eval x.length:=by
  simpa [Composition.intermediateLengthPolynomial,Nat.mul_comm] using Machine.output_length_le A x y _ hA
 have hr:=Composition.polynomial_eval_monotone r hL
 have hh:=Composition.executes A B x y z _ _ hA hB
 refine {hh with steps_le_m:=hh.steps_le_m.trans ?_}
 simp only [Composition.timePolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C]
 exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hr (Nat.mul_le_mul_left 2 hL)) 2) _
abbrev Input:={q:ℕ//q.Prime}
instance (a:Input):Fact a.val.Prime:=⟨a.property⟩
def sl:=LPSOriginalSLListMachine.machine
def switch:=QEC.Coding.BitTuring.BooleanSwitch.machine sl sl
noncomputable def switchTime:Polynomial ℕ:=LPSOriginalSLListMachine.time+Polynomial.C 2
theorem sl_io:sl.input≠sl.output:=by simp [sl,LPSOriginalSLListMachine.machine,Composition.machine]
noncomputable def switchExec (a:Input):
 EvalsToInTime (TM2.step switch.program) (switch.init (false::unary a.val))
  (some (switch.halt (LPSOriginalSLListMachine.output a.val))) (switchTime.eval (false::unary a.val).length):=by
 have h:=QEC.Coding.BitTuring.BooleanSwitch.execB sl sl sl_io sl_io (unary a.val) _ _
  (LPSOriginalSLListMachine.exec a.val a.property.one_lt)
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hm:=Composition.polynomial_eval_monotone LPSOriginalSLListMachine.time
  (show (unary a.val).length≤(false::unary a.val).length by simp)
 dsimp only at hm
 simp only [switchTime,Polynomial.eval_add,Polynomial.eval_C]
 omega
def markReverse:=Composition.machine BitDelimiter.machine BitReverse.machine
noncomputable def markReverseTime:Polynomial ℕ:=
 Composition.timePolynomial BitDelimiter.machine (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (Polynomial.X+1)
noncomputable def markReverseExec (w:List Bool):
 EvalsToInTime (TM2.step markReverse.program) (markReverse.init w)
  (some (markReverse.halt (w++[false]).reverse)) (markReverseTime.eval w.length):=by
 have hd:=BitDelimiter.exec w
 have hr:=BitReverse.exec (w++[false])
 exact composeRuns BitDelimiter.machine BitReverse.machine w (w++[false]) _
  (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (Polynomial.X+1)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using hd)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using hr)
theorem original_fields_nonempty (a:Input):
 (lpsSLList a.val).flatMap (coords a.val)≠[]:=by
 have hm:=mem_lpsSLList a.val (1:SL(2,ZMod a.val))
 intro he
 have hh:∀A∈lpsSLList a.val,coords a.val A=[]:=List.flatMap_eq_nil_iff.mp he
 have hz:=hh 1 hm
 simp [coords,LPSMatrixProductMachine.fields] at hz
theorem marked_source (a:Input):
 LPSOriginalSLListMachine.output a.val++[false]=rows a.val (lpsSLList a.val):=by
 change raw ((lpsSLList a.val).flatMap (coords a.val))++[false]=_
 rw [MatrixListQuery.delimiter_raw _ (original_fields_nonempty a)]
 rfl
def reverseBody:=Composition.machine switch markReverse
noncomputable def reverseTime:Polynomial ℕ:=Composition.timePolynomial switch switchTime markReverseTime
noncomputable def reverseBodyExec (a:Input):
 EvalsToInTime (TM2.step reverseBody.program) (reverseBody.init (false::unary a.val))
  (some (reverseBody.halt (rows a.val (lpsSLList a.val)).reverse)) (reverseTime.eval (false::unary a.val).length):=by
 have hm:=markReverseExec (LPSOriginalSLListMachine.output a.val)
 rw [marked_source a] at hm
 exact composeRuns switch markReverse _ _ _ switchTime markReverseTime (switchExec a) hm
def retain:=RetainedInput.machine reverseBody
noncomputable def retainTime:Polynomial ℕ:=RetainedInput.timePolynomial reverseBody reverseTime
noncomputable def retainExec (a:Input):
 EvalsToInTime (TM2.step retain.program) (retain.init (false::unary a.val))
  (some (retain.halt ((rows a.val (lpsSLList a.val)).reverse++false::unary a.val)))
  (retainTime.eval (false::unary a.val).length):=
 RetainedInput.executes_polynomial reverseBody (fun a:Input=>false::unary a.val)
  (fun a=> (rows a.val (lpsSLList a.val)).reverse) reverseTime reverseBodyExec a
def restore:=Composition.machine retain BitReverse.machine
noncomputable def restoreTime:Polynomial ℕ:=Composition.timePolynomial retain retainTime (Polynomial.X+1)
noncomputable def restoreExec (a:Input):
 EvalsToInTime (TM2.step restore.program) (restore.init (false::unary a.val))
  (some (restore.halt (qword a.val++rows a.val (lpsSLList a.val))))
  (restoreTime.eval (false::unary a.val).length):=by
 have hr:=BitReverse.exec ((rows a.val (lpsSLList a.val)).reverse++false::unary a.val)
 have he:((rows a.val (lpsSLList a.val)).reverse++false::unary a.val).reverse=
  qword a.val++rows a.val (lpsSLList a.val):=by
  simp [qword,unary,List.reverse_append,List.reverse_cons,List.append_assoc]
 rw [he] at hr
 exact composeRuns retain BitReverse.machine _ _ _ retainTime (Polynomial.X+1) (retainExec a)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using hr)
def machine:=Composition.machine (FixedLiteral.prefixMachine [false]) restore
noncomputable def time:Polynomial ℕ:=
 Composition.timePolynomial (FixedLiteral.prefixMachine [false]) (FixedLiteral.prefixTime [false]) restoreTime
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.val))
  (some (machine.halt (qword a.val++rows a.val (lpsSLList a.val)))) (time.eval (unary a.val).length):=by
 have hp:=FixedLiteral.prefixExec [false] (unary a.val)
 exact composeRuns (FixedLiteral.prefixMachine [false]) restore _ _ _ (FixedLiteral.prefixTime [false]) restoreTime hp (restoreExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_e75c5360c0_308 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
abbrev Input:=QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.Input
def input (a:Input):List Bool:=unary a.val
def output (q:ℕ) [Fact q.Prime]:List Bool:=
 raw ((QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.representatives q (lpsSLList q)).flatMap (QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine.coords q))
def machine:=Composition.machine QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.machine QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.machine
noncomputable def time:Polynomial ℕ:=Composition.timePolynomial QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.machine
 QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.time QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.time
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
  (some (machine.halt (output a.val))) (time.eval (input a).length):=by
 have hi:=QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.exec a
 have hf:=QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.rawExec a.val (lpsSLList a.val)
 exact QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.composeRuns QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.machine QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.machine
  _ _ _ QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Initializer.time QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine.Filter.time hi hf
noncomputable def outputsInTime (a:Input):
 TM2OutputsInTime machine.toFinTM2 (input a) (some (output a.val)) (time.eval (input a).length):=
 Machine.outputsInTime machine _ _ _ (exec a)
noncomputable def computableInPolyTime:
 TM2ComputableInPolyTime input id (fun a:Input=>output a.val) where
 tm:=machine.toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time
 outputsFun:=fun a=>by
  change TM2OutputsInTime machine.toFinTM2 (List.map id (input a))
   (some (List.map id (output a.val))) (time.eval (input a).length)
  have h:=outputsInTime a
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
  (some (machine.halt (output a.q))) (time.eval (2*Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨a.q,a.prime⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 change time.eval (unary a.q).length≤ time.eval (2*Fintype.card PSL(2,ZMod a.q))
 rw [unary_length]
 exact Composition.polynomial_eval_monotone time a.q_le_two_mul_card_psl
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p):
 TM2OutputsInTime machine.toFinTM2 (unary a.q) (some (output a.q))
  (time.eval (2*Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLListMachine


