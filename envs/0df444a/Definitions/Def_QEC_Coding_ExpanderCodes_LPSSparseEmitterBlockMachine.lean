-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterBlockMachine
-- name    : QEC_Coding_ExpanderCodes_LPSSparseEmitterBlockMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:07:23.424818+00:00
-- url     : https://prove2.me/theorems/0f62cf2e-d83d-47bb-971e-940962ae9c97
-- title:
--   LPSSparse Emitter Block Machine
-- statement:
--   Definitions and structural lemmas for LPSSparse Emitter Block Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterBlockMachine.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterRowMachine
import Definitions.Def_QEC_Coding_BitTuring_UnaryRippleCounterTraversal
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_indexNext_val
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_indexOverflow_iff_last
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum
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
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
open LPSSparseEmitterRow
local instance _p2m_local_instance_2bf7a625d3_20:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def rowWord {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D))
 (N:ℕ) (i:LPSSparseGroupIndex a.q):List Bool:=stream (es.length::entries a g es N i)
def first {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)):=
 Composition.machine (LPSSparseEmitterRow.machine g es) (SparseEmitterReorder.machine (1+2*es.length))
noncomputable def firstTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)):=
 Composition.timePolynomial (LPSSparseEmitterRow.machine g es) (LPSSparseEmitterRow.time g es) (SparseEmitterReorder.time (1+2*es.length))
noncomputable def firstExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D))
 (N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (first g es).program) ((first g es).init (stream [N,i.val,a.q]++suffix))
 (some ((first g es).halt (stream [N,i.val,a.q]++rowWord a g es N i++suffix)))
 ((firstTime g es).eval (stream [N,i.val,a.q]++suffix).length):=by
 have hl:(es.length::entries a g es N i).length=1+2*es.length:=by rw [List.length_cons,entries_length];omega
 have h:=RetainedFieldComputation.composeRuns (LPSSparseEmitterRow.machine g es) (SparseEmitterReorder.machine (1+2*es.length))
  _ _ _ (LPSSparseEmitterRow.time g es) (SparseEmitterReorder.time (1+2*es.length))
  (LPSSparseEmitterRow.exec a g es N i suffix) (SparseEmitterReorder.exec (1+2*es.length) (es.length::entries a g es N i) N i.val a.q suffix hl)
 rw [MatrixListQuery.stream_append] at h
 exact h
def words {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p):List (List (EntrySpec D))→ℕ→LPSSparseGroupIndex a.q→List Bool
 | [],_,_=>[]
 | es::rs,N,i=>words a g rs N i++rowWord a g es N i
def collector {p D:ℕ} (g:Fin D→LPSGeneratorIndex p):List (List (EntrySpec D))→Machine
 | []=>MatrixListQuery.identityMachine
 | es::rs=>Composition.machine (first g es) (collector g rs)
noncomputable def collectorTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p):List (List (EntrySpec D))→Polynomial ℕ
 | []=>Polynomial.C 4*Polynomial.X+Polynomial.C 4
 | es::rs=>Composition.timePolynomial (first g es) (firstTime g es) (collectorTime g rs)
noncomputable def collectorExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (N:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (collector g rs).program) ((collector g rs).init (stream [N,i.val,a.q]++suffix))
 (some ((collector g rs).halt (stream [N,i.val,a.q]++words a g rs N i++suffix)))
 ((collectorTime g rs).eval (stream [N,i.val,a.q]++suffix).length):=by
 induction rs generalizing suffix with
 | nil=>
  have hm:collector g ([]:List (List (EntrySpec D)))=MatrixListQuery.identityMachine:=rfl
  rw [hm]
  simpa only [collectorTime,words,List.append_nil,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
   using MatrixListQuery.identityExec (stream [N,i.val,a.q]++suffix)
 | cons es rs ih=>
  have hm:collector g (es::rs)=Composition.machine (first g es) (collector g rs):=rfl
  rw [hm]
  have h:=RetainedFieldComputation.composeRuns (first g es) (collector g rs) _ _ _ (firstTime g es) (collectorTime g rs)
   (firstExec a g es N i suffix) (by simpa only [List.append_assoc] using ih (rowWord a g es N i++suffix))
  simpa only [collectorTime,words,List.append_assoc] using h
def body {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):=
 Composition.machine (collector g rs) (RippleCounter.machine 0)
noncomputable def bodyTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):=
 Composition.timePolynomial (collector g rs) (collectorTime g rs) (RippleCounter.time 0)
noncomputable def bodyExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (body g rs).program) ((body g rs).init (stream [(lpsPSLList a.q).length,i.val,a.q]++suffix))
 (some ((body g rs).halt (LPSLexicographicCounter.indexOverflow a.q i::
  (stream [(lpsPSLList a.q).length,(LPSLexicographicCounter.indexNext a.q i).val,a.q]++
   words a g rs (lpsPSLList a.q).length i++suffix))))
 ((bodyTime g rs).eval (stream [(lpsPSLList a.q).length,i.val,a.q]++suffix).length):=by
 have hc:=collectorExec a g rs (lpsPSLList a.q).length i suffix
 have hb:=LPSLexicographicCounter.indexExec a.q (i,stream [a.q]++words a g rs (lpsPSLList a.q).length i++suffix)
 have he (j:LPSSparseGroupIndex a.q):LPSLexicographicCounter.indexInput a.q
  (j,stream [a.q]++words a g rs (lpsPSLList a.q).length i++suffix)=
  stream [(lpsPSLList a.q).length,j.val,a.q]++words a g rs (lpsPSLList a.q).length i++suffix:=by
  simp only [LPSLexicographicCounter.indexInput,RippleCounter.payload,stream,List.append_assoc,List.cons_append,List.nil_append]
 rw [he,he] at hb
 exact RetainedFieldComputation.composeRuns (collector g rs) (RippleCounter.machine 0) _ _ _ (collectorTime g rs) (RippleCounter.time 0) hc hb
def machine {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):=FlagLoop.machine (body g rs)
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
open LPSSparseEmitterRow
local instance _p2m_local_instance_2bf7a625d3_90:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def entryWeight {D:ℕ} (e:EntrySpec D):ℕ:=e.coefficient+e.offset+3
def rowWeight {D:ℕ} (es:List (EntrySpec D)):ℕ:=es.length+1+(es.map entryWeight).sum
def weight {D:ℕ} (rs:List (List (EntrySpec D))):ℕ:=(rs.map rowWeight).sum
theorem entry_length_le {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (e:EntrySpec D) (i:LPSSparseGroupIndex a.q):
 (stream (entry a g e (lpsPSLList a.q).length i)).length≤ entryWeight e*((lpsPSLList a.q).length+1):=by
 have hu: (LPSSparseEmitterAction.product e.inverse e.right (LPSSparseEmitterAction.voltage a g e.side e.direction) i).val < (lpsPSLList a.q).length :=
  (LPSSparseEmitterAction.product e.inverse e.right (LPSSparseEmitterAction.voltage a g e.side e.direction) i).isLt
 simp only [entry,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,entryWeight]
 nlinarith
theorem entries_length_le {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)) (i:LPSSparseGroupIndex a.q):
 (stream (entries a g es (lpsPSLList a.q).length i)).length≤(es.map entryWeight).sum*((lpsPSLList a.q).length+1):=by
 induction es with
 | nil=>simp [entries,stream]
 | cons e es ih=>
  have h:=entry_length_le a g e i
  simp only [entries,List.flatMap_cons,MatrixListQuery.stream_append,List.length_append,List.map_cons,List.sum_cons] at *
  nlinarith
theorem rowWord_length_le {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (es:List (EntrySpec D)) (i:LPSSparseGroupIndex a.q):
 (rowWord a g es (lpsPSLList a.q).length i).length≤ rowWeight es*((lpsPSLList a.q).length+1):=by
 have h:=entries_length_le a g es i
 simp only [rowWord,stream,List.length_append,List.length_cons,unary_length,rowWeight]
 nlinarith
theorem words_length_le {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))) (i:LPSSparseGroupIndex a.q):
 (words a g rs (lpsPSLList a.q).length i).length≤ weight rs*((lpsPSLList a.q).length+1):=by
 induction rs with
 | nil=>simp [words,weight]
 | cons es rs ih=>
  have h:=rowWord_length_le a g es i
  simp only [words,List.length_append,weight,List.map_cons,List.sum_cons] at *
  nlinarith
def advance {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (x:LPSSparseGroupIndex a.q×List Bool):LPSSparseGroupIndex a.q×List Bool:=
 (LPSLexicographicCounter.indexNext a.q x.1,words a g rs (lpsPSLList a.q).length x.1++x.2)
def result {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (n:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):LPSSparseGroupIndex a.q×List Bool:=
 (advance a g rs)^[n] (i,suffix)
def payload {p:ℕ} (a:LPSResiduePrime p) (x:LPSSparseGroupIndex a.q×List Bool):List Bool:=
 stream [(lpsPSLList a.q).length,x.1.val,a.q]++x.2
theorem result_zero {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 result a g rs 0 i suffix=(i,suffix):=rfl
theorem result_succ {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))) (n:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 result a g rs (n+1) i suffix=result a g rs n (LPSLexicographicCounter.indexNext a.q i) (words a g rs (lpsPSLList a.q).length i++suffix):=
 Function.iterate_succ_apply _ _ _
theorem result_suffix_length {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))) (n:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 (result a g rs n i suffix).2.length≤ suffix.length+n*(weight rs*((lpsPSLList a.q).length+1)):=by
 induction n generalizing i suffix with
 | zero=>simp [result_zero]
 | succ n ih=>
  rw [result_succ]
  have h:=ih (LPSLexicographicCounter.indexNext a.q i) (words a g rs (lpsPSLList a.q).length i++suffix)
  have hw:=words_length_le a g rs i
  simp only [List.length_append] at h
  nlinarith
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
open LPSSparseEmitterRow
local instance _p2m_local_instance_2bf7a625d3_150:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
noncomputable def invocationCost {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (i:LPSSparseGroupIndex a.q) (suffix:List Bool):ℕ:=
 (bodyTime g rs).eval (payload a (i,suffix)).length+2*(payload a (advance a g rs (i,suffix))).length+4
noncomputable def cost {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):
 ℕ→LPSSparseGroupIndex a.q→List Bool→ℕ
 | 0,i,suffix=>invocationCost a g rs i suffix
 | n+1,i,suffix=>cost a g rs n (LPSLexicographicCounter.indexNext a.q i) (words a g rs (lpsPSLList a.q).length i++suffix)+
  invocationCost a g rs i suffix
noncomputable def remainingExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (n:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool) (hlast:i.val+n+1=(lpsPSLList a.q).length):
 EvalsToInTime (TM2.step (FlagLoop.machine (body g rs)).program) ((FlagLoop.machine (body g rs)).init (payload a (i,suffix)))
 (some ((FlagLoop.machine (body g rs)).halt (payload a (result a g rs (n+1) i suffix)))) (cost a g rs n i suffix):=by
 induction n generalizing i suffix with
 | zero=>
  have hf:LPSLexicographicCounter.indexOverflow a.q i=true:=LPSLexicographicCounter.indexOverflow_iff_last a.q i |>.mpr (by simpa using hlast)
  have hb:=bodyExec a g rs i suffix
  have h:=FlagLoop.invocationExec (body g rs) (by simp [body,Composition.machine])
   (payload a (i,suffix)) (payload a (advance a g rs (i,suffix))) true
   ((bodyTime g rs).eval (payload a (i,suffix)).length)
   (by simpa only [payload,advance,hf,List.append_assoc] using hb)
  simpa [FlagLoop.target,cost,invocationCost,result_succ,result_zero,advance] using h
 | succ n ih=>
  have hne:i.val+1≠(lpsPSLList a.q).length:=by omega
  have hf:LPSLexicographicCounter.indexOverflow a.q i=false:=by
   apply Bool.eq_false_iff.mpr
   intro he
   exact hne ((LPSLexicographicCounter.indexOverflow_iff_last a.q i).mp he)
  have hv:(LPSLexicographicCounter.indexNext a.q i).val=i.val+1:=by
   rw [LPSLexicographicCounter.indexNext_val,Nat.mod_eq_of_lt (by omega)]
  have hb:=bodyExec a g rs i suffix
  have h:=FlagLoop.invocationExec (body g rs) (by simp [body,Composition.machine])
   (payload a (i,suffix)) (payload a (advance a g rs (i,suffix))) false
   ((bodyTime g rs).eval (payload a (i,suffix)).length)
   (by simpa only [payload,advance,hf,List.append_assoc] using hb)
  have hc:EvalsToInTime (TM2.step (FlagLoop.machine (body g rs)).program) ((FlagLoop.machine (body g rs)).init (payload a (i,suffix)))
   (some ((FlagLoop.machine (body g rs)).init (payload a (advance a g rs (i,suffix))))) (invocationCost a g rs i suffix):=by
   simpa [FlagLoop.target,invocationCost] using h
  have ht:=ih (LPSLexicographicCounter.indexNext a.q i) (words a g rs (lpsPSLList a.q).length i++suffix) (by rw [hv];omega)
  have hh:=EvalsToInTime.trans (TM2.step (FlagLoop.machine (body g rs)).program) (invocationCost a g rs i suffix)
   (cost a g rs n (LPSLexicographicCounter.indexNext a.q i) (words a g rs (lpsPSLList a.q).length i++suffix))
   ((FlagLoop.machine (body g rs)).init (payload a (i,suffix)))
   ((FlagLoop.machine (body g rs)).init (payload a (advance a g rs (i,suffix)))) _ hc ht
  simpa only [cost,result_succ] using hh
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
open LPSSparseEmitterRow
noncomputable def size {D:ℕ} (rs:List (List (EntrySpec D))):Polynomial ℕ:=Polynomial.C (weight rs+2)*(Polynomial.X+1)^2
theorem payload_length {p:ℕ} (a:LPSResiduePrime p) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 (payload a (i,suffix)).length=(lpsPSLList a.q).length+i.val+a.q+3+suffix.length:=by
 simp only [payload,List.length_append,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
 omega
theorem state_length_le {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (k:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool) (hk:k≤(lpsPSLList a.q).length):
 (payload a (result a g rs k i suffix)).length≤(size rs).eval (payload a (i,suffix)).length:=by
 have htail:=result_suffix_length a g rs k i suffix
 have hv: (result a g rs k i suffix).1.val < (lpsPSLList a.q).length :=(result a g rs k i suffix).1.isLt
 have hlen:(payload a (i,suffix)).length=(lpsPSLList a.q).length+i.val+a.q+3+suffix.length:=payload_length a i suffix
 have hN:(lpsPSLList a.q).length≤(payload a (i,suffix)).length:=by omega
 have hmult:k*(weight rs*((lpsPSLList a.q).length+1))≤
  (payload a (i,suffix)).length*(weight rs*((payload a (i,suffix)).length+1)):=
  Nat.mul_le_mul (hk.trans hN) (Nat.mul_le_mul_left _ (Nat.succ_le_succ hN))
 have hout:(payload a (result a g rs k i suffix)).length=
  (lpsPSLList a.q).length+(result a g rs k i suffix).1.val+a.q+3+(result a g rs k i suffix).2.length:=
  payload_length a _ _
 simp only [size,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
 nlinarith
theorem invocation_le {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (i:LPSSparseGroupIndex a.q) (suffix:List Bool) (L:ℕ)
 (h0:(payload a (i,suffix)).length≤L) (h1:(payload a (advance a g rs (i,suffix))).length≤L):
 invocationCost a g rs i suffix≤(bodyTime g rs).eval L+2*L+4:=by
 have hp:(bodyTime g rs).eval (payload a (i,suffix)).length≤(bodyTime g rs).eval L:=
  Composition.polynomial_eval_monotone (bodyTime g rs) h0
 dsimp only [invocationCost]
 omega
theorem cost_le {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (n:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool) (L:ℕ)
 (hL:∀k≤n+1,(payload a (result a g rs k i suffix)).length≤L):
 cost a g rs n i suffix≤(n+1)*((bodyTime g rs).eval L+2*L+4):=by
 induction n generalizing i suffix with
 | zero=>
  have h0:=hL 0 (by omega)
  have h1:=hL 1 (by omega)
  have hr:result a g rs 1 i suffix=advance a g rs (i,suffix):=rfl
  rw [result_zero] at h0
  rw [hr] at h1
  simpa only [cost,Nat.zero_add,Nat.one_mul] using invocation_le a g rs i suffix L h0 h1
 | succ n ih=>
  have h0:=hL 0 (by omega)
  have h1:=hL 1 (by omega)
  have hr:result a g rs 1 i suffix=advance a g rs (i,suffix):=rfl
  rw [result_zero] at h0
  rw [hr] at h1
  have hf:=invocation_le a g rs i suffix L h0 h1
  have ht:=ih (LPSLexicographicCounter.indexNext a.q i) (words a g rs (lpsPSLList a.q).length i++suffix)
   (fun k hk=>by simpa only [result_succ] using hL (k+1) (by omega))
  simp only [cost]
  nlinarith
noncomputable def time {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):Polynomial ℕ:=
 (Polynomial.X+1)*((bodyTime g rs).comp (size rs)+Polynomial.C 2*size rs+Polynomial.C 4)
noncomputable def exec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 EvalsToInTime (TM2.step (FlagLoop.machine (body g rs)).program) ((FlagLoop.machine (body g rs)).init (payload a (i,suffix)))
 (some ((FlagLoop.machine (body g rs)).halt (payload a (result a g rs ((lpsPSLList a.q).length-i.val) i suffix))))
 ((time g rs).eval (payload a (i,suffix)).length):=by
 have hi:=i.isLt
 let n:ℕ:=(lpsPSLList a.q).length-i.val-1
 have hn:i.val+n+1=(lpsPSLList a.q).length:=by dsimp [n];omega
 have hr:=remainingExec a g rs n i suffix hn
 have hcost:=cost_le a g rs n i suffix ((size rs).eval (payload a (i,suffix)).length)
  (fun k hk=>state_length_le a g rs k i suffix (by omega))
 have hlen:=payload_length a i suffix
 have hit:n+1≤(payload a (i,suffix)).length+1:=by omega
 have hbound:=Nat.mul_le_mul_right ((bodyTime g rs).eval ((size rs).eval (payload a (i,suffix)).length)+
  2*(size rs).eval (payload a (i,suffix)).length+4) hit
 have he:n+1=(lpsPSLList a.q).length-i.val:=by omega
 rw [he] at hr
 refine {hr with steps_le_m:=hr.steps_le_m.trans (hcost.trans ?_)}
 simpa only [time,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
  Polynomial.eval_comp,Polynomial.eval_C] using hbound
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
open LPSSparseEmitterRow
theorem result_succ_last {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (n:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 result a g rs (n+1) i suffix=advance a g rs (result a g rs n i suffix):=Function.iterate_succ_apply' _ _ _
theorem result_index_val {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (n:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 (result a g rs n i suffix).1.val=(i.val+n)%(lpsPSLList a.q).length:=by
 induction n with
 | zero=>simpa only [result_zero,Nat.add_zero] using (Nat.mod_eq_of_lt i.isLt).symm
 | succ n ih=>
  rw [result_succ_last]
  change (LPSLexicographicCounter.indexNext a.q (result a g rs n i suffix).1).val=_
  rw [LPSLexicographicCounter.indexNext_val,ih,Nat.mod_add_mod]
  congr 1
theorem result_final_index {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (i:LPSSparseGroupIndex a.q) (suffix:List Bool):
 (result a g rs ((lpsPSLList a.q).length-i.val) i suffix).1.val=0:=by
 rw [result_index_val,show i.val+((lpsPSLList a.q).length-i.val)=(lpsPSLList a.q).length by have h:=i.isLt;omega,Nat.mod_self]
def span {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (n:ℕ) (i:LPSSparseGroupIndex a.q) (h:i.val+n≤(lpsPSLList a.q).length):List Bool:=
 (List.ofFn fun k:Fin n=>words a g rs (lpsPSLList a.q).length
  ⟨i.val+k.val,by have hk:=k.isLt;omega⟩).reverse.flatten
theorem result_suffix_eq_span {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (n:ℕ) (i:LPSSparseGroupIndex a.q) (suffix:List Bool) (h:i.val+n≤(lpsPSLList a.q).length):
 (result a g rs n i suffix).2=span a g rs n i h++suffix:=by
 induction n generalizing i suffix with
 | zero=>simp [result_zero,span]
 | succ n ih=>
  by_cases hn:n=0
  · subst n
    simp [result_succ,result_zero,span,List.ofFn_succ]
  · have hv:(LPSLexicographicCounter.indexNext a.q i).val=i.val+1:=by
     rw [LPSLexicographicCounter.indexNext_val,Nat.mod_eq_of_lt (by omega)]
    have ht:(LPSLexicographicCounter.indexNext a.q i).val+n≤(lpsPSLList a.q).length:=by rw [hv];omega
    rw [result_succ,ih _ _ ht]
    have hf:(List.ofFn fun k:Fin n=>words a g rs (lpsPSLList a.q).length
      ⟨(LPSLexicographicCounter.indexNext a.q i).val+k.val,by have hk:=k.isLt;omega⟩)=
     (List.ofFn fun k:Fin n=>words a g rs (lpsPSLList a.q).length
      ⟨i.val+k.succ.val,by have hk:=k.isLt;omega⟩):=by
     congr 1
     funext k
     congr 1
     apply Fin.ext
     simp only [Fin.val_succ,hv]
     omega
    simp only [span,List.ofFn_succ,List.reverse_cons,List.flatten_append,List.flatten_cons,List.flatten_nil,
     List.append_nil]
    rw [hf]
    simp only [Fin.val_zero,Nat.add_zero,List.append_assoc]
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
open LPSSparseEmitterRow
def zero {p:ℕ} (a:LPSResiduePrime p):LPSSparseGroupIndex a.q:=
 ⟨0,Nat.zero_lt_of_lt (lpsPSLIndexOne a.q).isLt⟩
def blockWords {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):List Bool:=
 (List.ofFn fun i:LPSSparseGroupIndex a.q=>words a g rs (lpsPSLList a.q).length i).reverse.flatten
theorem span_zero {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D))):
 span a g rs (lpsPSLList a.q).length (zero a) (by simp [zero])=blockWords a g rs:=by
 simp only [span,zero,Nat.zero_add,Fin.eta,blockWords]
noncomputable def zeroExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (rs:List (List (EntrySpec D)))
 (suffix:List Bool):
 EvalsToInTime (TM2.step (FlagLoop.machine (body g rs)).program) ((FlagLoop.machine (body g rs)).init (payload a (zero a,suffix)))
 (some ((FlagLoop.machine (body g rs)).halt (payload a (zero a,blockWords a g rs++suffix))))
 ((time g rs).eval (payload a (zero a,suffix)).length):=by
 have h:=exec a g rs (zero a) suffix
 have hi:(result a g rs ((lpsPSLList a.q).length-(zero a).val) (zero a) suffix).1=zero a:=by
  apply Fin.ext
  exact result_final_index a g rs (zero a) suffix
 have ht:=result_suffix_eq_span a g rs (lpsPSLList a.q).length (zero a) suffix (by simp [zero])
 rw [span_zero] at ht
 have he:result a g rs ((lpsPSLList a.q).length-(zero a).val) (zero a) suffix=
  (zero a,blockWords a g rs++suffix):=by
  apply Prod.ext
  · exact hi
  · simpa only [zero,Nat.sub_zero] using ht
 rw [he] at h
 exact h
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterBlock
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterChain
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open LPSSparseEmitterRow
open scoped MatrixGroups
def words {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p):List (List (List (EntrySpec D)))→List Bool
 | []=>[]
 | b::bs=>words a g bs++LPSSparseEmitterBlock.blockWords a g b
def machine {p D:ℕ} (g:Fin D→LPSGeneratorIndex p):List (List (List (EntrySpec D)))→Machine
 | []=>MatrixListQuery.identityMachine
 | b::bs=>Composition.machine (FlagLoop.machine (LPSSparseEmitterBlock.body g b)) (machine g bs)
noncomputable def time {p D:ℕ} (g:Fin D→LPSGeneratorIndex p):List (List (List (EntrySpec D)))→Polynomial ℕ
 | []=>Polynomial.C 4*Polynomial.X+Polynomial.C 4
 | b::bs=>Composition.timePolynomial (FlagLoop.machine (LPSSparseEmitterBlock.body g b)) (LPSSparseEmitterBlock.time g b) (time g bs)
noncomputable def exec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))) (suffix:List Bool):
 EvalsToInTime (TM2.step (machine g bs).program) ((machine g bs).init (LPSSparseEmitterBlock.payload a (LPSSparseEmitterBlock.zero a,suffix)))
 (some ((machine g bs).halt (LPSSparseEmitterBlock.payload a (LPSSparseEmitterBlock.zero a,words a g bs++suffix))))
 ((time g bs).eval (LPSSparseEmitterBlock.payload a (LPSSparseEmitterBlock.zero a,suffix)).length):=by
 induction bs generalizing suffix with
 | nil=>
  have hm:machine g ([]:List (List (List (EntrySpec D))))=MatrixListQuery.identityMachine:=rfl
  rw [hm]
  simpa only [time,words,List.nil_append,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
   using MatrixListQuery.identityExec (LPSSparseEmitterBlock.payload a (LPSSparseEmitterBlock.zero a,suffix))
 | cons b bs ih=>
  have hm:machine g (b::bs)=Composition.machine (FlagLoop.machine (LPSSparseEmitterBlock.body g b)) (machine g bs):=rfl
  rw [hm]
  have h:=RetainedFieldComputation.composeRuns (FlagLoop.machine (LPSSparseEmitterBlock.body g b)) (machine g bs)
   _ _ _ (LPSSparseEmitterBlock.time g b) (time g bs) (LPSSparseEmitterBlock.zeroExec a g b suffix)
   (ih (LPSSparseEmitterBlock.blockWords a g b++suffix))
  simpa only [time,words,LPSSparseEmitterBlock.payload,List.append_assoc] using h
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterChain
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterInitializer
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_2bf7a625d3_397:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def count:=RetainedFieldComputation.retainedMarked LPSSparseEmitterCardinality.machine
noncomputable def countTime:=RetainedFieldComputation.retainedMarkedTime LPSSparseEmitterCardinality.machine LPSSparseEmitterCardinality.time
noncomputable def countExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step count.program) (count.init (unary a.q))
 (some (count.halt (stream [(lpsPSLList a.q).length]++unary a.q))) (countTime.eval (unary a.q).length):=by
 have hr:raw [(lpsPSLList a.q).length]=unary (lpsPSLList a.q).length:=by simpa only [stream,List.nil_append] using raw_append_last [] (lpsPSLList a.q).length
 have hb:=LPSSparseEmitterCardinality.exec ⟨a.q,a.prime⟩
 change EvalsToInTime _ _ (some (LPSSparseEmitterCardinality.machine.halt (unary (lpsPSLList a.q).length))) _ at hb
 rw [←hr] at hb
 exact RetainedFieldComputation.retainedMarkedExec LPSSparseEmitterCardinality.machine _ [(lpsPSLList a.q).length] (by simp) LPSSparseEmitterCardinality.time hb
def marked:=Composition.machine count BitDelimiter.machine
noncomputable def markedTime:=Composition.timePolynomial count countTime (Polynomial.C 2*Polynomial.X+Polynomial.C 3)
noncomputable def markedExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step marked.program) (marked.init (unary a.q))
 (some (marked.halt (stream [(lpsPSLList a.q).length,a.q]))) (markedTime.eval (unary a.q).length):=by
 have hd:=BitDelimiter.exec (stream [(lpsPSLList a.q).length]++unary a.q)
 have he:(stream [(lpsPSLList a.q).length]++unary a.q)++[false]=stream [(lpsPSLList a.q).length,a.q]:=by simp [stream,List.append_assoc]
 rw [he] at hd
 exact RetainedFieldComputation.composeRuns count BitDelimiter.machine _ _ _ countTime (Polynomial.C 2*Polynomial.X+Polynomial.C 3)
  (countExec a) (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using hd)
def withZero:=Composition.machine marked (FixedLiteral.prefixMachine (stream [0]))
noncomputable def withZeroTime:=Composition.timePolynomial marked markedTime (FixedLiteral.prefixTime (stream [0]))
noncomputable def withZeroExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step withZero.program) (withZero.init (unary a.q))
 (some (withZero.halt (stream [0,(lpsPSLList a.q).length,a.q]))) (withZeroTime.eval (unary a.q).length):=by
 have hz:=FixedLiteral.prefixExec (stream [0]) (stream [(lpsPSLList a.q).length,a.q])
 rw [←MatrixListQuery.stream_append] at hz
 exact RetainedFieldComputation.composeRuns marked (FixedLiteral.prefixMachine (stream [0])) _ _ _ markedTime (FixedLiteral.prefixTime (stream [0])) (markedExec a) hz
def machine:=Composition.machine withZero SparseEmitterSwap.machine
noncomputable def time:=Composition.timePolynomial withZero withZeroTime SparseEmitterSwap.time
noncomputable def exec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
 (some (machine.halt (LPSSparseEmitterBlock.payload a (LPSSparseEmitterBlock.zero a,[])))) (time.eval (unary a.q).length):=by
 have h:=RetainedFieldComputation.composeRuns withZero SparseEmitterSwap.machine _ _ _ withZeroTime SparseEmitterSwap.time
  (withZeroExec a) (SparseEmitterSwap.exec 0 (lpsPSLList a.q).length a.q)
 have hm:machine=Composition.machine withZero SparseEmitterSwap.machine:=rfl
 rw [hm]
 simpa only [time,LPSSparseEmitterBlock.payload,LPSSparseEmitterBlock.zero,List.append_nil] using h
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterInitializer
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFinalize
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_2bf7a625d3_441:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def mask (k:Fin 3):Bool:=decide (k.val=0)
def project:=PrefixProjection.prefixMachine 2 mask
noncomputable def projectExec (N i q:ℕ) (suffix:List Bool):
 EvalsToInTime (TM2.step project.program) (project.init (stream [N,i,q]++suffix))
 (some (project.halt (unary N))) (PrefixProjection.time.eval (stream [N,i,q]++suffix).length):=by
 have hf:fields 2 mask 0 [N,i,q]=[N]:=by simp [fields,maskAt,mask]
 have hr:raw [N]=unary N:=by simpa only [stream,List.nil_append] using raw_append_last [] N
 have h:=PrefixProjection.polyExec 2 mask [N,i,q] (by rfl) suffix
 rw [hf,hr] at h
 exact h
def counted (C:ℕ):=Composition.machine project (SparseEmitterOffset.multiply C)
noncomputable def countedTime (C:ℕ):=Composition.timePolynomial project PrefixProjection.time (SparseEmitterOffset.multiplyTime C)
noncomputable def countedExec (C N i q:ℕ) (suffix:List Bool):
 EvalsToInTime (TM2.step (counted C).program) ((counted C).init (stream [N,i,q]++suffix))
 (some ((counted C).halt (raw [C*N]))) ((countedTime C).eval (stream [N,i,q]++suffix).length):=by
 have hr:raw [C*N]=unary (C*N):=by simpa only [stream,List.nil_append] using raw_append_last [] (C*N)
 rw [hr]
 exact RetainedFieldComputation.composeRuns project (SparseEmitterOffset.multiply C) _ _ _ PrefixProjection.time (SparseEmitterOffset.multiplyTime C)
  (projectExec N i q suffix) (SparseEmitterOffset.multiplyExec C N)
def retained (C:ℕ):=RetainedFieldComputation.retainedMarked (counted C)
noncomputable def retainedTime (C:ℕ):=RetainedFieldComputation.retainedMarkedTime (counted C) (countedTime C)
noncomputable def retainedExec (C N i q:ℕ) (suffix:List Bool):
 EvalsToInTime (TM2.step (retained C).program) ((retained C).init (stream [N,i,q]++suffix))
 (some ((retained C).halt (stream [C*N,N,i,q]++suffix))) ((retainedTime C).eval (stream [N,i,q]++suffix).length):=by
 have h:=RetainedFieldComputation.retainedMarkedExec (counted C) _ [C*N] (by simp) (countedTime C) (countedExec C N i q suffix)
 rw [←List.append_assoc,←MatrixListQuery.stream_append] at h
 exact h
def machine (C:ℕ):=Composition.machine (retained C) (SparseEmitterReorder.remove 1)
noncomputable def time (C:ℕ):=Composition.timePolynomial (retained C) (retainedTime C) SparseEmitterReorder.removeTime
noncomputable def exec (C N i q:ℕ) (suffix:List Bool):
 EvalsToInTime (TM2.step (machine C).program) ((machine C).init (stream [N,i,q]++suffix))
 (some ((machine C).halt (stream [C*N]++suffix))) ((time C).eval (stream [N,i,q]++suffix).length):=
 RetainedFieldComputation.composeRuns (retained C) (SparseEmitterReorder.remove 1) _ _ _ (retainedTime C) SparseEmitterReorder.removeTime
  (retainedExec C N i q suffix) (SparseEmitterReorder.removeExec 1 [C*N] N i q suffix (by rfl) (by simp))
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFinalize
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
open LPSSparseEmitterRow
local instance _p2m_local_instance_2bf7a625d3_482:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def rowFactor {D:ℕ} (bs:List (List (List (EntrySpec D)))):ℕ:=(bs.map List.length).sum
def output {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):List Bool:=
 stream [rowFactor bs*(lpsPSLList a.q).length]++LPSSparseEmitterChain.words a g bs
def tail {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):=
 Composition.machine (LPSSparseEmitterChain.machine g bs) (LPSSparseEmitterFinalize.machine (rowFactor bs))
noncomputable def tailTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):=
 Composition.timePolynomial (LPSSparseEmitterChain.machine g bs) (LPSSparseEmitterChain.time g bs) (LPSSparseEmitterFinalize.time (rowFactor bs))
noncomputable def tailExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):
 EvalsToInTime (TM2.step (tail g bs).program) ((tail g bs).init (LPSSparseEmitterBlock.payload a (LPSSparseEmitterBlock.zero a,[])))
 (some ((tail g bs).halt (output a g bs))) ((tailTime g bs).eval (LPSSparseEmitterBlock.payload a (LPSSparseEmitterBlock.zero a,[])).length):=by
 have hc:=LPSSparseEmitterChain.exec a g bs []
 have hf:=LPSSparseEmitterFinalize.exec (rowFactor bs) (lpsPSLList a.q).length 0 a.q (LPSSparseEmitterChain.words a g bs)
 have he:LPSSparseEmitterBlock.payload a (LPSSparseEmitterBlock.zero a,LPSSparseEmitterChain.words a g bs++[])=
  stream [(lpsPSLList a.q).length,0,a.q]++LPSSparseEmitterChain.words a g bs:=by
  simp only [LPSSparseEmitterBlock.payload,LPSSparseEmitterBlock.zero,List.append_nil]
 rw [he] at hc
 exact RetainedFieldComputation.composeRuns (LPSSparseEmitterChain.machine g bs) (LPSSparseEmitterFinalize.machine (rowFactor bs))
  _ _ _ (LPSSparseEmitterChain.time g bs) (LPSSparseEmitterFinalize.time (rowFactor bs)) hc hf
def machine {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):=
 Composition.machine LPSSparseEmitterInitializer.machine (tail g bs)
noncomputable def time {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):=
 Composition.timePolynomial LPSSparseEmitterInitializer.machine LPSSparseEmitterInitializer.time (tailTime g bs)
noncomputable def exec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):
 EvalsToInTime (TM2.step (machine g bs).program) ((machine g bs).init (unary a.q))
 (some ((machine g bs).halt (output a g bs))) ((time g bs).eval (unary a.q).length):=
 RetainedFieldComputation.composeRuns LPSSparseEmitterInitializer.machine (tail g bs) _ _ _ LPSSparseEmitterInitializer.time (tailTime g bs)
  (LPSSparseEmitterInitializer.exec a) (tailExec a g bs)
noncomputable def outputsInTime {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):
 TM2OutputsInTime (machine g bs).toFinTM2 (unary a.q) (some (output a g bs)) ((time g bs).eval (unary a.q).length):=
 Machine.outputsInTime (machine g bs) _ _ _ (exec a g bs)
noncomputable def computableInPolyTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):
 TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>output a g bs) where
 tm:=(machine g bs).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time g bs
 outputsFun:=fun a=>by
  change TM2OutputsInTime (machine g bs).toFinTM2 (List.map id (unary a.q)) (some (List.map id (output a g bs))) ((time g bs).eval (unary a.q).length)
  have h:=outputsInTime a g bs
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def blockTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):Polynomial ℕ:=
 (time g bs).comp (Polynomial.C 2*Polynomial.X)
noncomputable def blockExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):
 EvalsToInTime (TM2.step (machine g bs).program) ((machine g bs).init (unary a.q))
 (some ((machine g bs).halt (output a g bs))) ((blockTime g bs).eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec a g bs
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone (time g bs) (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
noncomputable def blockOutputsInTime {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (bs:List (List (List (EntrySpec D)))):
 TM2OutputsInTime (machine g bs).toFinTM2 (unary a.q) (some (output a g bs)) ((blockTime g bs).eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime (machine g bs) _ _ _ (blockExec a g bs)
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterMachine


