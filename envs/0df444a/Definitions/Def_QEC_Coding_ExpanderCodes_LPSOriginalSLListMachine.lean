-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSLListMachine
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalSLListMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:04:58.155197+00:00
-- url     : https://prove2.me/theorems/65544f0c-cf6f-408f-9c31-c6f5db3c71fd
-- title:
--   LPSOriginal SLList Machine
-- statement:
--   Definitions and structural lemmas for LPSOriginal SLList Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalSLListMachine.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSLexicographicCounter
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRetainedPrefixQueries
import Definitions.Def_QEC_Coding_BitTuring_UnaryCoordinatesCollector
import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixReverseDrop
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_fields_all
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_ordinal_lt
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_ordinal_wrap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSLexicographicCounter_rawTuples_filterMap
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
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
theorem reverse_raw_header (q a b c d:ℕ):
 (raw [q,d,c,b,a]).reverse=raw [a,b,c,d,q]:=by
 have h0:=raw_append_last [q,d,c,b] a
 have h1:=raw_append_last [a,b,c,d] q
 change (raw ([q,d,c,b]++[a])).reverse=raw ([a,b,c,d]++[q])
 rw [h0,h1]
 simp [stream,unary,List.reverse_append,List.reverse_cons,List.append_assoc]
def body:=Composition.machine BitReverse.machine
 (Composition.machine BitDelimiter.machine DeterminantPredicate.predicateMachine)
def queryMachine:=RetainedInput.machine
 (Composition.machine (PrefixProjection.prefixMachine 4 (PrefixProjection.allMask 4)) body)
noncomputable def time:Polynomial ℕ:=DeterminantPredicate.predicateTime+Polynomial.C 30*(Polynomial.X+1)
def flag (q:ℕ) (x:LPSLexicographicCounter.Tuple q):Bool:=
 decide ((lpsEntryMatrix q x.1 x.2.1 x.2.2.1 x.2.2.2).det=1)
noncomputable def exec (q:ℕ) (hq:1<q) (x:LPSLexicographicCounter.Tuple q×List Bool):
 EvalsToInTime (TM2.step queryMachine.program) (queryMachine.init (LPSLexicographicCounter.input q x))
  (some (queryMachine.halt (flag q x.1::LPSLexicographicCounter.input q x)))
  (time.eval (LPSLexicographicCounter.input q x).length):=by
 let xs:=[q,x.1.2.2.2.val,x.1.2.2.1.val,x.1.2.1.val,x.1.1.val]
 let ys:=[x.1.1.val,x.1.2.1.val,x.1.2.2.1.val,x.1.2.2.2.val,q]
 have hp:=PrefixProjection.polyExec 4 (PrefixProjection.allMask 4) xs (by rfl) x.2
 rw [PrefixProjection.fields_all] at hp
 have hb:=BitReverse.exec (raw xs)
 have hre:(raw xs).reverse=raw ys:=reverse_raw_header _ _ _ _ _
 rw [hre] at hb
 have hd:=BitDelimiter.exec (raw ys)
 rw [MatrixListQuery.delimiter_raw ys (by simp [ys])] at hd
 have ha:=LPSSLDeterminantMachine.sourceExec q hq x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2
 change EvalsToInTime _ _ (some (DeterminantPredicate.predicateMachine.halt [flag q x.1]))
  (DeterminantPredicate.predicateTime.eval (stream ys).length) at ha
 have hc:=Composition.executes BitDelimiter.machine DeterminantPredicate.predicateMachine _ _ _ _ _ hd ha
 have hbc:=Composition.executes BitReverse.machine
  (Composition.machine BitDelimiter.machine DeterminantPredicate.predicateMachine) _ _ _ _ _ hb hc
 have hpc:=Composition.executes (PrefixProjection.prefixMachine 4 (PrefixProjection.allMask 4)) body _ _ _ _ _ hp hbc
 have hr:=RetainedInput.executes
  (Composition.machine (PrefixProjection.prefixMachine 4 (PrefixProjection.allMask 4)) body) _ _ _ hpc
 refine {hr with steps_le_m:=hr.steps_le_m.trans ?_}
 have hy:(stream ys).length=(stream xs).length:=by
  simp only [xs,ys,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
 have hL:(stream xs).length≤(stream xs++x.2).length:=by simp
 have hyL:(stream ys).length≤(stream xs++x.2).length:=by omega
 have hpmono:=Composition.polynomial_eval_monotone DeterminantPredicate.predicateTime hyL
 simp only [List.length_append] at hpmono
 have hxr:=raw_length_le xs
 have hyr:=raw_length_le ys
 change _≤time.eval (stream xs++x.2).length
 simp only [PrefixProjection.time,time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,Polynomial.eval_one,List.length_cons,List.length_nil,List.length_append]
 omega
end QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
def machine:=Composition.machine QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.queryMachine
 (Composition.machine (QEC.Coding.BitTuring.UnaryArithmetic.CoordinatesCollector.machine 4) (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3))
def accumulated (q:ℕ) (x:LPSLexicographicCounter.Tuple q) (s:List Bool):List Bool:=
 (if QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.flag q x then stream (LPSLexicographicCounter.coords x) else [])++s
noncomputable def time:Polynomial ℕ:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.time+Polynomial.C 200*(Polynomial.X+1)
noncomputable def exec (q:ℕ) (hq:1<q) (x:LPSLexicographicCounter.Tuple q×List Bool):
 EvalsToInTime (TM2.step machine.program) (machine.init (LPSLexicographicCounter.input q x))
  (some (machine.halt (LPSLexicographicCounter.overflow x.1::LPSLexicographicCounter.input q (LPSLexicographicCounter.next x.1,accumulated q x.1 x.2))))
  (time.eval (LPSLexicographicCounter.input q x).length):=by
 have hqexec:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.exec q hq x
 have hc:=QEC.Coding.BitTuring.UnaryArithmetic.CoordinatesCollector.polyExec 4 q (LPSLexicographicCounter.coords x.1) (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.flag q x.1) x.2 (by rfl) (by decide)
 have he:QEC.Coding.BitTuring.UnaryArithmetic.CoordinatesCollector.output q (LPSLexicographicCounter.coords x.1) (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.flag q x.1) x.2=
  LPSLexicographicCounter.input q (x.1,accumulated q x.1 x.2):=by
  simp only [QEC.Coding.BitTuring.UnaryArithmetic.CoordinatesCollector.output,LPSLexicographicCounter.input,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload,accumulated,List.append_assoc]
 rw [he] at hc
 have hr:=LPSLexicographicCounter.exec q (x.1,accumulated q x.1 x.2)
 have hcr:=Composition.executes (QEC.Coding.BitTuring.UnaryArithmetic.CoordinatesCollector.machine 4) (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3) _ _ _ _ _ hc hr
 have h:=Composition.executes QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.queryMachine
  (Composition.machine (QEC.Coding.BitTuring.UnaryArithmetic.CoordinatesCollector.machine 4) (QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.machine 3)) _ _ _ _ _ hqexec hcr
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hl:(stream (LPSLexicographicCounter.coords x.1)).length≤(LPSLexicographicCounter.input q x).length:=by
  simp only [LPSLexicographicCounter.input,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload,stream,List.length_append,List.length_cons,unary_length];omega
 have hid:(stream (q::LPSLexicographicCounter.coords x.1)++x.2).length=(LPSLexicographicCounter.input q x).length:=rfl
 rw [←hid] at hl
 have hrow:(stream (LPSLexicographicCounter.coords x.1)).length≤
  (stream (q::LPSLexicographicCounter.coords x.1)).length:=by
  simp only [stream,List.length_append,List.length_cons,unary_length];omega
 have ho:(LPSLexicographicCounter.input q (x.1,accumulated q x.1 x.2)).length≤2*(LPSLexicographicCounter.input q x).length:=by
  change (stream (q::LPSLexicographicCounter.coords x.1)++accumulated q x.1 x.2).length≤
   2*(stream (q::LPSLexicographicCounter.coords x.1)++x.2).length
  simp only [accumulated,List.length_append]
  cases QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.flag q x.1 <;> simp <;> omega
 simp only [time,QEC.Coding.BitTuring.UnaryArithmetic.CoordinatesCollector.time,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,Polynomial.eval_one,List.length_cons]
 change _≤QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.time.eval (LPSLexicographicCounter.input q x).length+200*((LPSLexicographicCounter.input q x).length+1)
 change _≤_ at ho
 rw [hid]
 omega
end QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
def machine:=FlagLoop.machine QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.machine
def rowBound (q:ℕ):ℕ:=4*(q+1)
def uniformSize (q A:ℕ):ℕ:=5*(q+1)+A
noncomputable def callBudget (q A:ℕ):ℕ:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.time.eval (uniformSize q A)+2*uniformSize q A+4
def collected (q:ℕ):ℕ→LPSLexicographicCounter.Tuple q→List Bool→List Bool
 | 0,_,s=>s
 | m+1,x,s=>collected q m (LPSLexicographicCounter.next x) (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.accumulated q x s)
def zeroTuple (q:ℕ) (hq:0<q):LPSLexicographicCounter.Tuple q:=(⟨0,hq⟩,⟨0,hq⟩,⟨0,hq⟩,⟨0,hq⟩)
theorem zero_ordinal (q:ℕ) (hq:0<q):LPSLexicographicCounter.ordinal (zeroTuple q hq)=0:=by
 simp [zeroTuple,LPSLexicographicCounter.ordinal,LPSLexicographicCounter.coords,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.rank]
theorem wrap_zero (q:ℕ) (hq:0<q) (x:LPSLexicographicCounter.Tuple q) (hf:LPSLexicographicCounter.overflow x=true):
 LPSLexicographicCounter.next x=zeroTuple q hq:=by
 apply LPSLexicographicCounter.ordinal_injective q
 rw [LPSLexicographicCounter.ordinal_wrap x hf,zero_ordinal]
theorem row_length_le (q:ℕ) (x:LPSLexicographicCounter.Tuple q):(stream (LPSLexicographicCounter.coords x)).length≤rowBound q:=by
 have h:=MatrixListQuery.stream_length_bound q (LPSLexicographicCounter.coords x) (LPSLexicographicCounter.coords_lt x)
 simpa only [rowBound,LPSLexicographicCounter.coords,List.length_cons,List.length_nil] using h
theorem accumulated_length_le (q:ℕ) (x:LPSLexicographicCounter.Tuple q) (s:List Bool):
 (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.accumulated q x s).length≤ s.length+rowBound q:=by
 have h:=row_length_le q x
 simp only [QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.accumulated,List.length_append]
 cases hf:QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.flag q x <;>
  simp only [Bool.false_eq_true,↓reduceIte,List.length_nil] <;> omega
theorem input_length_le (q A:ℕ) (x:LPSLexicographicCounter.Tuple q) (s:List Bool) (hs:s.length≤A):
 (LPSLexicographicCounter.input q (x,s)).length≤uniformSize q A:=by
 have h:=QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.header_length_le 3 q (LPSLexicographicCounter.coords x) (by rfl) (LPSLexicographicCounter.coords_lt x)
 change (stream (q::LPSLexicographicCounter.coords x)++s).length≤uniformSize q A
 simp only [List.length_append,uniformSize] at *
 omega
noncomputable def invocationExec (q A:ℕ) (hq:1<q) (x:LPSLexicographicCounter.Tuple q) (s:List Bool)
 (hs:s.length+rowBound q≤A):
 EvalsToInTime (TM2.step machine.program) (machine.init (LPSLexicographicCounter.input q (x,s)))
  (some (if LPSLexicographicCounter.overflow x then machine.halt (LPSLexicographicCounter.input q (LPSLexicographicCounter.next x,QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.accumulated q x s))
   else machine.init (LPSLexicographicCounter.input q (LPSLexicographicCounter.next x,QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.accumulated q x s)))) (callBudget q A):=by
 have hb:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.exec q hq (x,s)
 have h:=FlagLoop.invocationExec QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.machine
  (by simp [QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.machine,Composition.machine]) _ _ _ _ hb
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hi:=input_length_le q A x s (by omega)
 have ha:=accumulated_length_le q x s
 have ho:=input_length_le q A (LPSLexicographicCounter.next x) (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.accumulated q x s) (by omega)
 have ht:=Composition.polynomial_eval_monotone QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.time hi
 dsimp only at ht
 simp only [callBudget]
 omega
noncomputable def traverseAux (q A m:ℕ) (hq:1<q) (x:LPSLexicographicCounter.Tuple q) (s:List Bool)
 (hr:LPSLexicographicCounter.ordinal x+(m+1)=q^4) (hs:s.length+(m+1)*rowBound q≤A):
 EvalsToInTime (TM2.step machine.program) (machine.init (LPSLexicographicCounter.input q (x,s)))
  (some (machine.halt (LPSLexicographicCounter.input q (zeroTuple q (by omega),collected q (m+1) x s))))
  ((m+1)*callBudget q A):=by
 induction m generalizing x s with
 |zero=>
  have hf:LPSLexicographicCounter.overflow x=true:=(LPSLexicographicCounter.overflow_iff_last x).mpr (by simpa only [Nat.zero_add] using hr)
  have hw:=wrap_zero q (by omega) x hf
  have h:=invocationExec q A hq x s (by simpa only [Nat.zero_add,Nat.one_mul] using hs)
  simpa only [hf,↓reduceIte,hw,collected,Nat.zero_add,Nat.one_mul] using h
 |succ m ih=>
  have hf:LPSLexicographicCounter.overflow x=false:=by
   cases he:LPSLexicographicCounter.overflow x with
   |false=>rfl
   |true=>have hl:=(LPSLexicographicCounter.overflow_iff_last x).mp he;omega
  have hrn:=LPSLexicographicCounter.ordinal_next x hf
  have ha:=accumulated_length_le q x s
  have htail:=(ih (LPSLexicographicCounter.next x) (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.accumulated q x s)
   (by omega) (by simp only [Nat.add_mul,Nat.one_mul] at hs ⊢;omega))
  have h0:=invocationExec q A hq x s (by simp only [Nat.add_mul,Nat.one_mul] at hs;omega)
  rw [hf] at h0
  simp only [Bool.false_eq_true,↓reduceIte] at h0
  have h:=EvalsToInTime.trans (TM2.step machine.program) _ _ _ _ _ h0 htail
  have ht:(m+1)*callBudget q A+callBudget q A=(m+1+1)*callBudget q A:=by ring
  rw [ht] at h
  simpa only [collected] using h
noncomputable def traverseExec (q:ℕ) (hq:1<q) (x:LPSLexicographicCounter.Tuple q) (s:List Bool):
 EvalsToInTime (TM2.step machine.program) (machine.init (LPSLexicographicCounter.input q (x,s)))
  (some (machine.halt (LPSLexicographicCounter.input q (zeroTuple q (by omega),collected q (q^4-LPSLexicographicCounter.ordinal x) x s))))
  ((q^4-LPSLexicographicCounter.ordinal x)*callBudget q (s.length+q^4*rowBound q)):=by
 have hl:=LPSLexicographicCounter.ordinal_lt x
 have hc:q^4-LPSLexicographicCounter.ordinal x-1+1=q^4-LPSLexicographicCounter.ordinal x:=by omega
 have hmul:=Nat.mul_le_mul_right (rowBound q) (Nat.sub_le (q^4) (LPSLexicographicCounter.ordinal x))
 have h:=traverseAux q (s.length+q^4*rowBound q) (q^4-LPSLexicographicCounter.ordinal x-1) hq x s
  (by omega) (by rw [hc];omega)
 rwa [hc] at h
noncomputable def sizePolynomial:Polynomial ℕ:=Polynomial.C 10*(Polynomial.X+1)^5
noncomputable def time:Polynomial ℕ:=(Polynomial.X+1)^4*
 (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.time.comp sizePolynomial+Polynomial.C 2*sizePolynomial+Polynomial.C 4)
theorem uniformSize_le (q:ℕ) (x:LPSLexicographicCounter.Tuple q) (s:List Bool):
 uniformSize q (s.length+q^4*rowBound q)≤10*((LPSLexicographicCounter.input q (x,s)).length+1)^5:=by
 let L:=(LPSLexicographicCounter.input q (x,s)).length
 have hq:q+1≤L+1:=by
  dsimp [L];simp only [LPSLexicographicCounter.input,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload,stream,List.length_append,List.length_cons,unary_length];omega
 have hq0:q≤L+1:=by omega
 have hs:s.length≤L:=by dsimp [L];simp only [LPSLexicographicCounter.input,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload,List.length_append];omega
 have hp:q^4≤(L+1)^4:=Nat.pow_le_pow_left hq0 4
 have ht:q^4*(q+1)≤(L+1)^4*(L+1):=Nat.mul_le_mul hp hq
 have hp5:L+1≤(L+1)^5:=le_self_pow (by omega) (by decide)
 rw [←pow_succ] at ht
 change q^4*(q+1)≤(L+1)^5 at ht
 change 5*(q+1)+(s.length+q^4*(4*(q+1)))≤10*(L+1)^5
 rw [show q^4*(4*(q+1))=4*(q^4*(q+1)) by ring]
 omega
noncomputable def traversePolyExec (q:ℕ) (hq:1<q) (x:LPSLexicographicCounter.Tuple q) (s:List Bool):
 EvalsToInTime (TM2.step machine.program) (machine.init (LPSLexicographicCounter.input q (x,s)))
  (some (machine.halt (LPSLexicographicCounter.input q (zeroTuple q (by omega),collected q (q^4-LPSLexicographicCounter.ordinal x) x s))))
  (time.eval (LPSLexicographicCounter.input q (x,s)).length):=by
 have h:=traverseExec q hq x s
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hu:=uniformSize_le q x s
 have ht:=Composition.polynomial_eval_monotone QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.time hu
 dsimp only at ht
 have hq:q≤(LPSLexicographicCounter.input q (x,s)).length+1:=by
  simp only [LPSLexicographicCounter.input,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload,stream,List.length_append,List.length_cons,unary_length];omega
 have hp:q^4≤((LPSLexicographicCounter.input q (x,s)).length+1)^4:=Nat.pow_le_pow_left hq 4
 have hc:q^4-LPSLexicographicCounter.ordinal x≤((LPSLexicographicCounter.input q (x,s)).length+1)^4:=by omega
 simp only [time,sizePolynomial,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,
  Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp,Polynomial.eval_C,callBudget]
 exact Nat.mul_le_mul hc (by omega)
end QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Source
open scoped MatrixGroups
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
def record (q:ℕ) (x:LPSLexicographicCounter.Tuple q):List Bool:=
 if QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.flag q x then stream (LPSLexicographicCounter.coords x) else []
theorem collected_atOrdinal (q m:ℕ) (i:Fin (q^4)) (s:List Bool) (hi:i.val+m≤q^4):
 QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.collected q m (LPSLexicographicCounter.atOrdinal q i) s=
 ((((LPSLexicographicCounter.rawTuples q).drop i.val).take m).reverse.flatMap (record q))++s:=by
 induction m generalizing i s with
 |zero=>simp [QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.collected]
 |succ m ih=>
  have hil:i.val<(LPSLexicographicCounter.rawTuples q).length:=by rw [LPSLexicographicCounter.rawTuples_length];exact i.isLt
  have he:(LPSLexicographicCounter.rawTuples q).drop i.val=LPSLexicographicCounter.atOrdinal q i::(LPSLexicographicCounter.rawTuples q).drop (i.val+1):=by
   simpa only [LPSLexicographicCounter.atOrdinal,List.get_eq_getElem] using List.drop_eq_getElem_cons hil
  rw [he,List.take_succ_cons,List.reverse_cons,List.flatMap_append]
  simp only [List.flatMap_singleton,List.append_assoc]
  cases m with
  |zero=>simp [QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.collected,QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.accumulated,record]
  |succ m=>
   have hnext:i.val+1<q^4:=by omega
   have ht:=ih ⟨i.val+1,hnext⟩ (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Body.accumulated q (LPSLexicographicCounter.atOrdinal q i) s) (by dsimp;omega)
   rw [QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.collected,LPSLexicographicCounter.next_atOrdinal q i hnext,ht]
   rfl
theorem collected_source_order (q:ℕ) (hq:0<q):
 QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.collected q (q^4) (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zeroTuple q hq) []=
 (LPSLexicographicCounter.rawTuples q).reverse.flatMap (record q):=by
 have hp:0<q^4:=pow_pos hq _
 have hx:LPSLexicographicCounter.atOrdinal q ⟨0,hp⟩=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zeroTuple q hq:=by
  apply LPSLexicographicCounter.ordinal_injective q
  rw [LPSLexicographicCounter.atOrdinal_ordinal,QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zero_ordinal]
 have h:=collected_atOrdinal q (q^4) ⟨0,hp⟩ [] (by dsimp;omega)
 rw [hx] at h
 simp only [List.drop_zero,List.append_nil] at h
 have ht:(LPSLexicographicCounter.rawTuples q).take (q^4)=LPSLexicographicCounter.rawTuples q:=by
  rw [←LPSLexicographicCounter.rawTuples_length q,List.take_length]
 rwa [ht] at h
theorem reverse_stream_coords (q:ℕ) (x:LPSLexicographicCounter.Tuple q):
 (stream (LPSLexicographicCounter.coords x)).reverse=false::raw [x.1.val,x.2.1.val,x.2.2.1.val,x.2.2.2.val]:=by
 change (stream [x.2.2.2.val,x.2.2.1.val,x.2.1.val,x.1.val]).reverse=
  false::raw ([x.1.val,x.2.1.val,x.2.2.1.val]++[x.2.2.2.val])
 rw [raw_append_last]
 simp [stream,unary,List.reverse_append,List.reverse_cons,List.append_assoc]
theorem entry_fields (q:ℕ) (hq:0<q) (x:LPSLexicographicCounter.Tuple q):
 LPSMatrixProductMachine.fields q (lpsEntryMatrix q x.1 x.2.1 x.2.2.1 x.2.2.2)=
 [x.1.val,x.2.1.val,x.2.2.1.val,x.2.2.2.val]:=by
 let :NeZero q:=⟨by omega⟩
 simp [LPSMatrixProductMachine.fields,lpsEntryMatrix,Nat.mod_eq_of_lt x.1.isLt,
  Nat.mod_eq_of_lt x.2.1.isLt,Nat.mod_eq_of_lt x.2.2.1.isLt,Nat.mod_eq_of_lt x.2.2.2.isLt]
theorem records_source (q:ℕ) (hq:0<q) (xs:List (LPSLexicographicCounter.Tuple q)):
 xs.flatMap (fun x=>(record q x).reverse)=
 (xs.filterMap (fun x=>lpsSLMatrixCandidate q x.1 x.2.1 x.2.2.1 x.2.2.2)).flatMap
  (fun A=>false::raw (LPSMatrixProductMachine.fields q A.val)):=by
 induction xs with
 |nil=>rfl
 |cons x xs ih=>
  by_cases hx:(lpsEntryMatrix q x.1 x.2.1 x.2.2.1 x.2.2.2).det=1
  · have hc:lpsSLMatrixCandidate q x.1 x.2.1 x.2.2.1 x.2.2.2=
     some (⟨lpsEntryMatrix q x.1 x.2.1 x.2.2.1 x.2.2.2,hx⟩:SL(2,ZMod q)):=dif_pos hx
    have hr:(record q x).reverse=false::raw (LPSMatrixProductMachine.fields q
     (lpsEntryMatrix q x.1 x.2.1 x.2.2.1 x.2.2.2)):=by
     rw [entry_fields q hq x]
     simp only [record,QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.flag,hx,decide_true,↓reduceIte,reverse_stream_coords]
    simp only [List.flatMap_cons,List.filterMap_cons,hc,hr,ih]
    rfl
  · have hc:lpsSLMatrixCandidate q x.1 x.2.1 x.2.2.1 x.2.2.2=none:=dif_neg hx
    have hr:(record q x).reverse=[]:=by simp [record,QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.flag,hx]
    simpa only [List.flatMap_cons,List.filterMap_cons,hc,hr,List.nil_append] using ih
theorem reversed_collected_source (q:ℕ) (hq:0<q):
 (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.collected q (q^4) (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zeroTuple q hq) []).reverse=
 (lpsSLList q).flatMap (fun A=>false::raw (LPSMatrixProductMachine.fields q A.val)):=by
 rw [collected_source_order q hq]
 rw [List.reverse_flatMap,List.reverse_reverse]
 simp only [Function.comp_def]
 rw [records_source q hq,LPSLexicographicCounter.rawTuples_filterMap]
theorem raw_append_nonempty (xs ys:List ℕ) (hy:ys≠[]):
 raw (xs++ys)=stream xs++raw ys:=by
 have hs:stream ys≠[]:=by
  intro h
  have hl:=congrArg List.length h
  simp only [stream_length,List.length_nil] at hl
  have hn:0<ys.length:=List.length_pos_iff.mpr hy
  omega
 simp only [raw,MatrixListQuery.stream_append,List.dropLast_append_of_ne_nil hs]
theorem prefixed_rows {α:Type} (f:α→List ℕ) (xs:List α)
 (hne:xs≠[]) (hf:∀x∈xs,f x≠[]):
 xs.flatMap (fun x=>false::raw (f x))=false::raw (xs.flatMap f):=by
 induction xs with
 |nil=>exact False.elim (hne rfl)
 |cons a xs ih=>
  have ha:=hf a (by simp)
  cases xs with
  |nil=>simp
  |cons b xs=>
   have ht:=ih (by simp) (fun x hx=>hf x (by simp [hx]))
   have hb:f b≠[]:=hf b (by simp)
   have hn:(b::xs).flatMap f≠[]:=by
    exact List.append_ne_nil_of_left_ne_nil hb _
   rw [List.flatMap_cons,ht]
   rw [show (a::b::xs).flatMap f=f a++(b::xs).flatMap f from rfl,raw_append_nonempty _ _ hn]
   have hd:=MatrixListQuery.delimiter_raw (f a) ha
   rw [←hd]
   simp only [List.cons_append,List.append_assoc,List.nil_append]
theorem raw_source_output (q:ℕ) (hq:0<q):
 (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.collected q (q^4) (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zeroTuple q hq) []).reverse.drop 1=
 raw ((lpsSLList q).flatMap (fun A=>LPSMatrixProductMachine.fields q A.val)):=by
 rw [reversed_collected_source q hq]
 cases hs:lpsSLList q with
 |nil=>simp [raw,stream]
 |cons A As=>
  have h:=prefixed_rows (fun A:SL(2,ZMod q)=>LPSMatrixProductMachine.fields q A.val) (A::As)
   (by simp) (by intros;simp [LPSMatrixProductMachine.fields])
  rw [h]
  simp
end QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Source
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
def initializer:=Composition.machine (FixedLiteral.prefixMachine (List.replicate 5 false)) BitReverse.machine
def machine:=Composition.machine initializer
 (Composition.machine QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.machine (QEC.Coding.BitTuring.UnaryArithmetic.PrefixReverseDrop.machine 5))
def output (q:ℕ):List Bool:=raw ((lpsSLList q).flatMap (fun A=>LPSMatrixProductMachine.fields q A.val))
noncomputable def time:Polynomial ℕ:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.time.comp (Polynomial.X+Polynomial.C 5)+
 Polynomial.C 100*(Polynomial.X+Polynomial.C 6)^5
theorem zero_header (q:ℕ) (hq:0<q):
 LPSLexicographicCounter.input q (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zeroTuple q hq,[])=unary q++List.replicate 5 false:=by
 simp [LPSLexicographicCounter.input,QEC.Coding.BitTuring.UnaryArithmetic.RippleCounter.payload,LPSLexicographicCounter.coords,QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zeroTuple,stream,unary]
noncomputable def initializerExec (q:ℕ) (hq:0<q):
 EvalsToInTime (TM2.step initializer.program) (initializer.init (unary q))
  (some (initializer.halt (LPSLexicographicCounter.input q (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zeroTuple q hq,[])))) (7*q+36):=by
 have hp:=FixedLiteral.prefixExec (List.replicate 5 false) (unary q)
 have hr:=BitReverse.exec (List.replicate 5 false++unary q)
 have h:=Composition.executes (FixedLiteral.prefixMachine (List.replicate 5 false)) BitReverse.machine _ _ _ _ _ hp hr
 have he:(List.replicate 5 false++unary q).reverse=LPSLexicographicCounter.input q (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zeroTuple q hq,[]):=by
  rw [zero_header]
  simp [unary]
 rw [he] at h
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [FixedLiteral.prefixTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,List.length_append,List.length_replicate,unary_length]
 omega
noncomputable def exec (q:ℕ) (hq:1<q):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary q))
  (some (machine.halt (output q))) (time.eval (unary q).length):=by
 let z:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zeroTuple q (by omega)
 let acc:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.collected q (q^4) z []
 have hi:=initializerExec q (by omega)
 have hl:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.traversePolyExec q hq z []
 rw [QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.zero_ordinal] at hl
 simp only [Nat.sub_zero] at hl
 -- The exact original list source identity, not a caller-supplied result.
 have hsource:acc.reverse.drop 1=output q:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Source.raw_source_output q (by omega)
 -- Apply the source identity to the actual finalizer endpoint.
 have hf':=QEC.Coding.BitTuring.UnaryArithmetic.PrefixReverseDrop.exec 5 (q::LPSLexicographicCounter.coords z) acc (by simp [LPSLexicographicCounter.coords])
 rw [hsource] at hf'
 have hlf:=Composition.executes QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.machine (QEC.Coding.BitTuring.UnaryArithmetic.PrefixReverseDrop.machine 5) _ _ _ _ _ hl hf'
 have h:=Composition.executes initializer
  (Composition.machine QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.machine (QEC.Coding.BitTuring.UnaryArithmetic.PrefixReverseDrop.machine 5)) _ _ _ _ _ hi hlf
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hc:acc.length≤q^4*QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.rowBound q:=by
  -- Each accepted original candidate contributes at most its four canonical unary fields.
  have hrows:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Source.collected_source_order q (by omega)
  change acc=(LPSLexicographicCounter.rawTuples q).reverse.flatMap (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Source.record q) at hrows
  rw [hrows]
  have hh:∀xs:List (LPSLexicographicCounter.Tuple q),
   (xs.flatMap (QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Source.record q)).length≤xs.length*QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.rowBound q:=by
   intro xs
   induction xs with
   |nil=>simp
   |cons x xs ih=>
    have hx:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.row_length_le q x
    have hr:(QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Source.record q x).length≤QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.rowBound q:=by
     simp only [QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Source.record]
     cases QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Query.flag q x <;>
      simp only [Bool.false_eq_true,↓reduceIte,List.length_nil] <;> omega
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
  have hb:=hh (LPSLexicographicCounter.rawTuples q).reverse
  simpa only [List.length_reverse,LPSLexicographicCounter.rawTuples_length] using hb
 have hout: (LPSLexicographicCounter.input q (z,acc)).length≤QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.uniformSize q (q^4*QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.rowBound q):=
  QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.input_length_le q _ z acc hc
 have hhead:(LPSLexicographicCounter.input q (z,[])).length=q+5:=by
  rw [zero_header];simp only [List.length_append,unary_length,List.length_replicate]
 have hu:=QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.uniformSize_le q z []
 simp only [List.length_nil,Nat.zero_add,hhead] at hu
 have hp:q+6≤(q+6)^5:=le_self_pow (by omega) (by decide)
 have hout':(stream (q::LPSLexicographicCounter.coords z)++acc).length≤10*(q+6)^5:=hout.trans hu
 change (stream (q::LPSLexicographicCounter.coords z)++acc).length+2+
  (2*(stream (q::LPSLexicographicCounter.coords z)++acc).length+2)+
  QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine.Loop.time.eval (LPSLexicographicCounter.input q (z,[])).length+
  (2*(LPSLexicographicCounter.input q (z,[])).length+2)+(7*q+36)≤time.eval (unary q).length
 simp only [time,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_C,
  Polynomial.eval_mul,Polynomial.eval_pow,unary_length,hhead]
 omega
abbrev Input:={q:ℕ//1<q}
def input (q:Input):List Bool:=unary q.val
noncomputable def outputsInTime (q:Input):
 TM2OutputsInTime machine.toFinTM2 (input q) (some (output q.val)) (time.eval (input q).length):=
 Machine.outputsInTime machine _ _ _ (exec q.val q.property)
noncomputable def computableInPolyTime:
 TM2ComputableInPolyTime input id (fun q:Input=>output q.val) where
 tm:=machine.toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time
 outputsFun:=fun q=>by
  change TM2OutputsInTime machine.toFinTM2 (List.map id (input q))
   (some (List.map id (output q.val))) (time.eval (input q).length)
  have h:=outputsInTime q
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
  (some (machine.halt (output a.q))) (time.eval (2*Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec a.q a.prime.one_lt
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 rw [unary_length]
 exact Composition.polynomial_eval_monotone time a.q_le_two_mul_card_psl
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p):
 TM2OutputsInTime machine.toFinTM2 (unary a.q) (some (output a.q))
  (time.eval (2*Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalSLListMachine


