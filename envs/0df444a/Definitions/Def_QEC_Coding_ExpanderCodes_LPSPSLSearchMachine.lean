-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLSearchMachine
-- name    : QEC_Coding_ExpanderCodes_LPSPSLSearchMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:05:09.596206+00:00
-- url     : https://prove2.me/theorems/aee46f82-92f7-4669-a567-42c8b6bc4da8
-- title:
--   LPSPSLSearch Machine
-- statement:
--   Definitions and structural lemmas for LPSPSLSearch Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPSLSearchMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_BooleanSwitch
import Definitions.Def_QEC_Coding_BitTuring_UnarySuffixEmpty
import Definitions.Def_QEC_Coding_BitTuring_UnaryTailProjection
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPSLEqualityMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRetainedPrefixQueries
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_length_le
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_length
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_PrefixProjection_fields_all
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
namespace QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_25ca2d8bb9_19 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
def coords (q:ℕ) (A:SL(2,ZMod q)):List ℕ:=LPSMatrixProductMachine.fields q A.val
def header (q:ℕ) (A:SL(2,ZMod q)):List ℕ:=q::coords q A
def rows (q:ℕ) (R:List SL(2,ZMod q)):List Bool:=stream (R.flatMap (coords q))
def input (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):List Bool:=stream (header q A)++rows q R
def matchFlag (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)):Bool:=
 letI:=lpsPSLDecidableEq q
 decide ((QuotientGroup.mk B:PSL(2,ZMod q))=QuotientGroup.mk A)
theorem reverse_raw_header (q a b c d e f g h:ℕ):
 (raw [q,d,c,b,a,h,g,f,e]).reverse=raw [e,f,g,h,a,b,c,d,q]:=by
 have h0:=raw_append_last [q,d,c,b,a,h,g,f] e
 have h1:=raw_append_last [e,f,g,h,a,b,c,d] q
 change (raw ([q,d,c,b,a,h,g,f]++[e])).reverse=raw ([e,f,g,h,a,b,c,d]++[q])
 rw [h0,h1]
 simp [stream,unary,List.reverse_append,List.reverse_cons,List.append_assoc]
theorem result_reverse (a b c d e f g h q:ℕ):
 PSLComparison.result d c b a h g f e q=PSLComparison.result a b c d e f g h q:=by
 simp only [PSLComparison.result,Bool.and_assoc,Bool.and_comm]
def queryBody:=Composition.machine BitReverse.machine
 (Composition.machine BitDelimiter.machine PSLComparison.predicateMachine)
def queryMachine:=RetainedInput.machine
 (Composition.machine (PrefixProjection.prefixMachine 8 (PrefixProjection.allMask 8)) queryBody)
noncomputable def queryTime:Polynomial ℕ:=PSLComparison.time+Polynomial.C 30*(Polynomial.X+1)
noncomputable def queryExec (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) (s:List Bool):
 EvalsToInTime (TM2.step queryMachine.program)
  (queryMachine.init (stream (header q A++coords q B)++s))
  (some (queryMachine.halt (matchFlag q A B::(stream (header q A++coords q B)++s))))
  (queryTime.eval (stream (header q A++coords q B)++s).length):=by
 let xs:=header q A++coords q B
 let ys:=(LPSMatrixProductMachine.fields q B.val).reverse++(LPSMatrixProductMachine.fields q A.val).reverse++[q]
 have hp:=PrefixProjection.polyExec 8 (PrefixProjection.allMask 8) xs
  (by simp [xs,header,coords,LPSMatrixProductMachine.fields]) s
 rw [PrefixProjection.fields_all] at hp
 have hb:=BitReverse.exec (raw xs)
 have hre:(raw xs).reverse=raw ys:=by
  simpa [xs,ys,header,coords,LPSMatrixProductMachine.fields] using
   reverse_raw_header q (A.val 1 1).val (A.val 1 0).val (A.val 0 1).val (A.val 0 0).val
    (B.val 1 1).val (B.val 1 0).val (B.val 0 1).val (B.val 0 0).val
 rw [hre] at hb
 have hd:=BitDelimiter.exec (raw ys)
 rw [MatrixListQuery.delimiter_raw ys (by simp [ys,LPSMatrixProductMachine.fields])] at hd
 let : NeZero q:=⟨(Fact.out:q.Prime).ne_zero⟩
 have ha:=PSLComparison.polyExec (B.val 1 1).val (B.val 1 0).val (B.val 0 1).val (B.val 0 0).val
  (A.val 1 1).val (A.val 1 0).val (A.val 0 1).val (A.val 0 0).val q
  (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)
 have hflag:PSLComparison.result (B.val 1 1).val (B.val 1 0).val (B.val 0 1).val (B.val 0 0).val
    (A.val 1 1).val (A.val 1 0).val (A.val 0 1).val (A.val 0 0).val q=matchFlag q A B:=by
  rw [result_reverse]
  have hs:=LPSPSLEqualityMachine.result_eq_source q B A
  change [PSLComparison.result (B.val 0 0).val (B.val 0 1).val (B.val 1 0).val (B.val 1 1).val
   (A.val 0 0).val (A.val 0 1).val (A.val 1 0).val (A.val 1 1).val q]=[matchFlag q A B] at hs
  simpa only [List.cons.injEq,and_true] using hs
 rw [hflag] at ha
 change EvalsToInTime _ _ (some (PSLComparison.predicateMachine.halt [matchFlag q A B]))
  (PSLComparison.time.eval (stream ys).length) at ha
 have hc:=Composition.executes BitDelimiter.machine PSLComparison.predicateMachine _ _ _ _ _ hd ha
 have hbc:=Composition.executes BitReverse.machine
  (Composition.machine BitDelimiter.machine PSLComparison.predicateMachine) _ _ _ _ _ hb hc
 have hpc:=Composition.executes (PrefixProjection.prefixMachine 8 (PrefixProjection.allMask 8)) queryBody _ _ _ _ _ hp hbc
 have hr:=RetainedInput.executes
  (Composition.machine (PrefixProjection.prefixMachine 8 (PrefixProjection.allMask 8)) queryBody) _ _ _ hpc
 refine {hr with steps_le_m:=hr.steps_le_m.trans ?_}
 have hy:(stream ys).length=(stream xs).length:=by
  simp only [xs,ys,header,coords,LPSMatrixProductMachine.fields,List.reverse_cons,List.reverse_nil,List.nil_append,
   List.cons_append,List.nil_append,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
 have hpmono:=Composition.polynomial_eval_monotone PSLComparison.time
  (show (stream ys).length≤(stream xs++s).length by rw [hy];simp)
 simp only [List.length_append] at hpmono
 have hxr:=raw_length_le xs
 have hyr:=raw_length_le ys
 change _≤ queryTime.eval (stream xs++s).length
 simp only [PrefixProjection.time,queryTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,Polynomial.eval_one,List.length_cons,List.length_nil,List.length_append]
 omega
end QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
namespace QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_25ca2d8bb9_109 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
theorem rows_cons (q:ℕ) (B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 rows q (B::R)=stream (coords q B)++rows q R:=by
 simp only [rows,List.flatMap_cons,MatrixListQuery.stream_append]
theorem input_cons (q:ℕ) (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 input q A (B::R)=stream (header q A++coords q B)++rows q R:=by
 simp only [input,rows_cons,MatrixListQuery.stream_append,List.append_assoc]
theorem input_tail_le (q:ℕ) (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 (input q A R).length≤(input q A (B::R)).length:=by
 simp only [input,rows_cons,List.length_append]
 omega
theorem rows_cons_nonempty (q:ℕ) (B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 (rows q (B::R)).isEmpty=false:=by
 have hl:0<(rows q (B::R)).length:=by
  simp only [rows_cons,List.length_append,coords,LPSMatrixProductMachine.fields,stream_length,
   List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega
 cases he:rows q (B::R) with
 |nil=>simp [he] at hl
 |cons b bs=>rfl
def keepHead (k:Fin 9):Bool:=decide (k.val<5)
def dropMachine:=QEC.Coding.BitTuring.UnaryArithmetic.TailProjection.machine 8 keepHead
theorem selected_header (q:ℕ) (A B:SL(2,ZMod q)):
 fields 8 keepHead 0 (header q A++coords q B)=header q A:=by
 simp [header,coords,LPSMatrixProductMachine.fields,fields,maskAt,keepHead]
noncomputable def dropExec (q:ℕ) (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step dropMachine.program) (dropMachine.init (input q A (B::R)))
  (some (dropMachine.halt (input q A R))) (6*((input q A (B::R)).length+1)):=by
 have h:=QEC.Coding.BitTuring.UnaryArithmetic.TailProjection.streamExec 8 keepHead (header q A++coords q B)
  (by simp [header,coords,LPSMatrixProductMachine.fields]) (rows q R)
  (by rw [selected_header];simp [header])
 rw [selected_header] at h
 rw [input_cons]
 simp only [QEC.Coding.BitTuring.UnaryArithmetic.TailProjection.time,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] at h
 exact h
def declinedMachine:=Composition.machine dropMachine (FixedLiteral.prefixMachine [false])
def matchDispatch:=QEC.Coding.BitTuring.BooleanSwitch.machine (FixedLiteral.machine [true,true]) declinedMachine
noncomputable def matchDispatchExec (q:ℕ) (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)) (f:Bool):
 EvalsToInTime (TM2.step matchDispatch.program) (matchDispatch.init (f::input q A (B::R)))
  (some (matchDispatch.halt (if f then [true,true] else false::input q A R)))
  (12*(input q A (B::R)).length+20):=by
 cases f with
 |true=>
  have h:=QEC.Coding.BitTuring.BooleanSwitch.execA (FixedLiteral.machine [true,true]) declinedMachine _ _ _
   (FixedLiteral.exec [true,true] (input q A (B::R)))
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  omega
 |false=>
  have hd:=dropExec q A B R
  have hp:=FixedLiteral.prefixExec [false] (input q A R)
  have hc:=Composition.executes dropMachine (FixedLiteral.prefixMachine [false]) _ _ _ _ _ hd hp
  have h:=QEC.Coding.BitTuring.BooleanSwitch.execB (FixedLiteral.machine [true,true]) declinedMachine
   (by change (0:Fin 2)≠1;decide)
   (by simp [declinedMachine,Composition.machine]) _ _ _ hc
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hl:=input_tail_le q A B R
  simp only [FixedLiteral.prefixTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
   Polynomial.eval_X,List.length_cons,List.length_nil]
  omega
def compareMachine:=Composition.machine queryMachine matchDispatch
noncomputable def compareExec (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step compareMachine.program) (compareMachine.init (input q A (B::R)))
  (some (compareMachine.halt (if matchFlag q A B then [true,true] else false::input q A R)))
  (queryTime.eval (input q A (B::R)).length+14*(input q A (B::R)).length+24):=by
 have hq:=queryExec q A B (rows q R)
 rw [←input_cons] at hq
 have hs:=matchDispatchExec q A B R (matchFlag q A B)
 have h:=Composition.executes queryMachine matchDispatch _ _ _ _ _ hq hs
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [List.length_cons]
 omega
def emptyQuery:=RetainedInput.machine (SuffixEmpty.machine 5)
noncomputable def emptyQueryExec (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step emptyQuery.program) (emptyQuery.init (input q A R))
  (some (emptyQuery.halt ((rows q R).isEmpty::input q A R))) (4*(input q A R).length+11):=by
 have h:=RetainedInput.executes (SuffixEmpty.machine 5) _ _ _
  (SuffixEmpty.exec 5 (header q A) (rows q R) (by simp [header,coords,LPSMatrixProductMachine.fields]))
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 change (input q A R).length+3+3*(input q A R).length+2*[((rows q R).isEmpty)].length+6≤ _
 simp only [List.length_cons,List.length_nil]
 omega
def emptyDispatch:=QEC.Coding.BitTuring.BooleanSwitch.machine (FixedLiteral.machine [true,false]) compareMachine
def bodyMachine:=Composition.machine emptyQuery emptyDispatch
noncomputable def bodyTime:Polynomial ℕ:=PSLComparison.time+Polynomial.C 100*(Polynomial.X+1)
noncomputable def bodyEmptyExec (q:ℕ) (A:SL(2,ZMod q)):
 EvalsToInTime (TM2.step bodyMachine.program) (bodyMachine.init (input q A []))
  (some (bodyMachine.halt [true,false])) (bodyTime.eval (input q A []).length):=by
 have he:=emptyQueryExec q A []
 have hd:=QEC.Coding.BitTuring.BooleanSwitch.execA (FixedLiteral.machine [true,false]) compareMachine _ _ _
  (FixedLiteral.exec [true,false] (input q A []))
 change EvalsToInTime _ _ (some (emptyQuery.halt (true::input q A []))) _ at he
 have h:=Composition.executes emptyQuery emptyDispatch _ _ _ _ _ he hd
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [bodyTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,Polynomial.eval_one,List.length_cons]
 omega
noncomputable def bodyConsExec (q:ℕ) [Fact q.Prime] (A B:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step bodyMachine.program) (bodyMachine.init (input q A (B::R)))
  (some (bodyMachine.halt (if matchFlag q A B then [true,true] else false::input q A R)))
  (bodyTime.eval (input q A (B::R)).length):=by
 have he:=emptyQueryExec q A (B::R)
 rw [rows_cons_nonempty] at he
 have hc:=compareExec q A B R
 have hd:=QEC.Coding.BitTuring.BooleanSwitch.execB (FixedLiteral.machine [true,false]) compareMachine
  (by change (0:Fin 2)≠1;decide)
  (by simp [compareMachine,Composition.machine]) _ _ _ hc
 have h:=Composition.executes emptyQuery emptyDispatch _ _ _ _ _ he hd
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [bodyTime,queryTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,Polynomial.eval_one,List.length_cons]
 omega
end QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
namespace QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_25ca2d8bb9_246 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
def searchMachine:=FlagLoop.machine bodyMachine
def found (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):Bool:=R.any (matchFlag q A)
noncomputable def callBudget (L:ℕ):ℕ:=bodyTime.eval L+2*L+4
theorem input_pos (q:ℕ) (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 1≤(input q A R).length:=by
 simp only [input,List.length_append,header,coords,LPSMatrixProductMachine.fields,
  stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
 omega
theorem rows_count_bound (q:ℕ) (R:List SL(2,ZMod q)):R.length≤(rows q R).length:=by
 induction R with
 |nil=>simp [rows,stream]
 |cons B R ih=>
  simp only [List.length_cons,rows_cons,List.length_append]
  have hl:1≤(stream (coords q B)).length:=by
   simp only [coords,LPSMatrixProductMachine.fields,stream_length,
    List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  omega
noncomputable def searchExecAux (q L:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q))
 (hsize:(input q A R).length≤ L) (hpos:1≤ L):
 EvalsToInTime (TM2.step searchMachine.program) (searchMachine.init (input q A R))
  (some (searchMachine.halt [found q A R])) ((R.length+1)*callBudget L):=by
 induction R with
 |nil=>
  have hb:=bodyEmptyExec q A
  have h:=FlagLoop.invocationExec bodyMachine (by simp [bodyMachine,Composition.machine])
   (input q A []) [false] true _ hb
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  have hm:=Composition.polynomial_eval_monotone bodyTime hsize
  dsimp only at hm
  simp only [List.length_cons,List.length_nil,callBudget,Nat.one_mul,Nat.zero_add]
  omega
 |cons B R ih=>
  have hb:=bodyConsExec q A B R
  cases hf:matchFlag q A B with
  |true=>
   rw [hf] at hb
   simp only [found,List.any_cons,hf,Bool.true_or]
   have h:=FlagLoop.invocationExec bodyMachine (by simp [bodyMachine,Composition.machine])
    (input q A (B::R)) [true] true _ hb
   refine {h with steps_le_m:=h.steps_le_m.trans ?_}
   have hm:=Composition.polynomial_eval_monotone bodyTime hsize
   dsimp only at hm
   have h0:bodyTime.eval (input q A (B::R)).length+2*[true].length+4≤ callBudget L:=by
    simp only [List.length_cons,List.length_nil,callBudget];omega
   have hmul:callBudget L≤((B::R).length+1)*callBudget L:=by
    simp only [List.length_cons];nlinarith
   exact h0.trans hmul
  |false=>
   rw [hf] at hb
   have h0:=FlagLoop.invocationExec bodyMachine (by simp [bodyMachine,Composition.machine])
    (input q A (B::R)) (input q A R) false _ hb
   have hs:(input q A R).length≤ L:=(input_tail_le q A B R).trans hsize
   have ht:=ih hs
   have hc:EvalsToInTime (TM2.step searchMachine.program) (searchMachine.init (input q A (B::R)))
     (some (searchMachine.init (input q A R))) (callBudget L):=by
    refine {h0 with steps_le_m:=h0.steps_le_m.trans ?_}
    have hm:=Composition.polynomial_eval_monotone bodyTime hsize
    dsimp only at hm
    simp only [callBudget];omega
   have h:=EvalsToInTime.trans (TM2.step searchMachine.program) _ _ _ _ _ hc ht
   have he:(R.length+1)*callBudget L+callBudget L=((B::R).length+1)*callBudget L:=by
    simp only [List.length_cons];ring
   rw [he] at h
   simpa only [found,List.any_cons,hf,Bool.false_or] using h
noncomputable def searchTime:Polynomial ℕ:=(Polynomial.X+1)*(bodyTime+Polynomial.C 2*Polynomial.X+Polynomial.C 4)
noncomputable def searchExec (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step searchMachine.program) (searchMachine.init (input q A R))
  (some (searchMachine.halt [found q A R])) (searchTime.eval (input q A R).length):=by
 have h:=searchExecAux q (input q A R).length A R (le_refl _) (input_pos q A R)
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hl:R.length≤(input q A R).length:=by
  have hr:=rows_count_bound q R
  simp only [input,List.length_append];omega
 have hm:=Nat.mul_le_mul_right (callBudget (input q A R).length) (Nat.add_le_add_right hl 1)
 simpa only [searchTime,callBudget,Polynomial.eval_mul,Polynomial.eval_add,
  Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one] using hm
def retainedSearchMachine:=RetainedInput.machine searchMachine
noncomputable def retainedSearchTime:Polynomial ℕ:=searchTime+Polynomial.C 3*Polynomial.X+Polynomial.C 8
noncomputable def retainedSearchExec (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 EvalsToInTime (TM2.step retainedSearchMachine.program) (retainedSearchMachine.init (input q A R))
  (some (retainedSearchMachine.halt (found q A R::input q A R)))
  (retainedSearchTime.eval (input q A R).length):=by
 have h:=RetainedInput.executes searchMachine _ _ _ (searchExec q A R)
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [retainedSearchTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
  Polynomial.eval_X,List.length_cons,List.length_nil]
 omega
end QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
namespace QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
local instance _p2m_local_instance_25ca2d8bb9_350 : Fact (Even (Fintype.card (Fin 2))) :=⟨by simp⟩
def quotient (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)):PSL(2,ZMod q):=QuotientGroup.mk A
def representatives (q:ℕ) [Fact q.Prime]:List SL(2,ZMod q)→List SL(2,ZMod q)
 | [] => []
 | A::R =>if found q A R then representatives q R else A::representatives q R
noncomputable def searchOutputsInTime (q:ℕ) [Fact q.Prime] (A:SL(2,ZMod q)) (R:List SL(2,ZMod q)):
 TM2OutputsInTime searchMachine.toFinTM2 (input q A R) (some [found q A R])
  (searchTime.eval (input q A R).length):=Machine.outputsInTime searchMachine _ _ _ (searchExec q A R)
noncomputable def searchComputableInPolyTime (q:ℕ) [Fact q.Prime]:
 TM2ComputableInPolyTime (fun x:SL(2,ZMod q)×List SL(2,ZMod q)=>input q x.1 x.2)
  id (fun x=>[found q x.1 x.2]) where
 tm:=searchMachine.toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=searchTime
 outputsFun:=fun x=>by
  change TM2OutputsInTime searchMachine.toFinTM2 (List.map id (input q x.1 x.2))
   (some (List.map id [found q x.1 x.2])) (searchTime.eval (input q x.1 x.2).length)
  have h:=searchOutputsInTime q x.1 x.2
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
end QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine


