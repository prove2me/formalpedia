-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:41:16.623213+00:00
-- url     : https://prove2.me/theorems/26905891-7bf1-4b11-adf5-bf8a9ea11341
-- title:
--   LPSOriginal PSLLookup Machine
-- statement:
--   Definitions and structural lemmas for LPSOriginal PSLLookup Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLLookupMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldLookup
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
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
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.Initializer
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance _p2m_local_instance_eed6317f64_20:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
abbrev Input:=Σa:LPSOriginalPSLListMachine.Initializer.Input,Fin (lpsPSLList a.val).length
instance (a:Input):Fact a.1.val.Prime:=⟨a.1.property⟩
def input (a:Input):List Bool:=raw [a.2.val,a.1.val]
theorem input_eq (a:Input):input a=stream [a.2.val]++unary a.1.val:=by
 simpa only [input,List.cons_append,List.nil_append] using raw_append_last [a.2.val] a.1.val
theorem input_reverse (a:Input):(input a).reverse=raw [a.1.val,a.2.val]:=by
 simp [input,show raw [a.2.val,a.1.val]=unary a.2.val++false::unary a.1.val by simpa [stream] using raw_append_last [a.2.val] a.1.val,
  show raw [a.1.val,a.2.val]=unary a.1.val++false::unary a.2.val by simpa [stream] using raw_append_last [a.1.val] a.2.val,
  List.reverse_append,List.reverse_cons,unary,List.append_assoc]
def drop:=TailProjection.machine 0 (fun _=>false)
theorem selected_none (i:ℕ) (xs:List ℕ):fields 0 (fun _=>false) i xs=[]:=by
 induction xs generalizing i with
 | nil=>rfl
 | cons b xs ih=>simp [fields,maskAt,ih]
noncomputable def dropExec (a:Input):
 EvalsToInTime (TM2.step drop.program) (drop.init (input a)) (some (drop.halt (false::unary a.1.val)))
  (TailProjection.time.eval (input a).length):=by
 have h:=TailProjection.polyExec 0 (fun _=>false) [a.2.val]
  (by rfl) (unary a.1.val)
 rw [selected_none] at h
 simp only [raw,stream,List.dropLast_nil,List.nil_append] at h
 rw [input_eq]
 exact h
def psl:=LPSOriginalPSLListMachine.machine
def pslSwitch:=BooleanSwitch.machine psl psl
noncomputable def pslSwitchTime:Polynomial ℕ:=LPSOriginalPSLListMachine.time+Polynomial.C 2
theorem psl_io:psl.input≠psl.output:=by simp [psl,LPSOriginalPSLListMachine.machine,Composition.machine]
noncomputable def pslSwitchExec (a:Input):
 EvalsToInTime (TM2.step pslSwitch.program) (pslSwitch.init (false::unary a.1.val))
  (some (pslSwitch.halt (LPSOriginalPSLListMachine.output a.1.val)))
  (pslSwitchTime.eval (false::unary a.1.val).length):=by
 have hp:=LPSOriginalPSLListMachine.exec a.1
 have h:=BooleanSwitch.execB psl psl psl_io psl_io _ _ _ hp
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hm:=Composition.polynomial_eval_monotone LPSOriginalPSLListMachine.time
  (show (unary a.1.val).length≤(false::unary a.1.val).length by simp)
 dsimp only at hm
 simp only [pslSwitchTime,Polynomial.eval_add,Polynomial.eval_C]
 exact Nat.add_le_add_right hm 2
def rowsBody:=Composition.machine drop pslSwitch
noncomputable def rowsTime:Polynomial ℕ:=Composition.timePolynomial drop TailProjection.time pslSwitchTime
noncomputable def rowsExec (a:Input):
 EvalsToInTime (TM2.step rowsBody.program) (rowsBody.init (input a))
  (some (rowsBody.halt (LPSOriginalPSLListMachine.output a.1.val))) (rowsTime.eval (input a).length):=
 LPSOriginalPSLListMachine.Initializer.composeRuns drop pslSwitch _ _ _ TailProjection.time pslSwitchTime
  (dropExec a) (pslSwitchExec a)
theorem original_fields_nonempty (a:Input):
 (representatives a.1.val (lpsSLList a.1.val)).flatMap (coords a.1.val)≠[]:=
 LPSOriginalPSLIndexMachine.Initializer.original_fields_nonempty ⟨a.1,1⟩
theorem marked_source (a:Input):LPSOriginalPSLListMachine.output a.1.val++[false]=
 rows a.1.val (representatives a.1.val (lpsSLList a.1.val)):=by
 change raw ((representatives a.1.val (lpsSLList a.1.val)).flatMap (coords a.1.val))++[false]=_
 rw [MatrixListQuery.delimiter_raw _ (original_fields_nonempty a)]
 rfl
def reverseRows:=Composition.machine rowsBody LPSOriginalPSLListMachine.Initializer.markReverse
noncomputable def reverseRowsTime:Polynomial ℕ:=Composition.timePolynomial rowsBody rowsTime LPSOriginalPSLListMachine.Initializer.markReverseTime
noncomputable def reverseRowsExec (a:Input):
 EvalsToInTime (TM2.step reverseRows.program) (reverseRows.init (input a))
  (some (reverseRows.halt (rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse))
  (reverseRowsTime.eval (input a).length):=by
 have hm:=LPSOriginalPSLListMachine.Initializer.markReverseExec (LPSOriginalPSLListMachine.output a.1.val)
 rw [marked_source] at hm
 exact LPSOriginalPSLListMachine.Initializer.composeRuns rowsBody LPSOriginalPSLListMachine.Initializer.markReverse _ _ _
  rowsTime LPSOriginalPSLListMachine.Initializer.markReverseTime (rowsExec a) hm
def switch:=BooleanSwitch.machine reverseRows reverseRows
noncomputable def switchTime:Polynomial ℕ:=reverseRowsTime+Polynomial.C 2
noncomputable def switchExec (a:Input):
 EvalsToInTime (TM2.step switch.program) (switch.init (false::input a))
  (some (switch.halt (rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse))
  (switchTime.eval (false::input a).length):=by
 have h:=BooleanSwitch.execB reverseRows reverseRows (by simp [reverseRows,Composition.machine])
  (by simp [reverseRows,Composition.machine]) _ _ _ (reverseRowsExec a)
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hm:=Composition.polynomial_eval_monotone reverseRowsTime
  (show (input a).length≤(false::input a).length by simp)
 dsimp only at hm
 simp only [switchTime,Polynomial.eval_add,Polynomial.eval_C]
 exact Nat.add_le_add_right hm 2
def retain:=RetainedInput.machine switch
noncomputable def retainTime:Polynomial ℕ:=RetainedInput.timePolynomial switch switchTime
noncomputable def retainExec (a:Input):
 EvalsToInTime (TM2.step retain.program) (retain.init (false::input a))
  (some (retain.halt ((rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse++false::input a)))
  (retainTime.eval (false::input a).length):=
 RetainedInput.executes_polynomial switch (fun a:Input=>false::input a)
  (fun a=>(rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse) switchTime switchExec a
def restore:=Composition.machine retain BitReverse.machine
noncomputable def restoreTime:Polynomial ℕ:=Composition.timePolynomial retain retainTime (Polynomial.X+1)
noncomputable def restoreExec (a:Input):
 EvalsToInTime (TM2.step restore.program) (restore.init (false::input a))
  (some (restore.halt (QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.input a.1.val a.2.val ((representatives a.1.val (lpsSLList a.1.val)).map (coords a.1.val)))))
  (restoreTime.eval (false::input a).length):=by
 have hr:=BitReverse.exec ((rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse++false::input a)
 have he:((rows a.1.val (representatives a.1.val (lpsSLList a.1.val))).reverse++false::input a).reverse=
   QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.input a.1.val a.2.val ((representatives a.1.val (lpsSLList a.1.val)).map (coords a.1.val)):=by
  calc
   _=raw [a.1.val,a.2.val]++[false]++rows a.1.val (representatives a.1.val (lpsSLList a.1.val)):=by
    simp [List.reverse_append,List.reverse_cons,input_reverse,List.append_assoc]
   _=_:=by
    rw [MatrixListQuery.delimiter_raw _ (by simp)]
    simp only [QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.input,QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.rows,rows]
    rfl
 rw [he] at hr
 exact LPSOriginalPSLListMachine.Initializer.composeRuns retain BitReverse.machine _ _ _ retainTime (Polynomial.X+1)
  (retainExec a) (by simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using hr)
def machine:=Composition.machine (FixedLiteral.prefixMachine [false]) restore
noncomputable def time:Polynomial ℕ:=Composition.timePolynomial (FixedLiteral.prefixMachine [false]) (FixedLiteral.prefixTime [false]) restoreTime
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
  (some (machine.halt (QEC.Coding.BitTuring.UnaryArithmetic.FourFieldLookup.input a.1.val a.2.val ((representatives a.1.val (lpsSLList a.1.val)).map (coords a.1.val)))))
  (time.eval (input a).length):=
 LPSOriginalPSLListMachine.Initializer.composeRuns (FixedLiteral.prefixMachine [false]) restore _ _ _
  (FixedLiteral.prefixTime [false]) restoreTime (FixedLiteral.prefixExec [false] (input a)) (restoreExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine.Initializer
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance _p2m_local_instance_eed6317f64_203:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def originalReps (q:ℕ) [Fact q.Prime]:List SL(2,ZMod q):=representatives q (lpsSLList q)
theorem original_length (q:ℕ) [Fact q.Prime]:(originalReps q).length=(lpsPSLList q).length:=by
 simpa only [List.length_map,originalReps] using congrArg List.length (mapped_original_representatives q)
def representative (q:ℕ) [Fact q.Prime] (i:Fin (lpsPSLList q).length):SL(2,ZMod q):=
 (originalReps q)[i.val]'(by rw [original_length];exact i.isLt)
abbrev Input:=Initializer.Input
instance (a:Input):Fact a.1.val.Prime:=⟨a.1.property⟩
def input (a:Input):List Bool:=Initializer.input a
def output (a:Input):List Bool:=raw (coords a.1.val (representative a.1.val a.2))
def machine:=Composition.machine Initializer.machine FourFieldLookup.forwardMachine
noncomputable def time:Polynomial ℕ:=Composition.timePolynomial Initializer.machine Initializer.time FourFieldLookup.forwardTime
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
 (some (machine.halt (output a))) (time.eval (input a).length):=by
 have hi:a.2.val<((originalReps a.1.val).map (coords a.1.val)).length:=by
  simp only [List.length_map,original_length];exact a.2.isLt
 have hr:∀r∈(originalReps a.1.val).map (coords a.1.val),r.length=4:=by
  intro r hh
  obtain ⟨A,_,rfl⟩:=List.mem_map.mp hh
  simp [coords,LPSMatrixProductMachine.fields]
 have h:=FourFieldLookup.forwardExec a.1.val a.2.val ((originalReps a.1.val).map (coords a.1.val)) hi hr
 simp only [List.getElem_map] at h
 exact LPSOriginalPSLListMachine.Initializer.composeRuns Initializer.machine FourFieldLookup.forwardMachine _ _ _
  Initializer.time FourFieldLookup.forwardTime (Initializer.exec a) h
noncomputable def outputsInTime (a:Input):
 TM2OutputsInTime machine.toFinTM2 (input a) (some (output a)) (time.eval (input a).length):=
 Machine.outputsInTime machine _ _ _ (exec a)
noncomputable def computableInPolyTime:TM2ComputableInPolyTime input id output where
 tm:=machine.toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time
 outputsFun:=fun a=>by
  change TM2OutputsInTime machine.toFinTM2 (List.map id (input a)) (some (List.map id (output a))) (time.eval (input a).length)
  have h:=outputsInTime a
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
theorem input_length (a:Input):(input a).length=a.2.val+a.1.val+1:=by
 change (raw [a.2.val,a.1.val]).length=_
 rw [show raw [a.2.val,a.1.val]=stream [a.2.val]++unary a.1.val from raw_append_last [a.2.val] a.1.val]
 simp only [List.length_append,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,unary_length]
 omega
theorem original_length_card (q:ℕ) [Fact q.Prime]:(lpsPSLList q).length=Fintype.card PSL(2,ZMod q):=by
 simpa only [Fintype.card_fin] using Fintype.card_congr (lpsPSLEnumerationEquiv q)
theorem input_length_lt_card (a:Input):(input a).length<Fintype.card PSL(2,ZMod a.1.val)+a.1.val+1:=by
 rw [input_length]
 have h:a.2.val<Fintype.card PSL(2,ZMod a.1.val):=a.2.isLt.trans_le (le_of_eq (original_length_card a.1.val))
 omega
noncomputable def blockTime:Polynomial ℕ:=time.comp (Polynomial.C 3*Polynomial.X+Polynomial.C 1)
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (i:Fin (lpsPSLList a.q).length):
 EvalsToInTime (TM2.step machine.program) (machine.init (input ⟨⟨a.q,a.prime⟩,i⟩))
 (some (machine.halt (output ⟨⟨a.q,a.prime⟩,i⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨⟨a.q,a.prime⟩,i⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hL:(input ⟨⟨a.q,a.prime⟩,i⟩).length≤3*Fintype.card PSL(2,ZMod a.q)+1:=by
  have hh:=input_length_lt_card ⟨⟨a.q,a.prime⟩,i⟩
  have hq:=a.q_le_two_mul_card_psl
  dsimp only at hh
  omega
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time hL
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (i:Fin (lpsPSLList a.q).length):
 TM2OutputsInTime machine.toFinTM2 (input ⟨⟨a.q,a.prime⟩,i⟩) (some (output ⟨⟨a.q,a.prime⟩,i⟩))
 (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a i)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLLookupMachine


