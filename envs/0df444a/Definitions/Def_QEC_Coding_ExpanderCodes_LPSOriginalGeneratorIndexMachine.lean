-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:43:35.890511+00:00
-- url     : https://prove2.me/theorems/ae95d4f8-3e7e-4a77-afb3-115f45fd1996
-- title:
--   LPSOriginal Generator Index Machine
-- statement:
--   Definitions and structural lemmas for LPSOriginal Generator Index Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorIndexMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGeneratorMatrixListMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_raw_append_last
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_MatrixListQuery_selectPrefix
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsQuaternionShell_eq_prime_add_one
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
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open LPSPSLSearchMachine
open scoped MatrixGroups
local instance _p2m_local_instance_8252a2e3b6_28:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def matrix {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):SL(2,ZMod a.q):=
 LPSGeneratorMatrixListMachine.generatorSL a t
def result {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):Fin (lpsPSLList a.q).length:=
 lpsQuaternionVertexIndex a t.val (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.property)
def query {p:ℕ} (t:LPSGeneratorIndex p):=RetainedFieldComputation.machine 0 (ModulusQuery.mask 0) (LPSQuaternionMatrixMachine.machine p t.val)
noncomputable def queryTime {p:ℕ} (t:LPSGeneratorIndex p):=RetainedFieldComputation.time 0 (ModulusQuery.mask 0) (LPSQuaternionMatrixMachine.machine p t.val) (LPSQuaternionMatrixMachine.time p t.val)
noncomputable def queryExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step (query t).program) ((query t).init (stream [a.q]))
 (some ((query t).halt (stream (coords a.q (matrix a t)++[a.q])))) ((queryTime t).eval (stream [a.q]).length):=by
 have hf:fields 0 (ModulusQuery.mask 0) 0 [a.q]=[a.q]:=by simp [fields,maskAt,ModulusQuery.mask]
 have he:raw [a.q]=unary a.q:=by simpa [stream] using raw_append_last [] a.q
 have hb:EvalsToInTime (TM2.step (LPSQuaternionMatrixMachine.machine p t.val).program)
  ((LPSQuaternionMatrixMachine.machine p t.val).init (raw (fields 0 (ModulusQuery.mask 0) 0 [a.q])))
  (some ((LPSQuaternionMatrixMachine.machine p t.val).halt (raw (coords a.q (matrix a t)))))
  ((LPSQuaternionMatrixMachine.time p t.val).eval (raw (fields 0 (ModulusQuery.mask 0) 0 [a.q])).length):=by
  rw [hf,he]
  exact LPSQuaternionMatrixMachine.polyExec a t.val (norm_eq_of_mem_lpsQuaternionShell a.degreePrime.pos t.property)
 have h:=RetainedFieldComputation.exec 0 (ModulusQuery.mask 0) (LPSQuaternionMatrixMachine.machine p t.val)
  [a.q] (coords a.q (matrix a t)) (by rfl) (by simp [coords,LPSMatrixProductMachine.fields]) (LPSQuaternionMatrixMachine.time p t.val) hb
 rw [←MatrixListQuery.stream_append] at h
 exact h
def retainModulus:=ModularAdjugate.retainedUnary 4 (ModulusQuery.mask 4)
noncomputable def retainModulusExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step retainModulus.program) (retainModulus.init (stream (coords a.q (matrix a t)++[a.q])))
 (some (retainModulus.halt (stream (a.q::coords a.q (matrix a t)++[a.q]))))
 (ModularAdjugate.stageTime.eval (stream (coords a.q (matrix a t)++[a.q])).length):=
 ModularAdjugate.unaryStageExec 4 (ModulusQuery.mask 4) _
  (by simp [coords,LPSMatrixProductMachine.fields]) a.q
  (MatrixListQuery.selectLast 4 0 (coords a.q (matrix a t)) a.q (by simp [coords,LPSMatrixProductMachine.fields]))
def firstFive (k:Fin 6):Bool:=decide (k.val<5)
theorem first_five_fields {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 fields 5 firstFive 0 (a.q::coords a.q (matrix a t)++[a.q])=a.q::coords a.q (matrix a t):=by
 simp [coords,LPSMatrixProductMachine.fields,fields,maskAt,firstFive]
def prepareIndex:=RetainedFieldComputation.projectedReverse 5 firstFive
noncomputable def prepareIndexTime:=RetainedFieldComputation.projectedReverseTime 5 firstFive
noncomputable def prepareIndexExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step prepareIndex.program) (prepareIndex.init (stream (a.q::coords a.q (matrix a t)++[a.q])))
 (some (prepareIndex.halt (LPSOriginalPSLIndexMachine.input ⟨⟨a.q,a.prime⟩,matrix a t⟩)))
 (prepareIndexTime.eval (stream (a.q::coords a.q (matrix a t)++[a.q])).length):=by
 have h:=RetainedFieldComputation.projectedReverseExec 5 firstFive (a.q::coords a.q (matrix a t)++[a.q])
  (by simp [coords,LPSMatrixProductMachine.fields])
 rw [first_five_fields] at h
 have he:(raw (a.q::coords a.q (matrix a t))).reverse=LPSOriginalPSLIndexMachine.input ⟨⟨a.q,a.prime⟩,matrix a t⟩:=by
  have hi:=LPSOriginalPSLIndexMachine.Initializer.input_reverse ⟨⟨a.q,a.prime⟩,matrix a t⟩
  change (LPSOriginalPSLIndexMachine.Initializer.input ⟨⟨a.q,a.prime⟩,matrix a t⟩).reverse=raw (a.q::coords a.q (matrix a t)) at hi
  rw [←hi,List.reverse_reverse]
  rfl
 rw [he] at h
 exact h
def output {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):List Bool:=unary (result a t).val
theorem source_output {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 LPSOriginalPSLIndexMachine.output ⟨⟨a.q,a.prime⟩,matrix a t⟩=output a t:=by
 simp only [LPSOriginalPSLIndexMachine.output,output,result,matrix,LPSGeneratorMatrixListMachine.generatorSL,
  lpsQuaternionVertexIndex,lpsEffectiveQuaternionPSL,quotient]
def indexed:=Composition.machine prepareIndex LPSOriginalPSLIndexMachine.machine
noncomputable def indexedTime:=Composition.timePolynomial prepareIndex prepareIndexTime LPSOriginalPSLIndexMachine.time
noncomputable def indexedExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step indexed.program) (indexed.init (stream (a.q::coords a.q (matrix a t)++[a.q])))
 (some (indexed.halt (output a t))) (indexedTime.eval (stream (a.q::coords a.q (matrix a t)++[a.q])).length):=by
 have h:=LPSOriginalPSLIndexMachine.exec ⟨⟨a.q,a.prime⟩,matrix a t⟩
 rw [source_output] at h
 exact RetainedFieldComputation.composeRuns prepareIndex LPSOriginalPSLIndexMachine.machine _ _ _ prepareIndexTime LPSOriginalPSLIndexMachine.time (prepareIndexExec a t) h
def modulusAndIndex:=Composition.machine retainModulus indexed
noncomputable def modulusAndIndexTime:=Composition.timePolynomial retainModulus ModularAdjugate.stageTime indexedTime
noncomputable def modulusAndIndexExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step modulusAndIndex.program) (modulusAndIndex.init (stream (coords a.q (matrix a t)++[a.q])))
 (some (modulusAndIndex.halt (output a t))) (modulusAndIndexTime.eval (stream (coords a.q (matrix a t)++[a.q])).length):=
 RetainedFieldComputation.composeRuns retainModulus indexed _ _ _ ModularAdjugate.stageTime indexedTime (retainModulusExec a t) (indexedExec a t)
def queryAndIndex {p:ℕ} (t:LPSGeneratorIndex p):=Composition.machine (query t) modulusAndIndex
noncomputable def queryAndIndexTime {p:ℕ} (t:LPSGeneratorIndex p):=Composition.timePolynomial (query t) (queryTime t) modulusAndIndexTime
noncomputable def queryAndIndexExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step (queryAndIndex t).program) ((queryAndIndex t).init (stream [a.q]))
 (some ((queryAndIndex t).halt (output a t))) ((queryAndIndexTime t).eval (stream [a.q]).length):=
 RetainedFieldComputation.composeRuns (query t) modulusAndIndex _ _ _ (queryTime t) modulusAndIndexTime (queryExec a t) (modulusAndIndexExec a t)
def machine {p:ℕ} (t:LPSGeneratorIndex p):=Composition.machine BitDelimiter.machine (queryAndIndex t)
noncomputable def time {p:ℕ} (t:LPSGeneratorIndex p):=Composition.timePolynomial BitDelimiter.machine (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (queryAndIndexTime t)
noncomputable def exec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step (machine t).program) ((machine t).init (unary a.q))
 (some ((machine t).halt (output a t))) ((time t).eval (unary a.q).length):=by
 have h:=BitDelimiter.exec (unary a.q)
 have he:unary a.q++[false]=stream [a.q]:=by simp [stream]
 rw [he] at h
 exact RetainedFieldComputation.composeRuns BitDelimiter.machine (queryAndIndex t) _ _ _ (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (queryAndIndexTime t)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using h) (queryAndIndexExec a t)
noncomputable def outputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 TM2OutputsInTime (machine t).toFinTM2 (unary a.q) (some (output a t)) ((time t).eval (unary a.q).length):=
 Machine.outputsInTime (machine t) _ _ _ (exec a t)
noncomputable def computableInPolyTime {p:ℕ} (t:LPSGeneratorIndex p):
 TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>output a t) where
 tm:=(machine t).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time t
 outputsFun:=fun a=>by
  change TM2OutputsInTime (machine t).toFinTM2 (List.map id (unary a.q)) (some (List.map id (output a t))) ((time t).eval (unary a.q).length)
  have h:=outputsInTime a t
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def blockTime {p:ℕ} (t:LPSGeneratorIndex p):Polynomial ℕ:=(time t).comp (Polynomial.C 2*Polynomial.X)
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 EvalsToInTime (TM2.step (machine t).program) ((machine t).init (unary a.q))
 (some ((machine t).halt (output a t))) ((blockTime t).eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec a t
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone (time t) (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p):
 TM2OutputsInTime (machine t).toFinTM2 (unary a.q) (some (output a t)) ((blockTime t).eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime (machine t) _ _ _ (blockExec a t)
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_8252a2e3b6_181:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def indices {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):List ℕ:=ts.map (fun t=>(result a t).val)
theorem indices_length {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):(indices a ts).length=ts.length:=by simp [indices]
def query {p:ℕ} (n:ℕ) (t:LPSGeneratorIndex p):=RetainedFieldComputation.machine n (ModulusQuery.mask n) (LPSOriginalGeneratorIndexMachine.machine t)
noncomputable def queryTime {p:ℕ} (n:ℕ) (t:LPSGeneratorIndex p):=RetainedFieldComputation.time n (ModulusQuery.mask n) (LPSOriginalGeneratorIndexMachine.machine t) (LPSOriginalGeneratorIndexMachine.time t)
noncomputable def queryExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSGeneratorIndex p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (query ts.length t).program) ((query ts.length t).init (stream (indices a ts++[a.q])))
 (some ((query ts.length t).halt (stream ((result a t).val::indices a ts++[a.q]))))
 ((queryTime ts.length t).eval (stream (indices a ts++[a.q])).length):=by
 have hf:=MatrixListQuery.selectLast ts.length 0 (indices a ts) a.q (by simp [indices_length])
 have he:raw [a.q]=unary a.q:=by simpa [stream] using raw_append_last [] a.q
 have hb:EvalsToInTime (TM2.step (LPSOriginalGeneratorIndexMachine.machine t).program)
  ((LPSOriginalGeneratorIndexMachine.machine t).init (raw (fields ts.length (ModulusQuery.mask ts.length) 0 (indices a ts++[a.q]))))
  (some ((LPSOriginalGeneratorIndexMachine.machine t).halt (raw [(result a t).val])))
  ((LPSOriginalGeneratorIndexMachine.time t).eval (raw (fields ts.length (ModulusQuery.mask ts.length) 0 (indices a ts++[a.q]))).length):=by
  rw [hf,he]
  have hr:raw [(result a t).val]=unary (result a t).val:=by simpa [stream] using raw_append_last [] (result a t).val
  rw [hr]
  exact LPSOriginalGeneratorIndexMachine.exec a t
 have h:=RetainedFieldComputation.exec ts.length (ModulusQuery.mask ts.length) (LPSOriginalGeneratorIndexMachine.machine t)
  (indices a ts++[a.q]) [(result a t).val] (by simp [indices_length]) (by simp) (LPSOriginalGeneratorIndexMachine.time t) hb
 have he:stream [(result a t).val]++stream (indices a ts++[a.q])=stream ((result a t).val::indices a ts++[a.q]):=by
  rw [←MatrixListQuery.stream_append]
  rfl
 rw [he] at h
 exact h
def collector {p:ℕ}:List (LPSGeneratorIndex p)→Machine
 | []=>MatrixListQuery.identityMachine
 | t::ts=>Composition.machine (collector ts) (query ts.length t)
noncomputable def collectorTime {p:ℕ}:List (LPSGeneratorIndex p)→Polynomial ℕ
 | []=>Polynomial.C 4*Polynomial.X+Polynomial.C 4
 | t::ts=>Composition.timePolynomial (collector ts) (collectorTime ts) (queryTime ts.length t)
noncomputable def collectorExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (collector ts).program) ((collector ts).init (stream [a.q]))
 (some ((collector ts).halt (stream (indices a ts++[a.q])))) ((collectorTime ts).eval (stream [a.q]).length):=by
 induction ts with
 | nil=>
  have h:=MatrixListQuery.identityExec (stream [a.q])
  have he:(collectorTime ([]:List (LPSGeneratorIndex p))).eval (stream [a.q]).length=4*(stream [a.q]).length+4:=by
   simp only [collectorTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  rw [he]
  exact h
 | cons t ts ih=>
  have h:=RetainedFieldComputation.composeRuns (collector ts) (query ts.length t) _ _ _ (collectorTime ts) (queryTime ts.length t) ih (queryExec a t ts)
  exact h
def projector {p:ℕ} (ts:List (LPSGeneratorIndex p)):=FieldProjection.machine ts.length (MatrixListQuery.prefixMask ts.length)
noncomputable def projectorExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (projector ts).program) ((projector ts).init (stream (indices a ts++[a.q])))
 (some ((projector ts).halt (raw (indices a ts)))) (FieldProjection.time.eval (stream (indices a ts++[a.q])).length):=by
 have h:=FieldProjection.polyExec ts.length (MatrixListQuery.prefixMask ts.length) (indices a ts++[a.q]) (by simp [indices_length])
 rw [MatrixListQuery.selectPrefix ts.length 0 (indices a ts) a.q (by simp [indices_length])] at h
 exact h
def collected {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine (collector ts) (projector ts)
noncomputable def collectedTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial (collector ts) (collectorTime ts) FieldProjection.time
noncomputable def collectedExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (collected ts).program) ((collected ts).init (stream [a.q]))
 (some ((collected ts).halt (raw (indices a ts)))) ((collectedTime ts).eval (stream [a.q]).length):=
 RetainedFieldComputation.composeRuns (collector ts) (projector ts) _ _ _ (collectorTime ts) FieldProjection.time (collectorExec a ts) (projectorExec a ts)
def machine {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine BitDelimiter.machine (collected ts)
noncomputable def time {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial BitDelimiter.machine (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (collectedTime ts)
def output {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):List Bool:=raw (indices a ts)
noncomputable def exec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (machine ts).program) ((machine ts).init (unary a.q))
 (some ((machine ts).halt (output a ts))) ((time ts).eval (unary a.q).length):=by
 have h:=BitDelimiter.exec (unary a.q)
 have he:unary a.q++[false]=stream [a.q]:=by simp [stream]
 rw [he] at h
 exact RetainedFieldComputation.composeRuns BitDelimiter.machine (collected ts) _ _ _ (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (collectedTime ts)
  (by simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] using h) (collectedExec a ts)
noncomputable def outputsInTime {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 TM2OutputsInTime (machine ts).toFinTM2 (unary a.q) (some (output a ts)) ((time ts).eval (unary a.q).length):=
 Machine.outputsInTime (machine ts) _ _ _ (exec a ts)
noncomputable def computableInPolyTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):
 TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>output a ts) where
 tm:=(machine ts).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=time ts
 outputsFun:=fun a=>by
  change TM2OutputsInTime (machine ts).toFinTM2 (List.map id (unary a.q)) (some (List.map id (output a ts))) ((time ts).eval (unary a.q).length)
  have h:=outputsInTime a ts
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def blockTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):Polynomial ℕ:=(time ts).comp (Polynomial.C 2*Polynomial.X)
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (machine ts).program) ((machine ts).init (unary a.q))
 (some ((machine ts).halt (output a ts))) ((blockTime ts).eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec a ts
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone (time ts) (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 TM2OutputsInTime (machine ts).toFinTM2 (unary a.q) (some (output a ts)) ((blockTime ts).eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime (machine ts) _ _ _ (blockExec a ts)
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Identity
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open LPSPSLSearchMachine
open scoped MatrixGroups
local instance _p2m_local_instance_8252a2e3b6_304:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
abbrev Input:=LPSOriginalPSLListMachine.Initializer.Input
instance (a:Input):Fact a.val.Prime:=⟨a.property⟩
def header:List Bool:=raw [1,0,0,1]++[false]
def prepare:=FixedLiteral.prefixMachine header
noncomputable def prepareTime:=FixedLiteral.prefixTime header
theorem source_input (a:Input):header++unary a.val=LPSOriginalPSLIndexMachine.input ⟨a,1⟩:=by
 let:Fact (1<a.val):=⟨a.property.one_lt⟩
 have hh:=raw_append_last [1,0,0,1] a.val
 simp only [header] at hh ⊢
 rw [MatrixListQuery.delimiter_raw _ (by simp),←hh]
 simp [LPSOriginalPSLIndexMachine.input,LPSOriginalPSLIndexMachine.Initializer.input,
  coords,LPSMatrixProductMachine.fields,ZMod.val_one]
def output (a:Input):List Bool:=unary (lpsPSLIndexOne a.val).val
theorem source_output (a:Input):LPSOriginalPSLIndexMachine.output ⟨a,1⟩=output a:=by
 simp [LPSOriginalPSLIndexMachine.output,output,lpsPSLIndexOne,quotient]
def machine:=Composition.machine prepare LPSOriginalPSLIndexMachine.machine
noncomputable def time:=Composition.timePolynomial prepare prepareTime LPSOriginalPSLIndexMachine.time
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.val))
 (some (machine.halt (output a))) (time.eval (unary a.val).length):=by
 have hp:=FixedLiteral.prefixExec header (unary a.val)
 rw [source_input] at hp
 have hi:=LPSOriginalPSLIndexMachine.exec ⟨a,1⟩
 rw [source_output] at hi
 exact RetainedFieldComputation.composeRuns prepare LPSOriginalPSLIndexMachine.machine _ _ _ prepareTime LPSOriginalPSLIndexMachine.time hp hi
noncomputable def outputsInTime (a:Input):
 TM2OutputsInTime machine.toFinTM2 (unary a.val) (some (output a)) (time.eval (unary a.val).length):=
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
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step machine.program) (machine.init (unary a.q))
 (some (machine.halt (output ⟨a.q,a.prime⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨a.q,a.prime⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p):
 TM2OutputsInTime machine.toFinTM2 (unary a.q) (some (output ⟨a.q,a.prime⟩)) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a)
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Identity
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_8252a2e3b6_378:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_8252a2e3b6_393:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
theorem ordered_indices {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p):
 indices a (List.ofFn g)=List.ofFn (fun j=>(result a (g j)).val):=by
 simp [indices,List.map_ofFn,Function.comp_def]
noncomputable def sourceOutput {p:ℕ} (a:LPSResiduePrime p):List Bool:=
 raw (List.ofFn (fun j=>(result a (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one a.degreePrime a.degreeModFour) j)).val))
theorem output_eq_source {p:ℕ} (a:LPSResiduePrime p):
 output a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)=sourceOutput a:=by
 simp only [output,sourceOutput,LPSGeneratorMatrixListMachine.sourceDirections,ordered_indices]
noncomputable def sourceExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step (machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).program)
 ((machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).init (unary a.q))
 (some ((machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).halt (sourceOutput a)))
 ((time (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).eval (unary a.q).length):=by
 have h:=exec a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)
 rw [output_eq_source] at h
 exact h
noncomputable def sourceBlockExec {p:ℕ} (a:LPSResiduePrime p):
 EvalsToInTime (TM2.step (machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).program)
 ((machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).init (unary a.q))
 (some ((machine (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).halt (sourceOutput a)))
 ((blockTime (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)).eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=blockExec a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)
 rw [output_eq_source] at h
 exact h
noncomputable def sourceComputableInPolyTime {p:ℕ} (hp:p.Prime) (hp4:p%4=1):=
 computableInPolyTime (LPSGeneratorMatrixListMachine.sourceDirections hp hp4)
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Ordered


