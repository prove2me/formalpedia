-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalGeneratorVoltageMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:45:46.891192+00:00
-- url     : https://prove2.me/theorems/01c8e36a-a68f-4a12-8eee-92929f9b72f3
-- title:
--   LPSOriginal Generator Voltage Machine
-- statement:
--   Definitions and structural lemmas for LPSOriginal Generator Voltage Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGeneratorVoltageMachine.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGeneratorIndexMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
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
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_ef31e85fec_23:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def entries {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):List ℕ:=
 (lpsPSLIndexOne a.q).val::Ordered.indices a ts
theorem entries_length {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 (entries a ts).length=ts.length+1:=by simp [entries,Ordered.indices_length]
def identityQuery (n:ℕ):=RetainedFieldComputation.machine n (ModulusQuery.mask n) Identity.machine
noncomputable def identityQueryTime (n:ℕ):=RetainedFieldComputation.time n (ModulusQuery.mask n) Identity.machine Identity.time
noncomputable def identityQueryExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (identityQuery ts.length).program)
 ((identityQuery ts.length).init (stream (Ordered.indices a ts++[a.q])))
 (some ((identityQuery ts.length).halt (stream (entries a ts++[a.q]))))
 ((identityQueryTime ts.length).eval (stream (Ordered.indices a ts++[a.q])).length):=by
 have hf:=MatrixListQuery.selectLast ts.length 0 (Ordered.indices a ts) a.q (by simpa using Ordered.indices_length a ts)
 have he:raw [a.q]=unary a.q:=by simpa [stream] using raw_append_last [] a.q
 have hr:raw [(lpsPSLIndexOne a.q).val]=unary (lpsPSLIndexOne a.q).val:=by
  simpa [stream] using raw_append_last [] (lpsPSLIndexOne a.q).val
 have hb:EvalsToInTime (TM2.step Identity.machine.program)
  (Identity.machine.init (raw (fields ts.length (ModulusQuery.mask ts.length) 0 (Ordered.indices a ts++[a.q]))))
  (some (Identity.machine.halt (raw [(lpsPSLIndexOne a.q).val])))
  (Identity.time.eval (raw (fields ts.length (ModulusQuery.mask ts.length) 0 (Ordered.indices a ts++[a.q]))).length):=by
  rw [hf,he,hr]
  exact Identity.exec ⟨a.q,a.prime⟩
 have h:=RetainedFieldComputation.exec ts.length (ModulusQuery.mask ts.length) Identity.machine
  (Ordered.indices a ts++[a.q]) [(lpsPSLIndexOne a.q).val] (by simp [Ordered.indices_length]) (by simp) Identity.time hb
 rw [←MatrixListQuery.stream_append] at h
 exact h
def collector {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine (Ordered.collector ts) (identityQuery ts.length)
noncomputable def collectorTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial (Ordered.collector ts) (Ordered.collectorTime ts) (identityQueryTime ts.length)
noncomputable def collectorExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (collector ts).program) ((collector ts).init (stream [a.q]))
 (some ((collector ts).halt (stream (entries a ts++[a.q])))) ((collectorTime ts).eval (stream [a.q]).length):=
 RetainedFieldComputation.composeRuns (Ordered.collector ts) (identityQuery ts.length) _ _ _
  (Ordered.collectorTime ts) (identityQueryTime ts.length) (Ordered.collectorExec a ts) (identityQueryExec a ts)
def projector {p:ℕ} (ts:List (LPSGeneratorIndex p)):=FieldProjection.machine (ts.length+1) (MatrixListQuery.prefixMask (ts.length+1))
noncomputable def projectorExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (projector ts).program) ((projector ts).init (stream (entries a ts++[a.q])))
 (some ((projector ts).halt (raw (entries a ts)))) (FieldProjection.time.eval (stream (entries a ts++[a.q])).length):=by
 have h:=FieldProjection.polyExec (ts.length+1) (MatrixListQuery.prefixMask (ts.length+1)) (entries a ts++[a.q]) (by simp [entries_length])
 rw [MatrixListQuery.selectPrefix (ts.length+1) 0 (entries a ts) a.q (by simpa using entries_length a ts)] at h
 exact h
def collected {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine (collector ts) (projector ts)
noncomputable def collectedTime {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial (collector ts) (collectorTime ts) FieldProjection.time
noncomputable def collectedExec {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):
 EvalsToInTime (TM2.step (collected ts).program) ((collected ts).init (stream [a.q]))
 (some ((collected ts).halt (raw (entries a ts)))) ((collectedTime ts).eval (stream [a.q]).length):=
 RetainedFieldComputation.composeRuns (collector ts) (projector ts) _ _ _ (collectorTime ts) FieldProjection.time (collectorExec a ts) (projectorExec a ts)
def machine {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.machine BitDelimiter.machine (collected ts)
noncomputable def time {p:ℕ} (ts:List (LPSGeneratorIndex p)):=Composition.timePolynomial BitDelimiter.machine (Polynomial.C 2*Polynomial.X+Polynomial.C 3) (collectedTime ts)
def output {p:ℕ} (a:LPSResiduePrime p) (ts:List (LPSGeneratorIndex p)):List Bool:=raw (entries a ts)
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
theorem ordered_entries {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p):
 entries a (List.ofFn g)=(lpsPSLIndexOne a.q).val::List.ofFn (fun j=>(result a (g j)).val):=by
 rw [entries,Ordered.ordered_indices]
def fieldIndex {D:ℕ} (side:Fin 2) (j:Fin D):Fin (D+1):=
 if side=0 then 0 else ⟨j.val+1,by omega⟩
noncomputable def sourceOutput {p:ℕ} (a:LPSResiduePrime p):List Bool:=
 raw ((lpsPSLIndexOne a.q).val::List.ofFn (fun j=>(result a (lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one a.degreePrime a.degreeModFour) j)).val))
theorem output_eq_source {p:ℕ} (a:LPSResiduePrime p):
 output a (LPSGeneratorMatrixListMachine.sourceDirections a.degreePrime a.degreeModFour)=sourceOutput a:=by
 simp only [output,sourceOutput,LPSGeneratorMatrixListMachine.sourceDirections,ordered_entries]
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
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open scoped MatrixGroups
local instance _p2m_local_instance_ef31e85fec_196:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def entryMachine {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):=
 if side=0 then Identity.machine else LPSOriginalGeneratorIndexMachine.machine (g j)
noncomputable def entryTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):=
 if side=0 then Identity.time else LPSOriginalGeneratorIndexMachine.time (g j)
noncomputable def entryExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 EvalsToInTime (TM2.step (entryMachine g side j).program) ((entryMachine g side j).init (unary a.q))
 (some ((entryMachine g side j).halt (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val)))
 ((entryTime g side j).eval (unary a.q).length):=by
 by_cases hs:side=0
 · have hm:entryMachine g side j=Identity.machine:=if_pos hs
   have ht:entryTime g side j=Identity.time:=if_pos hs
   rw [hm,ht]
   simp only [lpsSparseVoltage,if_pos hs]
   exact Identity.exec ⟨a.q,a.prime⟩
 · have hm:entryMachine g side j=LPSOriginalGeneratorIndexMachine.machine (g j):=if_neg hs
   have ht:entryTime g side j=LPSOriginalGeneratorIndexMachine.time (g j):=if_neg hs
   rw [hm,ht]
   simp only [lpsSparseVoltage,if_neg hs]
   exact LPSOriginalGeneratorIndexMachine.exec a (g j)
noncomputable def entryOutputsInTime {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 TM2OutputsInTime (entryMachine g side j).toFinTM2 (unary a.q)
 (some (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val)) ((entryTime g side j).eval (unary a.q).length):=
 Machine.outputsInTime (entryMachine g side j) _ _ _ (entryExec a g side j)
noncomputable def entryComputableInPolyTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id
 (fun a=>unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val) where
 tm:=(entryMachine g side j).toFinTM2
 inputAlphabet:=Equiv.refl Bool
 outputAlphabet:=Equiv.refl Bool
 time:=entryTime g side j
 outputsFun:=fun a=>by
  change TM2OutputsInTime (entryMachine g side j).toFinTM2 (List.map id (unary a.q))
   (some (List.map id (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val))) ((entryTime g side j).eval (unary a.q).length)
  have h:=entryOutputsInTime a g side j
  dsimp only [Machine.toFinTM2] at h ⊢
  simpa only [List.map_id] using h
noncomputable def entryBlockTime {p D:ℕ} (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):Polynomial ℕ:=
 (entryTime g side j).comp (Polynomial.C 2*Polynomial.X)
noncomputable def entryBlockExec {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 EvalsToInTime (TM2.step (entryMachine g side j).program) ((entryMachine g side j).init (unary a.q))
 (some ((entryMachine g side j).halt (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val)))
 ((entryBlockTime g side j).eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=entryExec a g side j
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 simp only [entryBlockTime,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone (entryTime g side j) (by simpa only [unary_length] using a.q_le_two_mul_card_psl)
noncomputable def entryBlockOutputsInTime {p D:ℕ} (a:LPSResiduePrime p) (g:Fin D→LPSGeneratorIndex p) (side:Fin 2) (j:Fin D):
 TM2OutputsInTime (entryMachine g side j).toFinTM2 (unary a.q)
 (some (unary (lpsSparseVoltage (fun j=>result a (g j)) side j).val)) ((entryBlockTime g side j).eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime (entryMachine g side j) _ _ _ (entryBlockExec a g side j)
end QEC.Coding.TannerLiftedProduct.LPSOriginalGeneratorIndexMachine.Voltage


