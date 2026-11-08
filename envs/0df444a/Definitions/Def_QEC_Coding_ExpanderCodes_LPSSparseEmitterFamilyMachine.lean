-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
-- name    : QEC_Coding_ExpanderCodes_LPSSparseEmitterFamilyMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:39:42.422646+00:00
-- url     : https://prove2.me/theorems/a9240153-14a7-41d1-9f34-b2f1a0e0bf24
-- title:
--   LPSSparse Emitter Family Machine
-- statement:
--   Definitions and structural lemmas for LPSSparse Emitter Family Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseEmitterFamilyMachine.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseEmitterSourceMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPrimeMachine
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
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
def machine {p D r r' s:ℕ} (hp:p.Prime) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):=
 Composition.machine (lpsPrimeMachine hp) (LPSSparseEmitterSource.machine g t h h')
noncomputable def time {p D r r' s:ℕ} (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):Polynomial ℕ:=
 (ResiduePrime.fullTime+LPSSparseEmitterSource.time g t h h'+Polynomial.C 2*Polynomial.X+Polynomial.C 2).comp
 (Polynomial.C 2*Polynomial.X)
def output {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):=
 LPSSparseEmitterSource.output (lpsEffectiveResiduePrimeAt hp hp4 B) g t h h'
noncomputable def exec {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 EvalsToInTime (TM2.step (machine hp g t h h').program) ((machine hp g t h h').init (unary B))
 (some ((machine hp g t h h').halt (output hp hp4 B g t h h')))
 ((time g t h h').eval (Fintype.card PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q))):=by
 let a:=lpsEffectiveResiduePrimeAt hp hp4 B
 have hx:=Composition.executes (lpsPrimeMachine hp) (LPSSparseEmitterSource.machine g t h h') _ _ _ _ _
  (lpsPrimeMachineBlockExec hp hp4 B) (LPSSparseEmitterSource.blockExec a g t h h')
 refine {hx with steps_le_m:=hx.steps_le_m.trans ?_}
 dsimp only [a]
 simp only [time,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,unary_length]
 have hq:=a.q_le_two_mul_card_psl
 dsimp only [a] at hq
 omega
noncomputable def outputsInTime {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 TM2OutputsInTime (machine hp g t h h').toFinTM2 (unary B) (some (output hp hp4 B g t h h'))
 ((time g t h h').eval (Fintype.card PSL(2,ZMod (lpsEffectiveResiduePrimeAt hp hp4 B).q))):=
 Machine.outputsInTime _ _ _ _ (exec hp hp4 B g t h h')
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open scoped MatrixGroups
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open scoped MatrixGroups
def physicalSize {p:ℕ} (a:LPSResiduePrime p) (D r r':ℕ):ℕ:=
 Fintype.card (LiftedProduct.QubitIndex (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod a.q))
theorem physicalSize_eq {p:ℕ} (a:LPSResiduePrime p) (D r r':ℕ):
 physicalSize a D r r'=(D*D+(2*r)*(2*r'))*Fintype.card PSL(2,ZMod a.q):=by
 simp only [physicalSize,LiftedProduct.QubitIndex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
 ring
theorem carrier_le_physicalSize {p:ℕ} (a:LPSResiduePrime p) {D r r':ℕ} (hD:0 < D):
 Fintype.card PSL(2,ZMod a.q) ≤ physicalSize a D r r':=by
 rw [physicalSize_eq]
 have hd:1 ≤ D*D:=by nlinarith
 simpa only [Nat.one_mul] using Nat.mul_le_mul_right (Fintype.card PSL(2,ZMod a.q)) (hd.trans (Nat.le_add_right _ _))
noncomputable def physicalExec {p D r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (hD:0 < D)
 (g:Fin D→LPSGeneratorIndex p) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin D) (Fin s)) (h':Matrix (Fin r') (Fin D) (Fin s)):
 EvalsToInTime (TM2.step (machine hp g t h h').program) ((machine hp g t h h').init (unary B))
 (some ((machine hp g t h h').halt (output hp hp4 B g t h h')))
 ((time g t h h').eval (physicalSize (lpsEffectiveResiduePrimeAt hp hp4 B) D r r')):=by
 have hx:=exec hp hp4 B g t h h'
 refine {hx with steps_le_m:=hx.steps_le_m.trans ?_}
 exact Composition.polynomial_eval_monotone _ (carrier_le_physicalSize _ hD)
noncomputable def sourceDirections {p:ℕ} (hp:p.Prime) (hp4:p%4=1):Fin (p+1)→LPSGeneratorIndex p:=
 lpsFinGeneratorEquiv (card_lpsQuaternionShell_eq_prime_add_one hp hp4)
noncomputable def sourceMachine {p r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin (p+1)) (Fin s)) (h':Matrix (Fin r') (Fin (p+1)) (Fin s)):=
 machine hp (sourceDirections hp hp4) t h h'
noncomputable def sourceTime {p r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin (p+1)) (Fin s)) (h':Matrix (Fin r') (Fin (p+1)) (Fin s)):=
 time (sourceDirections hp hp4) t h h'
noncomputable def sourceOutput {p r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin (p+1)) (Fin s)) (h':Matrix (Fin r') (Fin (p+1)) (Fin s)):=
 output hp hp4 B (sourceDirections hp hp4) t h h'
noncomputable def sourceExec {p r r' s:ℕ} (hp:p.Prime) (hp4:p%4=1) (B:ℕ) (t:EncodedFieldTables s)
 (h:Matrix (Fin r) (Fin (p+1)) (Fin s)) (h':Matrix (Fin r') (Fin (p+1)) (Fin s)):
 EvalsToInTime (TM2.step (sourceMachine hp hp4 t h h').program) ((sourceMachine hp hp4 t h h').init (unary B))
 (some ((sourceMachine hp hp4 t h h').halt (sourceOutput hp hp4 B t h h')))
 ((sourceTime hp hp4 t h h').eval (physicalSize (lpsEffectiveResiduePrimeAt hp hp4 B) (p+1) r r')):=
 physicalExec hp hp4 B (by omega) (sourceDirections hp hp4) t h h'
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
namespace QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily
open scoped MatrixGroups
open FiniteFieldPauli
noncomputable local instance _p2m_local_instance_6058dbc402_120 {q D r r':ℕ} [Fact q.Prime]:DecidableEq
 (LiftedProduct.QubitIndex (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod q)):=Classical.decEq _
abbrev PhysicalCount (q D r r':ℕ) [Fact q.Prime]:=D*(D*(lpsPSLList q).length)+(2*r)*((2*r')*(lpsPSLList q).length)
abbrev CheckCount (q D r r' s:ℕ) [Fact q.Prime]:=((2*r)*(D*(lpsPSLList q).length))*s+(D*((2*r')*(lpsPSLList q).length))*s
noncomputable def decodedOperator {q D r r' s:ℕ} [Fact q.Prime] {F:Type} [Field F] [Fintype F]
 (e:Fin s≃F) (t:EncodedFieldTables s) (i:Fin (CheckCount q D r r' s)) (w:List Bool):=
 let rows:=LPSSparseEmitterCodec.rowsOrEmpty (PhysicalCount q D r r') s w
 let word:=lpsEncodedOutputWord e t (rows.getD i.val [])
 match lpsEncodedCheckNumbering.symm i with
 | Sum.inl _=>(registerUnitary (F:=F) (ι':=LiftedProduct.QubitIndex
   (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod q))).conjOperator (shift word)
 | Sum.inr _=>(registerUnitary (F:=F) (ι':=LiftedProduct.QubitIndex
   (Fin 2×Fin r) (Fin D) (Fin D) (Fin 2×Fin r') PSL(2,ZMod q))).conjOperator (phase word)
end QEC.Coding.TannerLiftedProduct.LPSSparseEmitterFamily


