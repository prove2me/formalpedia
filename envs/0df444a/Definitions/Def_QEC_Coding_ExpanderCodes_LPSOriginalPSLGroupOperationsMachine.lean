-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLGroupOperationsMachine
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPSLGroupOperationsMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:02:34.684645+00:00
-- url     : https://prove2.me/theorems/00626138-f502-4830-9d03-12748cfcdcff
-- title:
--   LPSOriginal PSLGroup Operations Machine
-- statement:
--   Definitions and structural lemmas for LPSOriginal PSLGroup Operations Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPSLGroupOperationsMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryRetainedFieldComputation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPSLLookupMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSLInverseMachine
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSOriginalPSLLookupMachine_representative_decode
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
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Inverse
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance _p2m_local_instance_7fc643cdab_25:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
abbrev Input:=LPSOriginalPSLLookupMachine.Input
instance (a:Input):Fact a.1.val.Prime:=⟨a.1.property⟩
def matrix (a:Input):SL(2,ZMod a.1.val):=LPSOriginalPSLLookupMachine.representative a.1.val a.2
def input (a:Input):List Bool:=stream [a.2.val,a.1.val]
def afterLookup (a:Input):List ℕ:=coords a.1.val (matrix a)++[a.2.val,a.1.val]
def lookup:=RetainedFieldComputation.machine 1 (PrefixProjection.allMask 1) LPSOriginalPSLLookupMachine.machine
noncomputable def lookupTime:=RetainedFieldComputation.time 1 (PrefixProjection.allMask 1) LPSOriginalPSLLookupMachine.machine LPSOriginalPSLLookupMachine.time
noncomputable def lookupExec (a:Input):
 EvalsToInTime (TM2.step lookup.program) (lookup.init (input a))
 (some (lookup.halt (stream (afterLookup a)))) (lookupTime.eval (input a).length):=by
 have ha:=LPSOriginalPSLLookupMachine.exec a
 have hf:fields 1 (PrefixProjection.allMask 1) 0 [a.2.val,a.1.val]=[a.2.val,a.1.val]:=PrefixProjection.fields_all 1 0 _
 have hb:EvalsToInTime (TM2.step LPSOriginalPSLLookupMachine.machine.program)
  (LPSOriginalPSLLookupMachine.machine.init (raw (fields 1 (PrefixProjection.allMask 1) 0 [a.2.val,a.1.val])))
  (some (LPSOriginalPSLLookupMachine.machine.halt (raw (coords a.1.val (matrix a)))))
  (LPSOriginalPSLLookupMachine.time.eval (raw (fields 1 (PrefixProjection.allMask 1) 0 [a.2.val,a.1.val])).length):=by
  rw [hf]
  exact ha
 have h:=RetainedFieldComputation.exec 1 (PrefixProjection.allMask 1) LPSOriginalPSLLookupMachine.machine
  [a.2.val,a.1.val] (coords a.1.val (matrix a)) (by rfl) (by simp [coords,LPSMatrixProductMachine.fields]) LPSOriginalPSLLookupMachine.time hb
 have he:stream (coords a.1.val (matrix a))++stream [a.2.val,a.1.val]=stream (afterLookup a):=by
  rw [afterLookup,MatrixListQuery.stream_append]
 rw [he] at h
 exact h
def inverseMask (k:Fin 6):Bool:=decide (k.val<4∨k.val=5)
theorem inverse_fields (a:Input):fields 5 inverseMask 0 (afterLookup a)=coords a.1.val (matrix a)++[a.1.val]:=by
 simp [afterLookup,coords,LPSMatrixProductMachine.fields,fields,maskAt,inverseMask]
def prepare:=RetainedFieldComputation.projectedMarked 5 inverseMask
noncomputable def prepareTime:=RetainedFieldComputation.projectedMarkedTime 5 inverseMask
noncomputable def prepareExec (a:Input):
 EvalsToInTime (TM2.step prepare.program) (prepare.init (stream (afterLookup a)))
 (some (prepare.halt (LPSSLInverseMachine.input a.1.val (matrix a)))) (prepareTime.eval (stream (afterLookup a)).length):=by
 have h:=RetainedFieldComputation.projectedMarkedExec 5 inverseMask (afterLookup a)
  (by simp [afterLookup,coords,LPSMatrixProductMachine.fields]) (by rw [inverse_fields];simp)
 rw [inverse_fields] at h
 exact h
def afterInverse (a:Input):List ℕ:=coords a.1.val ((matrix a)⁻¹)++coords a.1.val (matrix a)++[a.1.val]
def invert:=RetainedFieldComputation.retainedMarked ModularAdjugate.inverseMachine
noncomputable def invertTime:=RetainedFieldComputation.retainedMarkedTime ModularAdjugate.inverseMachine ModularAdjugate.time
noncomputable def invertExec (a:Input):
 EvalsToInTime (TM2.step invert.program) (invert.init (LPSSLInverseMachine.input a.1.val (matrix a)))
 (some (invert.halt (stream (afterInverse a)))) (invertTime.eval (LPSSLInverseMachine.input a.1.val (matrix a)).length):=by
 have h:=RetainedFieldComputation.retainedMarkedExec ModularAdjugate.inverseMachine
  (LPSSLInverseMachine.input a.1.val (matrix a)) (coords a.1.val ((matrix a)⁻¹))
  (by simp [coords,LPSMatrixProductMachine.fields]) ModularAdjugate.time (LPSSLInverseMachine.polyExec a.1.val a.1.property.pos (matrix a))
 have he:stream (coords a.1.val ((matrix a)⁻¹))++LPSSLInverseMachine.input a.1.val (matrix a)=stream (afterInverse a):=by
  simp only [LPSSLInverseMachine.input,coords,afterInverse,MatrixListQuery.stream_append,List.append_assoc]
 rw [he] at h
 exact h
def retainModulus:=ModularAdjugate.retainedUnary 8 (ModulusQuery.mask 8)
noncomputable def retainModulusExec (a:Input):
 EvalsToInTime (TM2.step retainModulus.program) (retainModulus.init (stream (afterInverse a)))
 (some (retainModulus.halt (stream (a.1.val::afterInverse a))))
 (ModularAdjugate.stageTime.eval (stream (afterInverse a)).length):=by
 have hh:(coords a.1.val ((matrix a)⁻¹)++coords a.1.val (matrix a)).length=8:=by simp [coords,LPSMatrixProductMachine.fields]
 exact ModularAdjugate.unaryStageExec 8 (ModulusQuery.mask 8) (afterInverse a)
  (by simp [afterInverse,coords,LPSMatrixProductMachine.fields]) a.1.val (MatrixListQuery.selectLast 8 0 _ a.1.val (by simpa using hh))
def firstFive (k:Fin 10):Bool:=decide (k.val<5)
theorem first_five_fields (a:Input):fields 9 firstFive 0 (a.1.val::afterInverse a)=a.1.val::coords a.1.val ((matrix a)⁻¹):=by
 simp [afterInverse,coords,LPSMatrixProductMachine.fields,fields,maskAt,firstFive]
def prepareIndex:=RetainedFieldComputation.projectedReverse 9 firstFive
noncomputable def prepareIndexTime:=RetainedFieldComputation.projectedReverseTime 9 firstFive
noncomputable def prepareIndexExec (a:Input):
 EvalsToInTime (TM2.step prepareIndex.program) (prepareIndex.init (stream (a.1.val::afterInverse a)))
 (some (prepareIndex.halt (LPSOriginalPSLIndexMachine.input ⟨a.1,(matrix a)⁻¹⟩)))
 (prepareIndexTime.eval (stream (a.1.val::afterInverse a)).length):=by
 have h:=RetainedFieldComputation.projectedReverseExec 9 firstFive (a.1.val::afterInverse a)
  (by simp [afterInverse,coords,LPSMatrixProductMachine.fields])
 rw [first_five_fields] at h
 have he:(raw (a.1.val::coords a.1.val ((matrix a)⁻¹))).reverse=LPSOriginalPSLIndexMachine.input ⟨a.1,(matrix a)⁻¹⟩:=by
  have hi:=LPSOriginalPSLIndexMachine.Initializer.input_reverse ⟨a.1,(matrix a)⁻¹⟩
  change (LPSOriginalPSLIndexMachine.Initializer.input ⟨a.1,(matrix a)⁻¹⟩).reverse=raw (a.1.val::coords a.1.val ((matrix a)⁻¹)) at hi
  rw [←hi,List.reverse_reverse]
  rfl
 rw [he] at h
 exact h
def output (a:Input):List Bool:=unary (lpsPSLIndexInv a.1.val a.2).val
theorem source_output (a:Input):LPSOriginalPSLIndexMachine.output ⟨a.1,(matrix a)⁻¹⟩=output a:=by
 have hi:quotient a.1.val ((matrix a)⁻¹)=(quotient a.1.val (matrix a))⁻¹:=by simp [quotient]
 have hd:quotient a.1.val (matrix a)=lpsPSLEnumerationEquiv a.1.val a.2:=LPSOriginalPSLLookupMachine.representative_decode _ _
 simp only [LPSOriginalPSLIndexMachine.output,hi,hd,output,lpsPSLIndexInv]
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Inverse
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Inverse
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance _p2m_local_instance_7fc643cdab_137:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
def indexed:=Composition.machine prepareIndex LPSOriginalPSLIndexMachine.machine
noncomputable def indexedTime:=Composition.timePolynomial prepareIndex prepareIndexTime LPSOriginalPSLIndexMachine.time
noncomputable def indexedExec (a:Input):
 EvalsToInTime (TM2.step indexed.program) (indexed.init (stream (a.1.val::afterInverse a)))
 (some (indexed.halt (output a))) (indexedTime.eval (stream (a.1.val::afterInverse a)).length):=by
 have h:=LPSOriginalPSLIndexMachine.exec ⟨a.1,(matrix a)⁻¹⟩
 rw [source_output] at h
 exact RetainedFieldComputation.composeRuns prepareIndex LPSOriginalPSLIndexMachine.machine _ _ _ prepareIndexTime LPSOriginalPSLIndexMachine.time (prepareIndexExec a) h
def modulusAndIndex:=Composition.machine retainModulus indexed
noncomputable def modulusAndIndexTime:=Composition.timePolynomial retainModulus ModularAdjugate.stageTime indexedTime
noncomputable def modulusAndIndexExec (a:Input):
 EvalsToInTime (TM2.step modulusAndIndex.program) (modulusAndIndex.init (stream (afterInverse a)))
 (some (modulusAndIndex.halt (output a))) (modulusAndIndexTime.eval (stream (afterInverse a)).length):=
 RetainedFieldComputation.composeRuns retainModulus indexed _ _ _ ModularAdjugate.stageTime indexedTime (retainModulusExec a) (indexedExec a)
def inversionAndIndex:=Composition.machine invert modulusAndIndex
noncomputable def inversionAndIndexTime:=Composition.timePolynomial invert invertTime modulusAndIndexTime
noncomputable def inversionAndIndexExec (a:Input):
 EvalsToInTime (TM2.step inversionAndIndex.program) (inversionAndIndex.init (LPSSLInverseMachine.input a.1.val (matrix a)))
 (some (inversionAndIndex.halt (output a))) (inversionAndIndexTime.eval (LPSSLInverseMachine.input a.1.val (matrix a)).length):=
 RetainedFieldComputation.composeRuns invert modulusAndIndex _ _ _ invertTime modulusAndIndexTime (invertExec a) (modulusAndIndexExec a)
def preparedInverseIndex:=Composition.machine prepare inversionAndIndex
noncomputable def preparedInverseIndexTime:=Composition.timePolynomial prepare prepareTime inversionAndIndexTime
noncomputable def preparedInverseIndexExec (a:Input):
 EvalsToInTime (TM2.step preparedInverseIndex.program) (preparedInverseIndex.init (stream (afterLookup a)))
 (some (preparedInverseIndex.halt (output a))) (preparedInverseIndexTime.eval (stream (afterLookup a)).length):=
 RetainedFieldComputation.composeRuns prepare inversionAndIndex _ _ _ prepareTime inversionAndIndexTime (prepareExec a) (inversionAndIndexExec a)
def machine:=Composition.machine lookup preparedInverseIndex
noncomputable def time:=Composition.timePolynomial lookup lookupTime preparedInverseIndexTime
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
 (some (machine.halt (output a))) (time.eval (input a).length):=
 RetainedFieldComputation.composeRuns lookup preparedInverseIndex _ _ _ lookupTime preparedInverseIndexTime (lookupExec a) (preparedInverseIndexExec a)
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
theorem input_length (a:Input):(input a).length=a.2.val+a.1.val+2:=by
 simp only [input,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
 omega
noncomputable def blockTime:Polynomial ℕ:=time.comp (Polynomial.C 3*Polynomial.X+Polynomial.C 2)
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (i:Fin (lpsPSLList a.q).length):
 EvalsToInTime (TM2.step machine.program) (machine.init (input ⟨⟨a.q,a.prime⟩,i⟩))
 (some (machine.halt (output ⟨⟨a.q,a.prime⟩,i⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨⟨a.q,a.prime⟩,i⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hL:(input ⟨⟨a.q,a.prime⟩,i⟩).length≤3*Fintype.card PSL(2,ZMod a.q)+2:=by
  rw [input_length]
  change i.val+a.q+2≤3*Fintype.card PSL(2,ZMod a.q)+2
  have hi:i.val<Fintype.card PSL(2,ZMod a.q):=i.isLt.trans_le (LPSOriginalPSLLookupMachine.original_length_card a.q).le
  have hq:=a.q_le_two_mul_card_psl
  omega
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time hL
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (i:Fin (lpsPSLList a.q).length):
 TM2OutputsInTime machine.toFinTM2 (input ⟨⟨a.q,a.prime⟩,i⟩) (some (output ⟨⟨a.q,a.prime⟩,i⟩))
 (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a i)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Inverse
namespace QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Multiply
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
open QEC.Coding.TannerLiftedProduct.LPSPSLSearchMachine
open scoped MatrixGroups
local instance _p2m_local_instance_7fc643cdab_248:Fact (Even (Fintype.card (Fin 2))):=⟨by simp⟩
abbrev Input:=Σ q:{q:ℕ//q.Prime},Fin (lpsPSLList q.val).length×Fin (lpsPSLList q.val).length
instance (a:Input):Fact a.1.val.Prime:=⟨a.1.property⟩
def left (a:Input):SL(2,ZMod a.1.val):=LPSOriginalPSLLookupMachine.representative a.1.val a.2.1
def right (a:Input):SL(2,ZMod a.1.val):=LPSOriginalPSLLookupMachine.representative a.1.val a.2.2
def input (a:Input):List Bool:=stream [a.2.1.val,a.2.2.val,a.1.val]
def afterRight (a:Input):List ℕ:=coords a.1.val (right a)++[a.2.1.val,a.2.2.val,a.1.val]
def rightMask (k:Fin 3):Bool:=decide (1≤k.val)
theorem right_fields (a:Input):fields 2 rightMask 0 [a.2.1.val,a.2.2.val,a.1.val]=[a.2.2.val,a.1.val]:=by
 simp [fields,maskAt,rightMask]
def lookupRight:=RetainedFieldComputation.machine 2 rightMask LPSOriginalPSLLookupMachine.machine
noncomputable def lookupRightTime:=RetainedFieldComputation.time 2 rightMask LPSOriginalPSLLookupMachine.machine LPSOriginalPSLLookupMachine.time
noncomputable def lookupRightExec (a:Input):
 EvalsToInTime (TM2.step lookupRight.program) (lookupRight.init (input a))
 (some (lookupRight.halt (stream (afterRight a)))) (lookupRightTime.eval (input a).length):=by
 have hb:EvalsToInTime (TM2.step LPSOriginalPSLLookupMachine.machine.program)
  (LPSOriginalPSLLookupMachine.machine.init (raw (fields 2 rightMask 0 [a.2.1.val,a.2.2.val,a.1.val])))
  (some (LPSOriginalPSLLookupMachine.machine.halt (raw (coords a.1.val (right a)))))
  (LPSOriginalPSLLookupMachine.time.eval (raw (fields 2 rightMask 0 [a.2.1.val,a.2.2.val,a.1.val])).length):=by
  rw [right_fields]
  exact LPSOriginalPSLLookupMachine.exec ⟨a.1,a.2.2⟩
 have h:=RetainedFieldComputation.exec 2 rightMask LPSOriginalPSLLookupMachine.machine
  [a.2.1.val,a.2.2.val,a.1.val] (coords a.1.val (right a)) (by rfl)
  (by simp [coords,LPSMatrixProductMachine.fields]) LPSOriginalPSLLookupMachine.time hb
 have he:stream (coords a.1.val (right a))++stream [a.2.1.val,a.2.2.val,a.1.val]=stream (afterRight a):=by
  rw [afterRight,MatrixListQuery.stream_append]
 rw [he] at h
 exact h
def afterLeft (a:Input):List ℕ:=coords a.1.val (left a)++afterRight a
def leftMask (k:Fin 7):Bool:=decide (k.val=4∨k.val=6)
theorem left_fields (a:Input):fields 6 leftMask 0 (afterRight a)=[a.2.1.val,a.1.val]:=by
 simp [afterRight,coords,LPSMatrixProductMachine.fields,fields,maskAt,leftMask]
def lookupLeft:=RetainedFieldComputation.machine 6 leftMask LPSOriginalPSLLookupMachine.machine
noncomputable def lookupLeftTime:=RetainedFieldComputation.time 6 leftMask LPSOriginalPSLLookupMachine.machine LPSOriginalPSLLookupMachine.time
noncomputable def lookupLeftExec (a:Input):
 EvalsToInTime (TM2.step lookupLeft.program) (lookupLeft.init (stream (afterRight a)))
 (some (lookupLeft.halt (stream (afterLeft a)))) (lookupLeftTime.eval (stream (afterRight a)).length):=by
 have hb:EvalsToInTime (TM2.step LPSOriginalPSLLookupMachine.machine.program)
  (LPSOriginalPSLLookupMachine.machine.init (raw (fields 6 leftMask 0 (afterRight a))))
  (some (LPSOriginalPSLLookupMachine.machine.halt (raw (coords a.1.val (left a)))))
  (LPSOriginalPSLLookupMachine.time.eval (raw (fields 6 leftMask 0 (afterRight a))).length):=by
  rw [left_fields]
  exact LPSOriginalPSLLookupMachine.exec ⟨a.1,a.2.1⟩
 have h:=RetainedFieldComputation.exec 6 leftMask LPSOriginalPSLLookupMachine.machine
  (afterRight a) (coords a.1.val (left a)) (by simp [afterRight,coords,LPSMatrixProductMachine.fields])
  (by simp [coords,LPSMatrixProductMachine.fields]) LPSOriginalPSLLookupMachine.time hb
 have he:stream (coords a.1.val (left a))++stream (afterRight a)=stream (afterLeft a):=by
  rw [afterLeft,MatrixListQuery.stream_append]
 rw [he] at h
 exact h
def productMask (k:Fin 11):Bool:=decide (k.val<8∨k.val=10)
theorem product_fields (a:Input):fields 10 productMask 0 (afterLeft a)=coords a.1.val (left a)++coords a.1.val (right a)++[a.1.val]:=by
 simp [afterLeft,afterRight,coords,LPSMatrixProductMachine.fields,fields,maskAt,productMask]
def prepare:=RetainedFieldComputation.projectedMarked 10 productMask
noncomputable def prepareTime:=RetainedFieldComputation.projectedMarkedTime 10 productMask
noncomputable def prepareExec (a:Input):
 EvalsToInTime (TM2.step prepare.program) (prepare.init (stream (afterLeft a)))
 (some (prepare.halt (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val)))
 (prepareTime.eval (stream (afterLeft a)).length):=by
 have h:=RetainedFieldComputation.projectedMarkedExec 10 productMask (afterLeft a)
  (by simp [afterLeft,afterRight,coords,LPSMatrixProductMachine.fields]) (by rw [product_fields];simp [coords,LPSMatrixProductMachine.fields])
 rw [product_fields] at h
 exact h
def afterProduct (a:Input):List ℕ:=coords a.1.val (left a*right a)++coords a.1.val (left a)++coords a.1.val (right a)++[a.1.val]
def product:=RetainedFieldComputation.retainedMarked ModularMatrixProduct.productMachine
noncomputable def productTime:=RetainedFieldComputation.retainedMarkedTime ModularMatrixProduct.productMachine ModularMatrixProduct.time
noncomputable def productExec (a:Input):
 EvalsToInTime (TM2.step product.program) (product.init (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val))
 (some (product.halt (stream (afterProduct a))))
 (productTime.eval (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val).length):=by
 have h:=RetainedFieldComputation.retainedMarkedExec ModularMatrixProduct.productMachine
  (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val) (coords a.1.val (left a*right a))
  (by simp [coords,LPSMatrixProductMachine.fields]) ModularMatrixProduct.time (LPSMatrixProductMachine.slExec a.1.val a.1.property.pos (left a) (right a))
 have he:stream (coords a.1.val (left a*right a))++LPSMatrixProductMachine.input a.1.val (left a).val (right a).val=stream (afterProduct a):=by
  simp only [LPSMatrixProductMachine.input,coords,afterProduct,MatrixListQuery.stream_append,List.append_assoc]
 rw [he] at h
 exact h
def retainModulus:=ModularAdjugate.retainedUnary 12 (ModulusQuery.mask 12)
noncomputable def retainModulusExec (a:Input):
 EvalsToInTime (TM2.step retainModulus.program) (retainModulus.init (stream (afterProduct a)))
 (some (retainModulus.halt (stream (a.1.val::afterProduct a))))
 (ModularAdjugate.stageTime.eval (stream (afterProduct a)).length):=by
 exact ModularAdjugate.unaryStageExec 12 (ModulusQuery.mask 12) (afterProduct a)
  (by simp [afterProduct,coords,LPSMatrixProductMachine.fields]) a.1.val
  (MatrixListQuery.selectLast 12 0 (coords a.1.val (left a*right a)++coords a.1.val (left a)++coords a.1.val (right a)) a.1.val (by simp [coords,LPSMatrixProductMachine.fields]))
def firstFive (k:Fin 14):Bool:=decide (k.val<5)
theorem first_five_fields (a:Input):fields 13 firstFive 0 (a.1.val::afterProduct a)=a.1.val::coords a.1.val (left a*right a):=by
 simp [afterProduct,coords,LPSMatrixProductMachine.fields,fields,maskAt,firstFive]
def prepareIndex:=RetainedFieldComputation.projectedReverse 13 firstFive
noncomputable def prepareIndexTime:=RetainedFieldComputation.projectedReverseTime 13 firstFive
noncomputable def prepareIndexExec (a:Input):
 EvalsToInTime (TM2.step prepareIndex.program) (prepareIndex.init (stream (a.1.val::afterProduct a)))
 (some (prepareIndex.halt (LPSOriginalPSLIndexMachine.input ⟨a.1,left a*right a⟩)))
 (prepareIndexTime.eval (stream (a.1.val::afterProduct a)).length):=by
 have h:=RetainedFieldComputation.projectedReverseExec 13 firstFive (a.1.val::afterProduct a)
  (by simp [afterProduct,coords,LPSMatrixProductMachine.fields])
 rw [first_five_fields] at h
 have he:(raw (a.1.val::coords a.1.val (left a*right a))).reverse=LPSOriginalPSLIndexMachine.input ⟨a.1,left a*right a⟩:=by
  have hi:=LPSOriginalPSLIndexMachine.Initializer.input_reverse ⟨a.1,left a*right a⟩
  change (LPSOriginalPSLIndexMachine.Initializer.input ⟨a.1,left a*right a⟩).reverse=raw (a.1.val::coords a.1.val (left a*right a)) at hi
  rw [←hi,List.reverse_reverse]
  rfl
 rw [he] at h
 exact h
def output (a:Input):List Bool:=unary (lpsPSLIndexMul a.1.val a.2.1 a.2.2).val
theorem source_output (a:Input):LPSOriginalPSLIndexMachine.output ⟨a.1,left a*right a⟩=output a:=by
 have hi:quotient a.1.val (left a*right a)=quotient a.1.val (left a)*quotient a.1.val (right a):=by simp [quotient]
 have hl:quotient a.1.val (left a)=lpsPSLEnumerationEquiv a.1.val a.2.1:=LPSOriginalPSLLookupMachine.representative_decode _ _
 have hr:quotient a.1.val (right a)=lpsPSLEnumerationEquiv a.1.val a.2.2:=LPSOriginalPSLLookupMachine.representative_decode _ _
 simp only [LPSOriginalPSLIndexMachine.output,hi,hl,hr,output,lpsPSLIndexMul]
def indexed:=Composition.machine prepareIndex LPSOriginalPSLIndexMachine.machine
noncomputable def indexedTime:=Composition.timePolynomial prepareIndex prepareIndexTime LPSOriginalPSLIndexMachine.time
noncomputable def indexedExec (a:Input):
 EvalsToInTime (TM2.step indexed.program) (indexed.init (stream (a.1.val::afterProduct a)))
 (some (indexed.halt (output a))) (indexedTime.eval (stream (a.1.val::afterProduct a)).length):=by
 have h:=LPSOriginalPSLIndexMachine.exec ⟨a.1,left a*right a⟩
 rw [source_output] at h
 exact RetainedFieldComputation.composeRuns prepareIndex LPSOriginalPSLIndexMachine.machine _ _ _ prepareIndexTime LPSOriginalPSLIndexMachine.time (prepareIndexExec a) (h)
def modulusAndIndex:=Composition.machine retainModulus indexed
noncomputable def modulusAndIndexTime:=Composition.timePolynomial retainModulus ModularAdjugate.stageTime indexedTime
noncomputable def modulusAndIndexExec (a:Input):
 EvalsToInTime (TM2.step modulusAndIndex.program) (modulusAndIndex.init (stream (afterProduct a)))
 (some (modulusAndIndex.halt (output a))) (modulusAndIndexTime.eval (stream (afterProduct a)).length):=
 RetainedFieldComputation.composeRuns retainModulus indexed _ _ _ ModularAdjugate.stageTime indexedTime (retainModulusExec a) (indexedExec a)
def productAndIndex:=Composition.machine product modulusAndIndex
noncomputable def productAndIndexTime:=Composition.timePolynomial product productTime modulusAndIndexTime
noncomputable def productAndIndexExec (a:Input):
 EvalsToInTime (TM2.step productAndIndex.program) (productAndIndex.init (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val))
 (some (productAndIndex.halt (output a))) (productAndIndexTime.eval (LPSMatrixProductMachine.input a.1.val (left a).val (right a).val).length):=
 RetainedFieldComputation.composeRuns product modulusAndIndex _ _ _ productTime modulusAndIndexTime (productExec a) (modulusAndIndexExec a)
def preparedProductIndex:=Composition.machine prepare productAndIndex
noncomputable def preparedProductIndexTime:=Composition.timePolynomial prepare prepareTime productAndIndexTime
noncomputable def preparedProductIndexExec (a:Input):
 EvalsToInTime (TM2.step preparedProductIndex.program) (preparedProductIndex.init (stream (afterLeft a)))
 (some (preparedProductIndex.halt (output a))) (preparedProductIndexTime.eval (stream (afterLeft a)).length):=
 RetainedFieldComputation.composeRuns prepare productAndIndex _ _ _ prepareTime productAndIndexTime (prepareExec a) (productAndIndexExec a)
def leftAndProductIndex:=Composition.machine lookupLeft preparedProductIndex
noncomputable def leftAndProductIndexTime:=Composition.timePolynomial lookupLeft lookupLeftTime preparedProductIndexTime
noncomputable def leftAndProductIndexExec (a:Input):
 EvalsToInTime (TM2.step leftAndProductIndex.program) (leftAndProductIndex.init (stream (afterRight a)))
 (some (leftAndProductIndex.halt (output a))) (leftAndProductIndexTime.eval (stream (afterRight a)).length):=
 RetainedFieldComputation.composeRuns lookupLeft preparedProductIndex _ _ _ lookupLeftTime preparedProductIndexTime (lookupLeftExec a) (preparedProductIndexExec a)
def machine:=Composition.machine lookupRight leftAndProductIndex
noncomputable def time:=Composition.timePolynomial lookupRight lookupRightTime leftAndProductIndexTime
noncomputable def exec (a:Input):
 EvalsToInTime (TM2.step machine.program) (machine.init (input a))
 (some (machine.halt (output a))) (time.eval (input a).length):=
 RetainedFieldComputation.composeRuns lookupRight leftAndProductIndex _ _ _ lookupRightTime leftAndProductIndexTime (lookupRightExec a) (leftAndProductIndexExec a)
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
theorem input_length (a:Input):(input a).length=a.2.1.val+a.2.2.val+a.1.val+3:=by
 simp only [input,stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
 omega
noncomputable def blockTime:Polynomial ℕ:=time.comp (Polynomial.C 4*Polynomial.X+Polynomial.C 3)
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (i j:Fin (lpsPSLList a.q).length):
 EvalsToInTime (TM2.step machine.program) (machine.init (input ⟨⟨a.q,a.prime⟩,i,j⟩))
 (some (machine.halt (output ⟨⟨a.q,a.prime⟩,i,j⟩))) (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=by
 have h:=exec ⟨⟨a.q,a.prime⟩,i,j⟩
 refine {h with steps_le_m:=h.steps_le_m.trans ?_}
 have hL:(input ⟨⟨a.q,a.prime⟩,i,j⟩).length≤4*Fintype.card PSL(2,ZMod a.q)+3:=by
  rw [input_length]
  change i.val+j.val+a.q+3≤4*Fintype.card PSL(2,ZMod a.q)+3
  have hi:i.val<Fintype.card PSL(2,ZMod a.q):=i.isLt.trans_le (LPSOriginalPSLLookupMachine.original_length_card a.q).le
  have hj:j.val<Fintype.card PSL(2,ZMod a.q):=j.isLt.trans_le (LPSOriginalPSLLookupMachine.original_length_card a.q).le
  have hq:=a.q_le_two_mul_card_psl
  omega
 simp only [blockTime,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
 exact Composition.polynomial_eval_monotone time hL
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (i j:Fin (lpsPSLList a.q).length):
 TM2OutputsInTime machine.toFinTM2 (input ⟨⟨a.q,a.prime⟩,i,j⟩) (some (output ⟨⟨a.q,a.prime⟩,i,j⟩))
 (blockTime.eval (Fintype.card PSL(2,ZMod a.q))):=
 Machine.outputsInTime machine _ _ _ (blockExec a i j)
end QEC.Coding.TannerLiftedProduct.LPSOriginalPSLGroupOperationsMachine.Multiply


