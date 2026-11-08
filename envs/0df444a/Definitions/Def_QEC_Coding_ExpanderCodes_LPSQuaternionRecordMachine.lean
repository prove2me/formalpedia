-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionRecordMachine
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternionRecordMachine
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:59:49.002435+00:00
-- url     : https://prove2.me/theorems/78ddd8d8-3836-4120-b335-096f6cb261ed
-- title:
--   LPSQuaternion Record Machine
-- statement:
--   Definitions and structural lemmas for LPSQuaternion Record Machine, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionRecordMachine.lean

import Definitions.Def_QEC_Coding_BitTuring_UnarySignedCoefficient
import Definitions.Def_QEC_Coding_BitTuring_ModulusQuery
import Definitions.Def_QEC_Coding_BitTuring_BitDelimiters
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSInverseMachine
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSMatrixProductMachine
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
namespace QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition
open FieldProjection
def coordinates {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) :=
  [(t.a:ZMod a.q).val,(t.b:ZMod a.q).val,(t.c:ZMod a.q).val,(t.d:ZMod a.q).val]
def record {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) := stream
  [LPSDegreeInverseMachine.scalar a,lpsEffectiveResiduePairIndex a.q,
   (t.d:ZMod a.q).val,(t.c:ZMod a.q).val,(t.b:ZMod a.q).val,(t.a:ZMod a.q).val,a.q]
def machine (p:ℕ) (t:LPSQuaternion) := Composition.machine BitDelimiter.machine
  (Composition.machine (ModulusQuery.machine 0 (SignedCoefficient.machine t.a))
   (Composition.machine (ModulusQuery.machine 1 (SignedCoefficient.machine t.b))
    (Composition.machine (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
     (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
      (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
       (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p)))))))
noncomputable def bodyTime (p:ℕ) (t:LPSQuaternion) : Polynomial ℕ :=
  SignedCoefficient.time t.a+SignedCoefficient.time t.b+SignedCoefficient.time t.c+SignedCoefficient.time t.d+
  LPSResidueRootMachine.time+LPSDegreeInverseMachine.time p
noncomputable def size : Polynomial ℕ := Polynomial.C 6*(Polynomial.X+1)
noncomputable def time (p:ℕ) (t:LPSQuaternion) : Polynomial ℕ :=
  (bodyTime p t).comp size+Polynomial.C 1000*(Polynomial.X+1)
theorem coordinate_bounds {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    t.a.natAbs<a.q ∧ t.b.natAbs<a.q ∧ t.c.natAbs<a.q ∧ t.d.natAbs<a.q := by
  have h:=coordinate_bounds_of_norm a.degreePrime.pos t ht
  have hp:(p:ℤ)<a.q := by exact_mod_cast (show p<a.q by have := a.large;omega)
  have ha:|t.a|<(a.q:ℤ):=(abs_le.mpr ⟨h.1,h.2.1⟩).trans_lt hp
  have hb:|t.b|<(a.q:ℤ):=(abs_le.mpr ⟨h.2.2.1,h.2.2.2.1⟩).trans_lt hp
  have hc:|t.c|<(a.q:ℤ):=(abs_le.mpr ⟨h.2.2.2.2.1,h.2.2.2.2.2.1⟩).trans_lt hp
  have hd:|t.d|<(a.q:ℤ):=(abs_le.mpr ⟨h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2⟩).trans_lt hp
  rw [←Int.natCast_natAbs] at ha hb hc hd
  exact ⟨by exact_mod_cast ha,by exact_mod_cast hb,by exact_mod_cast hc,by exact_mod_cast hd⟩
noncomputable def coefficientExec {p:ℕ} (a:LPSResiduePrime p) (c:ℤ) (hc:c.natAbs<a.q) :
    EvalsToInTime (TM2.step (SignedCoefficient.machine c).program)
      ((SignedCoefficient.machine c).init (unary a.q))
      (some ((SignedCoefficient.machine c).halt (unary (c:ZMod a.q).val)))
      ((SignedCoefficient.time c).eval a.q) := by
  have h:=SignedCoefficient.exec c a.q hc
  rw [SignedCoefficient.output_eq_val c a.q a.prime.pos hc,unary_length] at h
  exact h
noncomputable def exec {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) := by
  let : NeZero a.q:=⟨a.prime.ne_zero⟩
  let A:=(t.a:ZMod a.q).val
  let B:=(t.b:ZMod a.q).val
  let C:=(t.c:ZMod a.q).val
  let D:=(t.d:ZMod a.q).val
  let Y:=lpsEffectiveResiduePairIndex a.q
  let S:=LPSDegreeInverseMachine.scalar a
  have hb:=coordinate_bounds a t ht
  have hY:Y<a.q := by
    dsimp only [Y]
    rw [←lpsMinusRoot_pair_index a]
    exact SquareRoot.index_lt _ _ _
  have hS:S<a.q:=ZMod.val_lt _
  have h0:=ModulusQuery.exec 0 (SignedCoefficient.machine t.a) (SignedCoefficient.time t.a)
    [a.q] (by simp) a.q A (ZMod.val_lt _)
    (by simp [fields,maskAt,ModulusQuery.mask]) (coefficientExec a t.a hb.1)
  have h1:=ModulusQuery.exec 1 (SignedCoefficient.machine t.b) (SignedCoefficient.time t.b)
    [A,a.q] (by simp) a.q B (ZMod.val_lt _)
    (by simp [fields,maskAt,ModulusQuery.mask]) (coefficientExec a t.b hb.2.1)
  have h2:=ModulusQuery.exec 2 (SignedCoefficient.machine t.c) (SignedCoefficient.time t.c)
    [B,A,a.q] (by simp) a.q C (ZMod.val_lt _)
    (by simp [fields,maskAt,ModulusQuery.mask]) (coefficientExec a t.c hb.2.2.1)
  have h3:=ModulusQuery.exec 3 (SignedCoefficient.machine t.d) (SignedCoefficient.time t.d)
    [C,B,A,a.q] (by simp) a.q D (ZMod.val_lt _)
    (by simp [fields,maskAt,ModulusQuery.mask]) (coefficientExec a t.d hb.2.2.2)
  have h4:=ModulusQuery.exec 4 LPSResidueRootMachine.machine LPSResidueRootMachine.time
    [D,C,B,A,a.q] (by simp) a.q Y hY
    (by simp [fields,maskAt,ModulusQuery.mask]) (by simpa only [unary_length] using LPSResidueRootMachine.polyExec a)
  have h5:=ModulusQuery.exec 5 (LPSDegreeInverseMachine.machine p) (LPSDegreeInverseMachine.time p)
    [Y,D,C,B,A,a.q] (by simp) a.q S hS
    (by simp [fields,maskAt,ModulusQuery.mask]) (by simpa only [unary_length] using LPSDegreeInverseMachine.polyExec a)
  have h45:=Composition.executes (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
    (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p)) _ _ _ _ _ h4 h5
  have h345:=Composition.executes (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
    (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
      (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p))) _ _ _ _ _ h3 h45
  have h2345:=Composition.executes (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
    (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
      (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
       (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p)))) _ _ _ _ _ h2 h345
  have h12345:=Composition.executes (ModulusQuery.machine 1 (SignedCoefficient.machine t.b))
    (Composition.machine (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
     (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
      (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
       (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p))))) _ _ _ _ _ h1 h2345
  have h012345:=Composition.executes (ModulusQuery.machine 0 (SignedCoefficient.machine t.a))
    (Composition.machine (ModulusQuery.machine 1 (SignedCoefficient.machine t.b))
     (Composition.machine (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
      (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
       (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
        (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p)))))) _ _ _ _ _ h0 h12345
  have hd:=BitDelimiter.exec (unary a.q)
  rw [show unary a.q++[false]=stream [a.q] by simp [stream]] at hd
  exact Composition.executes BitDelimiter.machine
    (Composition.machine (ModulusQuery.machine 0 (SignedCoefficient.machine t.a))
     (Composition.machine (ModulusQuery.machine 1 (SignedCoefficient.machine t.b))
      (Composition.machine (ModulusQuery.machine 2 (SignedCoefficient.machine t.c))
       (Composition.machine (ModulusQuery.machine 3 (SignedCoefficient.machine t.d))
        (Composition.machine (ModulusQuery.machine 4 LPSResidueRootMachine.machine)
         (ModulusQuery.machine 5 (LPSDegreeInverseMachine.machine p))))))) _ _ _ _ _ hd h012345
noncomputable def polyExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    EvalsToInTime (TM2.step (machine p t).program) ((machine p t).init (unary a.q))
      (some ((machine p t).halt (record a t))) ((time p t).eval (unary a.q).length) := by
  have h:=exec a t ht
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  let : NeZero a.q:=⟨a.prime.ne_zero⟩
  let A:=(t.a:ZMod a.q).val
  let B:=(t.b:ZMod a.q).val
  let C:=(t.c:ZMod a.q).val
  let D:=(t.d:ZMod a.q).val
  let Y:=lpsEffectiveResiduePairIndex a.q
  have hA:A<a.q:=ZMod.val_lt _
  have hB:B<a.q:=ZMod.val_lt _
  have hC:C<a.q:=ZMod.val_lt _
  have hD:D<a.q:=ZMod.val_lt _
  have hY:Y<a.q := by
    dsimp only [Y]
    rw [←lpsMinusRoot_pair_index a]
    exact SquareRoot.index_lt _ _ _
  have hL0:(stream [a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp0:(SignedCoefficient.time t.a).eval (stream [a.q]).length≤(SignedCoefficient.time t.a).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (SignedCoefficient.time t.a) hL0
  have hL1:(stream [A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp1:(SignedCoefficient.time t.b).eval (stream [A,a.q]).length≤(SignedCoefficient.time t.b).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (SignedCoefficient.time t.b) hL1
  have hL2:(stream [B,A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp2:(SignedCoefficient.time t.c).eval (stream [B,A,a.q]).length≤(SignedCoefficient.time t.c).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (SignedCoefficient.time t.c) hL2
  have hL3:(stream [C,B,A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp3:(SignedCoefficient.time t.d).eval (stream [C,B,A,a.q]).length≤(SignedCoefficient.time t.d).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (SignedCoefficient.time t.d) hL3
  have hL4:(stream [D,C,B,A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp4:(LPSResidueRootMachine.time).eval (stream [D,C,B,A,a.q]).length≤(LPSResidueRootMachine.time).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (LPSResidueRootMachine.time) hL4
  have hL5:(stream [Y,D,C,B,A,a.q]).length≤6*(a.q+1) := by
    simp only [stream_length,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil];omega
  have hp5:(LPSDegreeInverseMachine.time p).eval (stream [Y,D,C,B,A,a.q]).length≤(LPSDegreeInverseMachine.time p).eval (6*(a.q+1)) :=
    Composition.polynomial_eval_monotone (LPSDegreeInverseMachine.time p) hL5

  change (ModulusQuery.time (LPSDegreeInverseMachine.time p)).eval (stream [Y,D,C,B,A,a.q]).length+
    (2*(stream [Y,D,C,B,A,a.q]).length+2)+
    (ModulusQuery.time LPSResidueRootMachine.time).eval (stream [D,C,B,A,a.q]).length+
    (2*(stream [D,C,B,A,a.q]).length+2)+
    (ModulusQuery.time (SignedCoefficient.time t.d)).eval (stream [C,B,A,a.q]).length+
    (2*(stream [C,B,A,a.q]).length+2)+
    (ModulusQuery.time (SignedCoefficient.time t.c)).eval (stream [B,A,a.q]).length+
    (2*(stream [B,A,a.q]).length+2)+
    (ModulusQuery.time (SignedCoefficient.time t.b)).eval (stream [A,a.q]).length+
    (2*(stream [A,a.q]).length+2)+
    (ModulusQuery.time (SignedCoefficient.time t.a)).eval (stream [a.q]).length+
    (2*(stream [a.q]).length+2)+(2*(unary a.q).length+3)≤(time p t).eval (unary a.q).length
  simp only [time,bodyTime,size,ModulusQuery.time,Polynomial.eval_comp,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,unary_length]
  omega
noncomputable def outputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    TM2OutputsInTime (machine p t).toFinTM2 (unary a.q) (some (record a t))
      ((time p t).eval (unary a.q).length) :=
  Machine.outputsInTime (machine p t) _ _ _ (polyExec a t ht)
noncomputable def computableInPolyTime (p:ℕ) (t:LPSQuaternion) (ht:t.norm=p) :
    TM2ComputableInPolyTime (fun a:LPSResiduePrime p=>unary a.q) id (fun a=>record a t) where
  tm:=(machine p t).toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time p t
  outputsFun:=fun a=>by
    change TM2OutputsInTime (machine p t).toFinTM2 (List.map id (unary a.q))
      (some (List.map id (record a t))) ((time p t).eval (unary a.q).length)
    have h:=outputsInTime a t ht
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id] using h
open scoped MatrixGroups
noncomputable def blockExec {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    EvalsToInTime (TM2.step (machine p t).program) ((machine p t).init (unary a.q))
      (some ((machine p t).halt (record a t))) ((time p t).eval (2*Fintype.card PSL(2,ZMod a.q))) := by
  have h:=polyExec a t ht
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  rw [unary_length]
  exact Composition.polynomial_eval_monotone (time p t) a.q_le_two_mul_card_psl
noncomputable def blockOutputsInTime {p:ℕ} (a:LPSResiduePrime p) (t:LPSQuaternion) (ht:t.norm=p) :
    TM2OutputsInTime (machine p t).toFinTM2 (unary a.q) (some (record a t))
      ((time p t).eval (2*Fintype.card PSL(2,ZMod a.q))) :=
  Machine.outputsInTime (machine p t) _ _ _ (blockExec a t ht)
end QEC.Coding.TannerLiftedProduct.LPSQuaternionRecordMachine


