-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternionPrimeFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:44:22.239642+00:00
-- url     : https://prove2.me/theorems/b624b1b4-273b-4f54-b8d1-de85d415de32
-- title:
--   LPSQuaternion Prime Factor
-- statement:
--   Definitions and structural lemmas for LPSQuaternion Prime Factor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionPrimeFactor.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_firstRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_firstZeroExtension
import Theorems.Thm_QEC_Coding_LiftedProduct_secondRestriction_secondZeroExtension
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Coding_SmallSetExpansion_meanZeroAdjacency_apply_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPositiveTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_succ_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_right
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qBinom_zero_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_qPochhammer_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyConstantProjection_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyHeckeElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyRightRegularRepresentation_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyVectorWordProduct_lps_backtrack
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coe_lpsQuaternionAwayWordProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiGeometricSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiLambertTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiSignedCubeSeriesRaw
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsBacktrackingPrefixEquiv_symm_product
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFiniteHeckeElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPGLHeckeLabel_eq_toPGL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrefixTerm_backtrackingPrefixEquiv_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrefixTerm_reducedPrefixEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_cons
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_nil
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordConsEquiv_symm_tail
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsScaleQuaternion_div_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_norm_lpsQuaternionWordProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_sideInverseEquiv_symm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_trace_cayleyConstantProjection
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
attribute [local simp] QEC.Coding.SmallSetExpansion.meanZeroAdjacency_apply_coe
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jtpPositiveTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.FormalPowerSeries.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_succ_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_right
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_succ
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qBinom_zero_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.qPochhammer_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.card_lpsReducedWords_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyHeckeElement_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyRightRegularRepresentation_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyVectorWordProduct_lpsReducedWordPrefixEquiv
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyVectorWordProduct_lps_backtrack
attribute [local simp] QEC.Coding.TannerLiftedProduct.coe_lpsQuaternionAwayWordProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiGeometricSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertTerm
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiSignedCubeSeriesRaw
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
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
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsAlternatingReducedWordElement_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsBacktrackingPrefixEquiv_symm_product
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsFiniteHeckeElement_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsPGLHeckeLabel_eq_toPGL
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsPrefixTerm_backtrackingPrefixEquiv_symm
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsPrefixTerm_reducedPrefixEquiv
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_conj
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_cons
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_nil
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsReducedWordConsEquiv_symm_tail
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsReducedWordElement_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.norm_lpsQuaternionWordProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.rightDoubleCoverNeighbor_rightDoubleCoverNeighbor
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.sideInverseEquiv_symm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.trace_cayleyConstantProjection
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
namespace QEC.Coding.TannerLiftedProduct
open Matrix
open scoped LinearAlgebra.Projectivization
variable {p : ℕ}
theorem lpsQuaternionMatrix_eq_zero_iff_coordinatesDvd
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1) (t : LPSQuaternion) :
    lpsQuaternionMatrix p t = 0 ↔ t.CoordinatesDvd (p : ℤ) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    change ((2 : ℕ) : ZMod p) = 0 at hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have hple : p ≤ 2 := Nat.le_of_dvd (by omega) hz
    have hpge : 2 ≤ p := hp.two_le
    interval_cases p <;> norm_num at hp4
  constructor
  · intro hM
    have h00 := congrFun (congrFun hM (0 : Fin 2)) (0 : Fin 2)
    have h01 := congrFun (congrFun hM (0 : Fin 2)) (1 : Fin 2)
    have h10 := congrFun (congrFun hM (1 : Fin 2)) (0 : Fin 2)
    have h11 := congrFun (congrFun hM (1 : Fin 2)) (1 : Fin 2)
    simp [lpsQuaternionMatrix] at h00 h01 h10 h11
    have ha : (t.a : ZMod p) = 0 := by
      have hz : (2 : ZMod p) * (t.a : ZMod p) = 0 := by
        linear_combination h00 + h11
      exact (mul_eq_zero.mp hz).resolve_left h2
    have hc : (t.c : ZMod p) = 0 := by
      have hz : (2 : ZMod p) * (t.c : ZMod p) = 0 := by
        linear_combination h01 - h10
      exact (mul_eq_zero.mp hz).resolve_left h2
    have hu : (t.b : ZMod p) * lpsResidueX p +
        (t.d : ZMod p) * lpsResidueY p = 0 := by
      linear_combination h00 - ha
    have hv : -(t.b : ZMod p) * lpsResidueY p +
        (t.d : ZMod p) * lpsResidueX p = 0 := by
      linear_combination h01 - hc
    have hroot := lpsResidueX_sq_add_lpsResidueY_sq_add_one p
    have hxy : lpsResidueX p ^ 2 + lpsResidueY p ^ 2 =
        (-1 : ZMod p) := by
      linear_combination hroot
    have hb : (t.b : ZMod p) = 0 := by
      have hs : (t.b : ZMod p) *
          (lpsResidueX p ^ 2 + lpsResidueY p ^ 2) = 0 := by
        linear_combination lpsResidueX p * hu - lpsResidueY p * hv
      rw [hxy] at hs
      simpa using hs
    have hd : (t.d : ZMod p) = 0 := by
      have hs : (t.d : ZMod p) *
          (lpsResidueX p ^ 2 + lpsResidueY p ^ 2) = 0 := by
        linear_combination lpsResidueY p * hu + lpsResidueX p * hv
      rw [hxy] at hs
      simpa using hs
    simpa [LPSQuaternion.CoordinatesDvd,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd] using ⟨ha, hb, hc, hd⟩
  · intro hdiv
    rcases hdiv with ⟨ha, hb, hc, hd⟩
    have ha0 : (t.a : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ha
    have hb0 : (t.b : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hb
    have hc0 : (t.c : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hc
    have hd0 : (t.d : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lpsQuaternionMatrix, ha0, hb0, hc0, hd0]
theorem finrank_ker_lpsQuaternionMatrix_eq_one
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSQuaternion) (hnorm : (p : ℤ) ∣ t.norm)
    (hprimitive : ¬t.CoordinatesDvd (p : ℤ)) :
    Module.finrank (ZMod p)
      (LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p t))) = 1 := by
  let f := Matrix.toLin' (lpsQuaternionMatrix p t)
  have hM : lpsQuaternionMatrix p t ≠ 0 := by
    simpa [lpsQuaternionMatrix_eq_zero_iff_coordinatesDvd hp hp4 t]
  have hf : f ≠ 0 := by
    intro hf0
    apply hM
    exact Matrix.toLin'.injective (by simpa [f] using hf0)
  have hdetM : (lpsQuaternionMatrix p t).det = 0 := by
    rw [det_lpsQuaternionMatrix]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hnorm
  have hkerBot : LinearMap.ker f ≠ ⊥ := by
    rw [← LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.det_toLin']
    exact hdetM
  have hkerTop : LinearMap.ker f ≠ ⊤ := by
    intro htop
    apply hf
    apply LinearMap.ext
    intro v
    have hv : v ∈ LinearMap.ker f := by rw [htop]; trivial
    simpa using hv
  have hlo : 1 ≤ Module.finrank (ZMod p) (LinearMap.ker f) :=
    Submodule.one_le_finrank_iff.mpr hkerBot
  have hhi : Module.finrank (ZMod p) (LinearMap.ker f) < 2 := by
    simpa [f] using Submodule.finrank_lt hkerTop
  change Module.finrank (ZMod p) (LinearMap.ker f) = 1
  exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo
noncomputable def lpsQuaternionKernelPoint
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSQuaternion) (hnorm : (p : ℤ) ∣ t.norm)
    (hprimitive : ¬t.CoordinatesDvd (p : ℤ)) :
    ℙ (ZMod p) (Fin 2 → ZMod p) :=
  Projectivization.mk''
    (LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p t)))
    (finrank_ker_lpsQuaternionMatrix_eq_one hp hp4 t hnorm hprimitive)
@[simp] theorem lpsQuaternionKernelPoint_submodule
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1)
    (t : LPSQuaternion) (hnorm : (p : ℤ) ∣ t.norm)
    (hprimitive : ¬t.CoordinatesDvd (p : ℤ)) :
    (lpsQuaternionKernelPoint hp hp4 t hnorm hprimitive).submodule =
      LinearMap.ker (Matrix.toLin' (lpsQuaternionMatrix p t)) := by
  apply Projectivization.submodule_mk''
theorem not_coordinatesDvd_of_norm_eq_prime
    (hp : p.Prime) (t : LPSQuaternion) (hnorm : t.norm = p) :
    ¬t.CoordinatesDvd (p : ℤ) := by
  intro hdiv
  let u := lpsQuaternionDiv (p : ℤ) t
  have hscale : lpsScaleQuaternion (p : ℤ) u = t :=
    lpsScaleQuaternion_div_eq hdiv
  have hnormScale := congrArg LPSQuaternion.norm hscale
  rw [norm_lpsScaleQuaternion, hnorm] at hnormScale
  have huNonneg : 0 ≤ u.norm := by
    simp only [LPSQuaternion.norm]
    positivity
  have hpz : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hpNe : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hcancel : (p : ℤ) * ((p : ℤ) * u.norm) = (p : ℤ) * 1 := by
    simpa [pow_two, mul_assoc] using hnormScale
  have hunit : (p : ℤ) * u.norm = 1 := mul_left_cancel₀ hpNe hcancel
  have hdvdInt : (p : ℤ) ∣ (1 : ℤ) := ⟨u.norm, hunit.symm⟩
  have hdvdNat : p ∣ 1 := by exact_mod_cast hdvdInt
  exact hp.ne_one (Nat.dvd_one.mp hdvdNat)
theorem LPSQuaternion.HasLPSParity.conj
    {t : LPSQuaternion} (ht : t.HasLPSParity) : t.conj.HasLPSParity := by
  rcases ht with ⟨ha, hb, hc, hd⟩
  change Odd t.a ∧ Even (-t.b) ∧ Even (-t.c) ∧ Even (-t.d)
  exact ⟨ha, hb.neg, hc.neg, hd.neg⟩
@[simp] theorem LPSQuaternion.neg_a (t : LPSQuaternion) :
    (-t).a = -t.a := by
  change (LPSQuaternion.ringEquivQuaternion (-t)).re = _
  rw [map_neg]
  rfl
@[simp] theorem LPSQuaternion.neg_b (t : LPSQuaternion) :
    (-t).b = -t.b := by
  change (LPSQuaternion.ringEquivQuaternion (-t)).imI = _
  rw [map_neg]
  rfl
@[simp] theorem LPSQuaternion.neg_c (t : LPSQuaternion) :
    (-t).c = -t.c := by
  change (LPSQuaternion.ringEquivQuaternion (-t)).imJ = _
  rw [map_neg]
  rfl
@[simp] theorem LPSQuaternion.neg_d (t : LPSQuaternion) :
    (-t).d = -t.d := by
  change (LPSQuaternion.ringEquivQuaternion (-t)).imK = _
  rw [map_neg]
  rfl
noncomputable def lpsPrimeQuaternionKernelPoint
    [Fact p.Prime] (hp : p.Prime) (hp4 : p % 4 = 1) :
    LPSGeneratorIndex p → ℙ (ZMod p) (Fin 2 → ZMod p) := fun beta =>
  lpsQuaternionKernelPoint hp hp4 beta.1
    (by
      have hnorm := norm_eq_of_mem_lpsQuaternionShell hp.pos beta.2
      exact ⟨1, by simpa [hnorm]⟩)
    (not_coordinatesDvd_of_norm_eq_prime hp beta.1
      (norm_eq_of_mem_lpsQuaternionShell hp.pos beta.2))
end QEC.Coding.TannerLiftedProduct


