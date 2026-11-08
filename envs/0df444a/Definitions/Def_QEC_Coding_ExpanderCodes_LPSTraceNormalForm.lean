-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
-- name    : QEC_Coding_ExpanderCodes_LPSTraceNormalForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:32:54.034246+00:00
-- url     : https://prove2.me/theorems/2683b162-ff81-45e0-872c-52cad4f28d95
-- title:
--   LPSTrace Normal Form
-- statement:
--   Definitions and structural lemmas for LPSTrace Normal Form, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceNormalForm.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeReducedWords
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPSLWordProduct_eq_one_iff_mem_traceCongruenceShell
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrefixTerm_backtrackingPrefixEquiv_symm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrefixTerm_reducedPrefixEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_cons
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_nil
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordConsEquiv_symm_tail
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsReducedWordElement_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lps_prime_pow_mod_four
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_lpsClosedReducedWords_iff
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
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
theorem lps_degree_coprime_two_mul_residue
    (a : LPSResiduePrime p) : Nat.Coprime p (2 * a.q) := by
  have hpNeTwo : p ≠ 2 := by
    have hp4 := a.degreeModFour
    omega
  have hpTwo : Nat.Coprime p 2 :=
    Nat.coprime_two_right.mpr (a.degreePrime.odd_of_ne_two hpNeTwo)
  have hpq : Nat.Coprime p a.q := by
    have hp := a.degreePrime.pos
    have hlarge := a.large
    exact ((a.prime.coprime_iff_not_dvd).mpr
      (Nat.not_dvd_of_pos_of_lt hp (by omega))).symm
  exact hpTwo.mul_right hpq
theorem two_mul_residue_dvd_degree_mul_iff
    (a : LPSResiduePrime p) (x : ℤ) :
    ((2 * a.q : ℕ) : ℤ) ∣ (p : ℤ) * x ↔
      ((2 * a.q : ℕ) : ℤ) ∣ x := by
  have hcoprimeNat := (lps_degree_coprime_two_mul_residue a).symm
  have hcoprime : IsCoprime (((2 * a.q : ℕ) : ℤ)) (p : ℤ) :=
    hcoprimeNat.isCoprime
  constructor
  · intro h
    exact hcoprime.dvd_of_dvd_mul_right (by simpa [mul_comm] using h)
  · rintro ⟨y, rfl⟩
    refine ⟨(p : ℤ) * y, ?_⟩
    ring
theorem two_mul_residue_dvd_scale_iff
    (a : LPSResiduePrime p) (t : LPSQuaternion) :
    (((2 * a.q : ℕ) : ℤ) ∣ (lpsScaleQuaternion (p : ℤ) t).b ↔
        ((2 * a.q : ℕ) : ℤ) ∣ t.b) ∧
      (((2 * a.q : ℕ) : ℤ) ∣ (lpsScaleQuaternion (p : ℤ) t).c ↔
        ((2 * a.q : ℕ) : ℤ) ∣ t.c) ∧
      (((2 * a.q : ℕ) : ℤ) ∣ (lpsScaleQuaternion (p : ℤ) t).d ↔
        ((2 * a.q : ℕ) : ℤ) ∣ t.d) := by
  exact ⟨two_mul_residue_dvd_degree_mul_iff a t.b,
    two_mul_residue_dvd_degree_mul_iff a t.c,
    two_mul_residue_dvd_degree_mul_iff a t.d⟩
theorem dvd_normalizeFirstSign_iff
    (m : ℤ) (t : LPSQuaternion) :
    (m ∣ (lpsNormalizeFirstSign t).b ↔ m ∣ t.b) ∧
      (m ∣ (lpsNormalizeFirstSign t).c ↔ m ∣ t.c) ∧
      (m ∣ (lpsNormalizeFirstSign t).d ↔ m ∣ t.d) := by
  by_cases h : 0 < t.a
  · simp [lpsNormalizeFirstSign, h]
  · simp [lpsNormalizeFirstSign, h]
noncomputable def lpsAlternatingPSLWordProduct
    (a : LPSResiduePrime p) :
    (n : ℕ) → LPSAlternatingReducedWord a.degreePrime.pos n →
      PSL(2, ZMod a.q)
  | 0, word => lpsPSLWordProduct a word.1.1
  | 1, word => lpsPSLWordProduct a word.1.1
  | _n + 2, Sum.inl word => lpsPSLWordProduct a word.1.1
  | n + 2, Sum.inr word => lpsAlternatingPSLWordProduct a n word
theorem lpsPSLWordProduct_eq_one_iff_imaginary_dvd
    (a : LPSResiduePrime p) {n : ℕ}
    (word : LPSReducedWord a.degreePrime.pos n) :
    lpsPSLWordProduct a word.1.1 = 1 ↔
      ((2 * a.q : ℕ) : ℤ) ∣ (lpsQuaternionWordProduct word.1.1).b ∧
        ((2 * a.q : ℕ) : ℤ) ∣ (lpsQuaternionWordProduct word.1.1).c ∧
          ((2 * a.q : ℕ) : ℤ) ∣ (lpsQuaternionWordProduct word.1.1).d := by
  have h := lpsPSLWordProduct_eq_one_iff_mem_traceCongruenceShell
    a word.1.1
  rw [mem_lpsTraceCongruenceShell_iff
      (pow_pos a.degreePrime.pos word.1.1.length),
    norm_lpsQuaternionWordProduct a word.1.1] at h
  simpa only [Int.natCast_pow, true_and] using h
theorem lpsAlternatingPSLWordProduct_eq_one_iff_imaginary_dvd
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSAlternatingReducedWord a.degreePrime.pos n) :
    lpsAlternatingPSLWordProduct a n word = 1 ↔
      ((2 * a.q : ℕ) : ℤ) ∣
          (lpsAlternatingReducedWordToQuaternionShell a n word).1.b ∧
        ((2 * a.q : ℕ) : ℤ) ∣
          (lpsAlternatingReducedWordToQuaternionShell a n word).1.c ∧
        ((2 * a.q : ℕ) : ℤ) ∣
          (lpsAlternatingReducedWordToQuaternionShell a n word).1.d := by
  induction n using Nat.twoStepInduction with
  | zero =>
      change LPSReducedWord a.degreePrime.pos 0 at word
      change lpsPSLWordProduct a word.1.1 = 1 ↔
        ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).b ∧
          ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).c ∧
          ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).d
      rw [lpsPSLWordProduct_eq_one_iff_imaginary_dvd]
      have hnormalize := dvd_normalizeFirstSign_iff
        (((2 * a.q : ℕ) : ℤ))
        (lpsQuaternionWordProduct word.1.1)
      rw [hnormalize.1, hnormalize.2.1, hnormalize.2.2]
  | one =>
      change LPSReducedWord a.degreePrime.pos 1 at word
      change lpsPSLWordProduct a word.1.1 = 1 ↔
        ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).b ∧
          ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).c ∧
          ((2 * a.q : ℕ) : ℤ) ∣
            (lpsNormalizeFirstSign
              (lpsQuaternionWordProduct word.1.1)).d
      rw [lpsPSLWordProduct_eq_one_iff_imaginary_dvd]
      have hnormalize := dvd_normalizeFirstSign_iff
        (((2 * a.q : ℕ) : ℤ))
        (lpsQuaternionWordProduct word.1.1)
      rw [hnormalize.1, hnormalize.2.1, hnormalize.2.2]
  | more n hn _hnOne =>
      change LPSReducedWord a.degreePrime.pos (n + 2) ⊕
        LPSAlternatingReducedWord a.degreePrime.pos n at word
      cases word with
      | inl word =>
          change lpsPSLWordProduct a word.1.1 = 1 ↔
            ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsQuaternionWordProduct word.1.1)).b ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsQuaternionWordProduct word.1.1)).c ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsQuaternionWordProduct word.1.1)).d
          rw [lpsPSLWordProduct_eq_one_iff_imaginary_dvd]
          have hnormalize := dvd_normalizeFirstSign_iff
            (((2 * a.q : ℕ) : ℤ))
            (lpsQuaternionWordProduct word.1.1)
          rw [hnormalize.1, hnormalize.2.1, hnormalize.2.2]
      | inr word =>
          change lpsAlternatingPSLWordProduct a n word = 1 ↔
            ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsScaleQuaternion (p : ℤ)
                    (lpsAlternatingQuaternionProduct a n word))).b ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsScaleQuaternion (p : ℤ)
                    (lpsAlternatingQuaternionProduct a n word))).c ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsScaleQuaternion (p : ℤ)
                    (lpsAlternatingQuaternionProduct a n word))).d
          rw [hn word]
          have hnormalize := dvd_normalizeFirstSign_iff
            (((2 * a.q : ℕ) : ℤ))
            (lpsScaleQuaternion (p : ℤ)
              (lpsAlternatingQuaternionProduct a n word))
          rw [hnormalize.1, hnormalize.2.1, hnormalize.2.2]
          have hscale := two_mul_residue_dvd_scale_iff a
            (lpsAlternatingQuaternionProduct a n word)
          rw [hscale.1, hscale.2.1, hscale.2.2]
          change
            (((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsAlternatingQuaternionProduct a n word)).b ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsAlternatingQuaternionProduct a n word)).c ∧
              ((2 * a.q : ℕ) : ℤ) ∣
                (lpsNormalizeFirstSign
                  (lpsAlternatingQuaternionProduct a n word)).d) ↔ _
          have hbase := dvd_normalizeFirstSign_iff
            (((2 * a.q : ℕ) : ℤ))
            (lpsAlternatingQuaternionProduct a n word)
          rw [hbase.1, hbase.2.1, hbase.2.2]
abbrev LPSClosedAlternatingReducedWord
    (a : LPSResiduePrime p) (n : ℕ) :=
  {word : LPSAlternatingReducedWord a.degreePrime.pos n //
    lpsAlternatingPSLWordProduct a n word = 1}
abbrev LPSNormalizedTraceQuaternion
    (a : LPSResiduePrime p) (n : ℕ) :=
  {t : {t // t ∈ lpsQuaternionShell (p ^ n)} //
    ((2 * a.q : ℕ) : ℤ) ∣ t.1.b ∧
      ((2 * a.q : ℕ) : ℤ) ∣ t.1.c ∧
        ((2 * a.q : ℕ) : ℤ) ∣ t.1.d}
noncomputable def lpsClosedAlternatingReducedWordEquivNormalizedTrace
    (a : LPSResiduePrime p) (n : ℕ)
    (hsurj : Function.Surjective
      (lpsAlternatingReducedWordToQuaternionShell a n)) :
    LPSClosedAlternatingReducedWord a n ≃
      LPSNormalizedTraceQuaternion a n :=
  (Equiv.ofBijective (lpsAlternatingReducedWordToQuaternionShell a n)
    (lpsAlternatingReducedWordToQuaternionShell_bijective_of_surjective
      a n hsurj)).subtypeEquiv fun word =>
        lpsAlternatingPSLWordProduct_eq_one_iff_imaginary_dvd a n word
def lpsSignedQuaternion (negative : Bool)
    (t : LPSQuaternion) : LPSQuaternion :=
  if negative then ⟨-t.a, -t.b, -t.c, -t.d⟩ else t
@[simp] theorem norm_lpsSignedQuaternion
    (negative : Bool) (t : LPSQuaternion) :
    (lpsSignedQuaternion negative t).norm = t.norm := by
  cases negative <;> simp [lpsSignedQuaternion, LPSQuaternion.norm]
theorem dvd_lpsSignedQuaternion_iff
    (m : ℤ) (negative : Bool) (t : LPSQuaternion) :
    (m ∣ (lpsSignedQuaternion negative t).b ↔ m ∣ t.b) ∧
      (m ∣ (lpsSignedQuaternion negative t).c ↔ m ∣ t.c) ∧
      (m ∣ (lpsSignedQuaternion negative t).d ↔ m ∣ t.d) := by
  cases negative <;> simp [lpsSignedQuaternion]
theorem even_of_two_mul_dvd
    {q : ℕ} {x : ℤ} (h : (((2 * q : ℕ) : ℤ)) ∣ x) : Even x := by
  rcases h with ⟨y, rfl⟩
  refine ⟨(q : ℤ) * y, ?_⟩
  push_cast
  ring
noncomputable def lpsSignedNormalizedTraceQuaternion
    (a : LPSResiduePrime p) (n : ℕ) :
    Bool × LPSNormalizedTraceQuaternion a n →
      {t // t ∈ lpsTraceCongruenceShell a.q (p ^ n)} := fun x =>
  ⟨lpsSignedQuaternion x.1 x.2.1.1,
    (mem_lpsTraceCongruenceShell_iff (pow_pos a.degreePrime.pos n) _).mpr <| by
      have hnorm := (mem_lpsQuaternionShell_iff
        (pow_pos a.degreePrime.pos n) x.2.1.1).mp x.2.1.2
      have hdvd := dvd_lpsSignedQuaternion_iff
        (((2 * a.q : ℕ) : ℤ)) x.1 x.2.1.1
      exact ⟨by rw [norm_lpsSignedQuaternion, hnorm.1],
        hdvd.1.mpr x.2.2.1,
        hdvd.2.1.mpr x.2.2.2.1,
        hdvd.2.2.mpr x.2.2.2.2⟩⟩
theorem lpsSignedNormalizedTraceQuaternion_injective
    (a : LPSResiduePrime p) (n : ℕ) :
    Function.Injective (lpsSignedNormalizedTraceQuaternion a n) := by
  rintro ⟨negative, t⟩ ⟨negative', u⟩ h
  have hval := congrArg Subtype.val h
  have htPos := ((mem_lpsQuaternionShell_iff
    (pow_pos a.degreePrime.pos n) t.1.1).mp t.1.2).2.1
  have huPos := ((mem_lpsQuaternionShell_iff
    (pow_pos a.degreePrime.pos n) u.1.1).mp u.1.2).2.1
  cases negative <;> cases negative'
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      simpa [lpsSignedNormalizedTraceQuaternion,
        lpsSignedQuaternion] using hval
  · have ha := congrArg LPSQuaternion.a hval
    simp [lpsSignedNormalizedTraceQuaternion,
      lpsSignedQuaternion] at ha
    omega
  · have ha := congrArg LPSQuaternion.a hval
    simp [lpsSignedNormalizedTraceQuaternion,
      lpsSignedQuaternion] at ha
    omega
  · apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Subtype.ext
      have ha := congrArg LPSQuaternion.a hval
      have hb := congrArg LPSQuaternion.b hval
      have hc := congrArg LPSQuaternion.c hval
      have hd := congrArg LPSQuaternion.d hval
      apply LPSQuaternion.ext <;>
        simp [lpsSignedNormalizedTraceQuaternion,
          lpsSignedQuaternion] at ha hb hc hd ⊢ <;>
        omega
theorem lpsSignedNormalizedTraceQuaternion_surjective
    (a : LPSResiduePrime p) (n : ℕ) :
    Function.Surjective (lpsSignedNormalizedTraceQuaternion a n) := by
  intro u
  have hu := (mem_lpsTraceCongruenceShell_iff
    (pow_pos a.degreePrime.pos n) u.1).mp u.2
  have hbEven : Even u.1.b := even_of_two_mul_dvd hu.2.1
  have hcEven : Even u.1.c := even_of_two_mul_dvd hu.2.2.1
  have hdEven : Even u.1.d := even_of_two_mul_dvd hu.2.2.2
  have hpPow4 : p ^ n % 4 = 1 :=
    lps_prime_pow_mod_four a.degreeModFour n
  have haOdd : Odd u.1.a := by
    rcases exactly_one_odd_coordinate hpPow4 u.1 hu.1 with
      ha | hb | hc | hd
    · exact ha.1
    · exact ((Int.not_odd_iff_even.mpr hbEven) hb.2.1).elim
    · exact ((Int.not_odd_iff_even.mpr hcEven) hc.2.2.1).elim
    · exact ((Int.not_odd_iff_even.mpr hdEven) hd.2.2.2).elim
  have haNe : u.1.a ≠ 0 := by
    intro hzero
    have hoddZero : Odd (0 : ℤ) := hzero ▸ haOdd
    simp at hoddZero
  by_cases haPos : 0 < u.1.a
  · let t : LPSNormalizedTraceQuaternion a n :=
      ⟨⟨u.1, (mem_lpsQuaternionShell_iff
        (pow_pos a.degreePrime.pos n) u.1).mpr
          ⟨by exact_mod_cast hu.1, haPos, haOdd⟩⟩,
        hu.2⟩
    refine ⟨⟨false, t⟩, ?_⟩
    apply Subtype.ext
    rfl
  · have hnegPos : 0 < -u.1.a := by omega
    let negU : LPSQuaternion := ⟨-u.1.a, -u.1.b, -u.1.c, -u.1.d⟩
    have hnegNorm : negU.norm = (p ^ n : ℕ) := by
      change (-u.1.a) ^ 2 + (-u.1.b) ^ 2 +
        (-u.1.c) ^ 2 + (-u.1.d) ^ 2 = _
      simpa [LPSQuaternion.norm] using hu.1
    let t : LPSNormalizedTraceQuaternion a n :=
      ⟨⟨negU, (mem_lpsQuaternionShell_iff
        (pow_pos a.degreePrime.pos n) negU).mpr
          ⟨hnegNorm, hnegPos, haOdd.neg⟩⟩,
        by simpa [negU] using hu.2⟩
    refine ⟨⟨true, t⟩, ?_⟩
    apply Subtype.ext
    apply LPSQuaternion.ext <;>
      simp [lpsSignedNormalizedTraceQuaternion,
        lpsSignedQuaternion, t, negU]
noncomputable def lpsSignedNormalizedTraceQuaternionEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    Bool × LPSNormalizedTraceQuaternion a n ≃
      {t // t ∈ lpsTraceCongruenceShell a.q (p ^ n)} :=
  Equiv.ofBijective (lpsSignedNormalizedTraceQuaternion a n)
    ⟨lpsSignedNormalizedTraceQuaternion_injective a n,
      lpsSignedNormalizedTraceQuaternion_surjective a n⟩
@[simp] theorem lpsPSLWordProduct_eq_cayleyVectorWordProduct
    (a : LPSResiduePrime p) {n : ℕ}
    (word : List.Vector (LPSGeneratorIndex p) n) :
    lpsPSLWordProduct a word.1 =
      cayleyVectorWordProduct (lpsQuaternionLabel a) word := by
  rfl
noncomputable def lpsClosedReducedWordSubtypeEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    {word : LPSReducedWord a.degreePrime.pos n //
      lpsPSLWordProduct a word.1.1 = 1} ≃
      {word // word ∈ lpsClosedReducedWords a n} where
  toFun word := ⟨word.1.1,
    (mem_lpsClosedReducedWords_iff a word.1.1).mpr
      ⟨word.1.2, by simpa using word.2⟩⟩
  invFun word :=
    ⟨⟨word.1, (mem_lpsClosedReducedWords_iff a word.1).mp word.2 |>.1⟩,
      by
        have hclosed :=
          (mem_lpsClosedReducedWords_iff a word.1).mp word.2 |>.2
        simpa using hclosed⟩
  left_inv word := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv word := by
    apply Subtype.ext
    rfl
def lpsAlternatingReducedWordAddTwoEquiv
    (hp : 0 < p) (n : ℕ) :
    LPSAlternatingReducedWord hp (n + 2) ≃
      LPSReducedWord hp (n + 2) ⊕ LPSAlternatingReducedWord hp n :=
  Equiv.refl _
noncomputable def lpsClosedAlternatingReducedWordAddTwoEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    LPSClosedAlternatingReducedWord a (n + 2) ≃
      {word : LPSReducedWord a.degreePrime.pos (n + 2) //
        lpsPSLWordProduct a word.1.1 = 1} ⊕
        LPSClosedAlternatingReducedWord a n :=
  ((lpsAlternatingReducedWordAddTwoEquiv a.degreePrime.pos n).subtypeEquiv
    fun _word => Iff.rfl).trans Equiv.subtypeSum
end QEC.Coding.TannerLiftedProduct


