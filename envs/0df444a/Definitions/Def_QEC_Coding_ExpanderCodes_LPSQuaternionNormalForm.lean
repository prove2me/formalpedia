-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternionNormalForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:02:59.817074+00:00
-- url     : https://prove2.me/theorems/4c61862e-1d79-4dfa-9ce8-ffdc5c9e3f54
-- title:
--   LPSQuaternion Normal Form
-- statement:
--   Definitions and structural lemmas for LPSQuaternion Normal Form, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionNormalForm.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionPrimePowerCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionWord
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSQuaternion_HasLPSParity_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_lpsReducedWords_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyConstantProjection_apply
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasLPSParity_lpsQuaternionWordProduct
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
variable {p : ℕ}
def LPSAlternatingReducedWord (hp : 0 < p) : ℕ → Type
  | 0 => LPSReducedWord hp 0
  | 1 => LPSReducedWord hp 1
  | n + 2 => LPSReducedWord hp (n + 2) ⊕
      LPSAlternatingReducedWord hp n
noncomputable instance lpsAlternatingReducedWordFintype
    (hp : 0 < p) (n : ℕ) : Fintype (LPSAlternatingReducedWord hp n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      change Fintype (LPSReducedWord hp 0)
      infer_instance
  | one =>
      change Fintype (LPSReducedWord hp 1)
      infer_instance
  | more n hn _hnOne =>
      change Fintype
        (LPSReducedWord hp (n + 2) ⊕ LPSAlternatingReducedWord hp n)
      exact @instFintypeSum _ _ inferInstance hn
def lpsScaleQuaternion (s : ℤ) (t : LPSQuaternion) : LPSQuaternion where
  a := s * t.a
  b := s * t.b
  c := s * t.c
  d := s * t.d
@[simp] theorem norm_lpsScaleQuaternion (s : ℤ) (t : LPSQuaternion) :
    (lpsScaleQuaternion s t).norm = s ^ 2 * t.norm := by
  simp [lpsScaleQuaternion, LPSQuaternion.norm]
  ring
theorem hasLPSParity_lpsScaleQuaternion_of_odd
    {s : ℤ} {t : LPSQuaternion} (hs : Odd s)
    (ht : t.HasLPSParity) :
    (lpsScaleQuaternion s t).HasLPSParity := by
  exact ⟨hs.mul ht.1, ht.2.1.mul_left s,
    ht.2.2.1.mul_left s, ht.2.2.2.mul_left s⟩
noncomputable def lpsAlternatingQuaternionProduct
    (a : LPSResiduePrime p) :
    (n : ℕ) → LPSAlternatingReducedWord a.degreePrime.pos n → LPSQuaternion
  | 0, word => lpsQuaternionWordProduct word.1.1
  | 1, word => lpsQuaternionWordProduct word.1.1
  | _n + 2, Sum.inl word => lpsQuaternionWordProduct word.1.1
  | n + 2, Sum.inr word =>
      lpsScaleQuaternion (p : ℤ) (lpsAlternatingQuaternionProduct a n word)
theorem norm_lpsAlternatingQuaternionProduct
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSAlternatingReducedWord a.degreePrime.pos n) :
    (lpsAlternatingQuaternionProduct a n word).norm = (p : ℤ) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa [LPSAlternatingReducedWord, lpsAlternatingQuaternionProduct]
        using norm_lpsQuaternionWordProduct a word.1.1
  | one =>
      simpa [LPSAlternatingReducedWord, lpsAlternatingQuaternionProduct]
        using norm_lpsQuaternionWordProduct a word.1.1
  | more n hn _hnOne =>
      change LPSReducedWord a.degreePrime.pos (n + 2) ⊕
        LPSAlternatingReducedWord a.degreePrime.pos n at word
      cases word with
      | inl word =>
          simpa [lpsAlternatingQuaternionProduct]
            using norm_lpsQuaternionWordProduct a word.1.1
      | inr word =>
          rw [lpsAlternatingQuaternionProduct,
            norm_lpsScaleQuaternion, hn word]
          ring
theorem hasLPSParity_lpsAlternatingQuaternionProduct
    (a : LPSResiduePrime p) (n : ℕ)
    (word : LPSAlternatingReducedWord a.degreePrime.pos n) :
    (lpsAlternatingQuaternionProduct a n word).HasLPSParity := by
  have hpNeTwo : p ≠ 2 := by
    have hp4 := a.degreeModFour
    omega
  have hpOddNat : Odd p := a.degreePrime.odd_of_ne_two hpNeTwo
  have hpOdd : Odd (p : ℤ) := by exact_mod_cast hpOddNat
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa [LPSAlternatingReducedWord, lpsAlternatingQuaternionProduct]
        using hasLPSParity_lpsQuaternionWordProduct a word.1.1
  | one =>
      simpa [LPSAlternatingReducedWord, lpsAlternatingQuaternionProduct]
        using hasLPSParity_lpsQuaternionWordProduct a word.1.1
  | more n hn _hnOne =>
      change LPSReducedWord a.degreePrime.pos (n + 2) ⊕
        LPSAlternatingReducedWord a.degreePrime.pos n at word
      cases word with
      | inl word =>
          simpa [lpsAlternatingQuaternionProduct]
            using hasLPSParity_lpsQuaternionWordProduct a word.1.1
      | inr word =>
          exact hasLPSParity_lpsScaleQuaternion_of_odd hpOdd (hn word)
def lpsNormalizeFirstSign (t : LPSQuaternion) : LPSQuaternion :=
  if 0 < t.a then t else ⟨-t.a, -t.b, -t.c, -t.d⟩
@[simp] theorem norm_lpsNormalizeFirstSign (t : LPSQuaternion) :
    (lpsNormalizeFirstSign t).norm = t.norm := by
  by_cases h : 0 < t.a <;>
    simp [lpsNormalizeFirstSign, h, LPSQuaternion.norm]
theorem hasLPSParity_lpsNormalizeFirstSign
    {t : LPSQuaternion} (ht : t.HasLPSParity) :
    (lpsNormalizeFirstSign t).HasLPSParity := by
  by_cases h : 0 < t.a
  · simpa [lpsNormalizeFirstSign, h] using ht
  · simp only [lpsNormalizeFirstSign, if_neg h,
      LPSQuaternion.HasLPSParity]
    exact ⟨ht.1.neg, ht.2.1.neg, ht.2.2.1.neg, ht.2.2.2.neg⟩
theorem lpsNormalizeFirstSign_a_pos_of_odd
    {t : LPSQuaternion} (ht : Odd t.a) :
    0 < (lpsNormalizeFirstSign t).a := by
  have hne : t.a ≠ 0 := by
    intro hzero
    have hoddZero : Odd (0 : ℤ) := hzero ▸ ht
    simp at hoddZero
  by_cases h : 0 < t.a
  · simp [lpsNormalizeFirstSign, h]
  · simp [lpsNormalizeFirstSign, h]
    omega
noncomputable def lpsAlternatingReducedWordToQuaternionShell
    (a : LPSResiduePrime p) (n : ℕ) :
    LPSAlternatingReducedWord a.degreePrime.pos n →
      {t // t ∈ lpsQuaternionShell (p ^ n)} := fun word =>
  ⟨lpsNormalizeFirstSign (lpsAlternatingQuaternionProduct a n word),
    (mem_lpsQuaternionShell_iff (pow_pos a.degreePrime.pos n) _).mpr <| by
      have hparity := hasLPSParity_lpsAlternatingQuaternionProduct a n word
      exact ⟨by
        rw [norm_lpsNormalizeFirstSign,
          norm_lpsAlternatingQuaternionProduct]
        norm_cast,
      lpsNormalizeFirstSign_a_pos_of_odd hparity.1,
      (hasLPSParity_lpsNormalizeFirstSign hparity).1⟩⟩
end QEC.Coding.TannerLiftedProduct


