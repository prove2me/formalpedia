-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSReducedWords
-- name    : QEC_Coding_ExpanderCodes_LPSReducedWords
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T10:20:53.664911+00:00
-- url     : https://prove2.me/theorems/18374d1b-cfb9-45d6-b70e-70e929c122ad
-- title:
--   LPSReduced Words
-- statement:
--   Definitions and structural lemmas for LPSReduced Words, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSReducedWords.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_CayleyWordTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareCount
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyConstantProjection_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_cayleyRightRegularRepresentation_apply
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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPGLHeckeLabel_eq_toPGL
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionLabel_conj
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_cons
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuaternionWordProduct_nil
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
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyConstantProjection_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.cayleyRightRegularRepresentation_apply
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
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsPGLHeckeLabel_eq_toPGL
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionLabel_conj
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_cons
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuaternionWordProduct_nil
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
@[simp] theorem lpsGeneratorConjEquiv_apply_apply
    (hp : 0 < p) (t : LPSGeneratorIndex p) :
    lpsGeneratorConjEquiv hp (lpsGeneratorConjEquiv hp t) = t := by
  apply Subtype.ext
  exact t.1.conj_conj
noncomputable def lpsReducedSuccessors
    (hp : 0 < p) (t : LPSGeneratorIndex p) :
    Finset (LPSGeneratorIndex p) :=
  Finset.univ.erase (lpsGeneratorConjEquiv hp t)
theorem mem_lpsReducedSuccessors_iff
    (hp : 0 < p) (t u : LPSGeneratorIndex p) :
    u ∈ lpsReducedSuccessors hp t ↔
      u ≠ lpsGeneratorConjEquiv hp t := by
  simp [lpsReducedSuccessors]
def LPSWordIsReduced
    (hp : 0 < p) (word : List (LPSGeneratorIndex p)) : Prop :=
  word.IsChain fun t u => u ≠ lpsGeneratorConjEquiv hp t
noncomputable instance (hp : 0 < p)
    (word : List (LPSGeneratorIndex p)) :
    Decidable (LPSWordIsReduced hp word) :=
  Classical.propDecidable _
@[simp] theorem lpsWordIsReduced_nil (hp : 0 < p) :
    LPSWordIsReduced hp [] := by
  exact List.isChain_nil
@[simp] theorem lpsWordIsReduced_singleton
    (hp : 0 < p) (t : LPSGeneratorIndex p) :
    LPSWordIsReduced hp [t] := by
  exact List.isChain_singleton t
theorem lpsWordIsReduced_cons_cons
    (hp : 0 < p) (t u : LPSGeneratorIndex p)
    (word : List (LPSGeneratorIndex p)) :
    LPSWordIsReduced hp (t :: u :: word) ↔
      u ≠ lpsGeneratorConjEquiv hp t ∧
        LPSWordIsReduced hp (u :: word) :=
  List.isChain_cons_cons
theorem ne_lpsGeneratorConjEquiv_comm
    (hp : 0 < p) (t u : LPSGeneratorIndex p) :
    u ≠ lpsGeneratorConjEquiv hp t ↔
      t ≠ lpsGeneratorConjEquiv hp u := by
  constructor
  · intro h htu
    apply h
    have hconj := congrArg (lpsGeneratorConjEquiv hp) htu
    simpa using hconj.symm
  · intro h hut
    apply h
    have hconj := congrArg (lpsGeneratorConjEquiv hp) hut
    simpa using hconj.symm
noncomputable def lpsReducedWords
    (hp : 0 < p) (n : ℕ) :
    Finset (List.Vector (LPSGeneratorIndex p) n) :=
  Finset.univ.filter fun word => LPSWordIsReduced hp word.1
abbrev LPSReducedWord (hp : 0 < p) (n : ℕ) :=
  {word : List.Vector (LPSGeneratorIndex p) n //
    LPSWordIsReduced hp word.1}
noncomputable def lpsReducedWordConsEquiv
    (hp : p.Prime) (n : ℕ) :
    LPSReducedWord hp.pos (n + 2) ≃
      {pair : LPSReducedWord hp.pos (n + 1) × LPSGeneratorIndex p //
        pair.2 ∈ lpsReducedSuccessors hp.pos pair.1.1.head} where
  toFun word := by
    let tail : List.Vector (LPSGeneratorIndex p) (n + 1) := word.1.tail
    have htail : LPSWordIsReduced hp.pos tail.1 := by
      dsimp [tail]
      rw [List.Vector.tail_val]
      exact word.2.tail
    let reducedTail : LPSReducedWord hp.pos (n + 1) := ⟨tail, htail⟩
    refine ⟨⟨reducedTail, word.1.head⟩, ?_⟩
    rw [mem_lpsReducedSuccessors_iff,
      ← ne_lpsGeneratorConjEquiv_comm]
    have hchain : LPSWordIsReduced hp.pos
        (word.1.head :: word.1.tail.1) := by
      have hval := congrArg Subtype.val
        (List.Vector.cons_head_tail word.1)
      rw [List.Vector.cons_val] at hval
      rw [hval]
      exact word.2
    have htailVal := congrArg Subtype.val
      (List.Vector.cons_head_tail word.1.tail)
    rw [List.Vector.cons_val] at htailVal
    have htwo : LPSWordIsReduced hp.pos
        (word.1.head :: word.1.tail.head :: word.1.tail.tail.1) := by
      rw [htailVal]
      exact hchain
    exact (lpsWordIsReduced_cons_cons _ _ _ _).mp htwo |>.1
  invFun pair := by
    refine ⟨pair.1.2 ::ᵥ pair.1.1.1, ?_⟩
    rw [List.Vector.cons_val]
    apply List.IsChain.cons pair.1.1.2
    intro u hu
    have huHead : u = pair.1.1.1.head := by
      exact Option.some.inj
        (hu.symm.trans (List.Vector.head?_toList pair.1.1.1))
    subst u
    rw [ne_lpsGeneratorConjEquiv_comm,
      ← mem_lpsReducedSuccessors_iff]
    exact pair.2
  left_inv word := by
    apply Subtype.ext
    exact List.Vector.cons_head_tail word.1
  right_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      simp
    · simp
noncomputable def lpsReducedWordPrefixEquiv
    (hp : p.Prime) (n : ℕ) :
    {pair : LPSGeneratorIndex p × LPSReducedWord hp.pos (n + 1) //
      pair.1 ∈ lpsReducedSuccessors hp.pos pair.2.1.head} ≃
      LPSReducedWord hp.pos (n + 2) where
  toFun pair :=
    (lpsReducedWordConsEquiv hp n).symm
      ⟨⟨pair.1.2, pair.1.1⟩, pair.2⟩
  invFun word :=
    let pair := lpsReducedWordConsEquiv hp n word
    ⟨⟨pair.1.2, pair.1.1⟩, pair.2⟩
  left_inv pair := by
    apply Subtype.ext
    simp
  right_inv word := by
    simp
noncomputable def lpsBacktrackingPrefixEquiv
    (hp : p.Prime) (n : ℕ) :
    {pair : LPSGeneratorIndex p × LPSReducedWord hp.pos (n + 1) //
      pair.1 ∉ lpsReducedSuccessors hp.pos pair.2.1.head} ≃
      LPSReducedWord hp.pos (n + 1) where
  toFun pair := pair.1.2
  invFun word := by
    refine ⟨⟨lpsGeneratorConjEquiv hp.pos word.1.head, word⟩, ?_⟩
    simp [mem_lpsReducedSuccessors_iff]
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · have hbacktrack : pair.1.1 =
          lpsGeneratorConjEquiv hp.pos pair.1.2.1.head := by
        simpa [mem_lpsReducedSuccessors_iff] using pair.2
      exact hbacktrack.symm
    · rfl
  right_inv word := rfl
noncomputable def lpsReducedWordElement
    (a : LPSResiduePrime p) (n : ℕ) :
    MonoidAlgebra ℂ PSL(2, ZMod a.q) :=
  ∑ word ∈ lpsReducedWords a.degreePrime.pos n,
    MonoidAlgebra.single
      (cayleyVectorWordProduct (lpsQuaternionLabel a) word) 1
def LPSPrefixIsReduced (a : LPSResiduePrime p) (n : ℕ)
    (pair : LPSGeneratorIndex p ×
      LPSReducedWord a.degreePrime.pos (n + 1)) : Prop :=
  pair.1 ∈ lpsReducedSuccessors a.degreePrime.pos pair.2.1.head
noncomputable instance (a : LPSResiduePrime p) (n : ℕ)
    (pair : LPSGeneratorIndex p ×
      LPSReducedWord a.degreePrime.pos (n + 1)) :
    Decidable (LPSPrefixIsReduced a n pair) :=
  Classical.propDecidable _
noncomputable def lpsPrefixIsReducedEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    {pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 1) //
      LPSPrefixIsReduced a n pair} ≃
      LPSReducedWord a.degreePrime.pos (n + 2) :=
  lpsReducedWordPrefixEquiv a.degreePrime n
noncomputable def lpsPrefixIsBacktrackingEquiv
    (a : LPSResiduePrime p) (n : ℕ) :
    {pair : LPSGeneratorIndex p ×
        LPSReducedWord a.degreePrime.pos (n + 1) //
      ¬LPSPrefixIsReduced a n pair} ≃
      LPSReducedWord a.degreePrime.pos (n + 1) :=
  lpsBacktrackingPrefixEquiv a.degreePrime n
noncomputable def lpsPrefixTerm (a : LPSResiduePrime p) {n : ℕ}
    (pair : LPSGeneratorIndex p ×
      LPSReducedWord a.degreePrime.pos n) :
    MonoidAlgebra ℂ PSL(2, ZMod a.q) :=
  MonoidAlgebra.single
    (lpsQuaternionLabel a pair.1 *
      cayleyVectorWordProduct (lpsQuaternionLabel a) pair.2.1) 1
noncomputable def lpsClosedReducedWords
    (a : LPSResiduePrime p) (n : ℕ) :
    Finset (List.Vector (LPSGeneratorIndex p) n) :=
  (lpsReducedWords a.degreePrime.pos n).filter fun word =>
    cayleyVectorWordProduct (lpsQuaternionLabel a) word = 1
noncomputable def lpsAlternatingReducedWordElement
    (a : LPSResiduePrime p) : ℕ →
    MonoidAlgebra ℂ PSL(2, ZMod a.q)
  | 0 => lpsReducedWordElement a 0
  | 1 => lpsReducedWordElement a 1
  | n + 2 => lpsReducedWordElement a (n + 2) +
      lpsAlternatingReducedWordElement a n
noncomputable def lpsAlternatingClosedReducedWordCount
    (a : LPSResiduePrime p) : ℕ → ℕ
  | 0 => (lpsClosedReducedWords a 0).card
  | 1 => (lpsClosedReducedWords a 1).card
  | n + 2 => (lpsClosedReducedWords a (n + 2)).card +
      lpsAlternatingClosedReducedWordCount a n
end QEC.Coding.TannerLiftedProduct


