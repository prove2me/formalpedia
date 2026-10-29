-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistency
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistency
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:48:00.296249+00:00
-- url     : https://prove2.me/theorems/22a4f64f-f8ff-4cf0-b0d0-b4adaf752056
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / BoundednessTransport / PointConsistency
-- statement:
--   This bundle transports point-consistency estimates through the helper and final projective outputs. It identifies tensor placements and total expectations, rewrites helper consistency as off-diagonal mass, and gives natural-error bounds both with an explicit total gap and with a supplied total difference.
--
--   Principal definitions:
--   - `opTensor_one_left_eq_rightTensor`: identifies tensoring with the left identity and right placement.
--   - `pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor`: transports the complete point-measurement total expectation.
--   - `pointMeasurement_total_evalFamily_total_ev_eq_rightTensor`: compares left and right total placements.
--   - `helper_point_consistency_error_eq_off_diagonal_avg`: identifies helper consistency with averaged off-diagonal mass.
--   - `helper_point_consistency_of_pointConsistencyAddInU_transfer`: derives helper point consistency from add-in-u transfer.
--   - `final_fields_point_consistency_totalGap_natural`: transports consistency with the total-overlap gap displayed explicitly.
--   - `final_fields_point_consistency_totalGap_natural_of_total_difference`: uses a supplied right-register total difference instead.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistency.lean#L32-L370

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/PointConsistency.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_MainTheorems
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_SumForm
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUPointConsistency
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Factored
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Transfer
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_Decomposition
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Helper
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimp
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Attr.Register
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix

namespace LIDT

namespace MIPStarRE.LDT.MakingMeasurementsProjective
end MIPStarRE.LDT.MakingMeasurementsProjective
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Boundedness transport point-consistency estimates

This file contains the point-consistency consequences of the helper-agreement
off-diagonal decomposition and the natural-error transports through the final
projective fields.

## References

- `references/ldt-paper/self_improvement.tex` lines 435 and 747--755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.Quantum
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tensor product with the identity on the left register is the right tensor
placement. -/
lemma opTensor_one_left_eq_rightTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (ι₁ := ι₁) (1 : MIPStarRE.Quantum.Op ι₁) B =
      rightTensor (ι₁ := ι₁) B := by
  rfl

/-- The point measurement is complete and polynomial evaluation preserves the
right-register total, so the tensor total has the same expectation as the right
placement of the original total. -/
lemma pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (S : SubMeas (Polynomial params) ι)
    (u : Point params) :
    ev strategy.state
        (opTensor
          (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total)
          (((polynomialEvaluationFamily params S) u).total)) =
      ev strategy.state (rightTensor (ι₁ := ι) S.total) := by
  have hA_total :
      (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) =
        (1 : MIPStarRE.Quantum.Op ι) := by
    exact (strategy.pointMeasurement u).total_eq_one
  have hS_total : (((polynomialEvaluationFamily params S) u).total) = S.total := by
    simpa [polynomialEvaluationFamily, evaluateAt] using
      postprocess_total S (fun g : Polynomial params => g u)
  rw [hA_total, hS_total, opTensor_one_left_eq_rightTensor]

/-- Left and right tensor placements of the point-measurement and evaluation
totals reduce to the right-register total expectation. -/
lemma pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (S : SubMeas (Polynomial params) ι)
    (u : Point params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
          rightTensor (ι₁ := ι)
            (((polynomialEvaluationFamily params S) u).total)) =
      ev strategy.state (rightTensor (ι₁ := ι) S.total) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  exact pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
    params strategy S u

/-- The helper-stage consistency defect is exactly the averaged off-diagonal
mass appearing in the point-consistency `add-in-u` calculation.

This is the same algebraic identity as
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`, read as a
`ConsRel` defect for the point measurement against the polynomial-evaluation
family of `H`. -/
theorem helper_point_consistency_error_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  classical
  unfold bipartiteConsError
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  have hdiff_eq :
      ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h)) := by
    exact helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum params strategy H u
  have hdiff_nonneg :
      0 ≤ ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) := by
    rw [hdiff_eq]
    exact Finset.sum_nonneg fun h _ =>
      Finset.sum_nonneg fun a _ =>
        ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg ((strategy.pointMeasurement u).toMeasurement.outcome_pos a)
            (H.outcome_pos h))
  have htotal :
      ev strategy.state
          (opTensor
            (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total)
            (((polynomialEvaluationFamily params H) u).total)) =
        ev strategy.state (rightTensor (ι₁ := ι) H.total) := by
    exact pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
      params strategy H u
  have hmatch :
      qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params H) u) =
        ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) := by
    simp [qBipartiteMatchMass, helperAgreementOperatorAtPoint,
      polynomialEvaluationFamily, evaluateAt, ev_sum, IdxProjMeas.toIdxSubMeas]
  unfold qBipartiteConsDefect
  rw [htotal, hmatch]
  rw [max_eq_right hdiff_nonneg, hdiff_eq]

-- This point-consistency conversion expands the off-diagonal add-in-u transfer
-- and the helper error normalization.
/-- Helper-stage point consistency from the point-consistency `add-in-u`
transfer hypothesis.

The transfer bound controls the off-diagonal mass
`E_u ∑_h ∑_{a ≠ h(u)} ⟨ψ, A^u_a ⊗ Hhat_h ψ⟩`.  The preceding algebraic
identity identifies this mass with the `ConsRel` defect for the point
measurement and the polynomial-evaluation family of `Hhat`. -/
theorem helper_point_consistency_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (Polynomial params) ι}
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params Hhat)
      (selfImprovementHelperError params eps delta) := by
  refine ⟨?_⟩
  rw [helper_point_consistency_error_eq_off_diagonal_avg]
  exact
    pointConsistencyAddInU_off_diagonal_avg_le_helper_error_of_transfer
      params strategy eps delta heps hdelta T Hhat htransfer

-- This lemma composes the selected point-consistency add-in-u chain with the
-- point-consistency conversion above.


/-- Natural-error transport of point consistency from the helper output to the
projective output, with the submeasurement total-overlap displacement stated
explicitly.

The measurement-valued right-register triangle lemma has no total-overlap term:
both right-register totals are the identity.  In the present application
`polynomialEvaluationFamily params Hhat` and
`polynomialEvaluationFamily params H.toSubMeas` are only submeasurements, so
the total-overlap term
`⟨ψ, A^u_{\mathrm{tot}} ⊗ H^u_{\mathrm{tot}} ψ⟩` must also be transported.
This theorem separates that displacement as the parameter `η`; the remaining
contribution is exactly the square root of the data-processing SDD error.  The
note `docs/paper-gaps/issue-1093-submeasurement-triangle-total-overlap.tex`
records the corresponding discrepancy with the measurement-valued paper step. -/
theorem final_fields_point_consistency_totalGap_natural
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta η : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      avgOver (uniformDistribution (Point params)) (fun u =>
        |ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) + η) := by
  have hdata_right :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftRight)
        ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
        (selfImprovementDataProcessingError params eps delta) := by
    simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight]
      using
        sddRel_liftRight_of_liftLeft_permInv
          strategy.permInvState (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Hhat)
          (polynomialEvaluationFamily params H.toSubMeas)
          (selfImprovementDataProcessingError params eps delta) hdata
  exact
    Preliminaries.triangleSub_right_subMeas_totalGap
      strategy.state (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params Hhat)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta)
      (selfImprovementDataProcessingError params eps delta) η hhelperPoint
      hdata_right hTotal

/-- Natural-error point-consistency transport when the total-overlap
displacement is supplied as a single right-register total difference.

Since the point measurement is complete and
`polynomialEvaluationFamily params H` has the same total as `H`, the averaged
total-overlap term in `final_fields_point_consistency_totalGap_natural` is
independent of the point `u`.  This theorem records the corresponding reduction
of the issue #1226 obstruction to the scalar difference between the totals of
the two right-register submeasurements. -/
theorem final_fields_point_consistency_totalGap_natural_of_total_difference
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta η : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| ≤ η) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) + η) := by
  have hTotalAvg :
      avgOver (uniformDistribution (Point params)) (fun u =>
        |ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η := by
    have hpoint : ∀ u : Point params,
        |ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))| =
        |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| := by
      intro u
      rw [pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
          params strategy H.toSubMeas u,
        pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
          params strategy Hhat u]
    have hconst :
        avgOver (uniformDistribution (Point params)) (fun u =>
          |ev strategy.state
              (leftTensor (ι₂ := ι)
                (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
                rightTensor (ι₁ := ι)
                  (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
                rightTensor (ι₁ := ι)
                  (((polynomialEvaluationFamily params Hhat) u).total))|) =
          avgOver (uniformDistribution (Point params)) (fun _ =>
            |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
              ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)|) := by
      refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
      intro u
      exact hpoint u
    rw [hconst, avgOver_uniform_const]
    exact hTotal
  exact
    final_fields_point_consistency_totalGap_natural
      params strategy eps delta η hhelperPoint hdata hTotalAvg





end MIPStarRE.LDT.SelfImprovement

end

end LIDT


