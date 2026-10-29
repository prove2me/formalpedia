-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_BoundednessGap
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_BoundednessGap
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:52:09.97697+00:00
-- url     : https://prove2.me/theorems/2c99ad2c-db81-4bda-b362-32a84e44cac4
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / BoundednessTransport / BoundednessGap
-- statement:
--   This bundle transports the helper boundedness gap through the self-improvement construction. It decomposes the gap, bounds its off-diagonal part, moves the estimate through data processing, and compares the final projective residual with both natural and literal threshold errors.
--
--   Principal definitions:
--   - `helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg`: Decomposes the helper gap into an upper gap and an averaged off-diagonal term.
--   - `helper_boundedness_gap_le_selfImprovementHelperError`: The basic helper-stage gap bound.
--   - `helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer`: The bound after using add-in-$u$ point-consistency transfer.
--   - `helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs`: Converts helper completeness to a right-placed total bound.
--   - `helper_boundedness_gap_transport_through_data_processing`: Transports the gap through outcome data processing.
--   - `projective_boundedness_gap_le_helper_boundedness_gap`: Bounds the projective residual by the helper gap.
--   - `final_fields_projective_residual_bound_natural` and `final_fields_projective_residual_bound`: The natural and literal-threshold final residual bounds.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/BoundednessGap.lean#L31-L578

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/BoundednessTransport/BoundednessGap.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistency
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistencyLiteral
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
# Boundedness transport boundedness-gap estimates

This file contains the helper boundedness-gap decomposition, its
data-processing transport, and the final projective-residual boundedness
constructors used in the self-improvement proof.

## References

- `references/ldt-paper/self_improvement.tex` lines 612--613 and 742--755
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

/-- Algebraic decomposition of the helper boundedness gap.

The scalar gap
`⟨Z ⊗ I - helperAgreementAverageOperator⟩` is the sum of
`⟨Z ⊗ I⟩ - ⟨I ⊗ H.total⟩` and the off-diagonal average produced by
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`.  This is the
formal algebraic bridge between the reindexing calculation and the final
boundedness estimate in the proof of self-improvement. -/
theorem helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    helperBoundednessGap params strategy H Z =
      (ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) H.total)) +
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
              ev strategy.state
                (opTensor ((strategy.pointMeasurement u).outcome a)
                  (H.outcome h))) := by
  have hslack :=
    helper_boundedness_slack_average_ev_eq_off_diagonal_avg params strategy H
  have hgap_decomp :
      helperBoundednessGap params strategy H Z =
        (ev strategy.state (helperUpperOperator params Z) -
            ev strategy.state (rightTensor (ι₁ := ι) H.total)) +
          (ev strategy.state (rightTensor (ι₁ := ι) H.total) -
            ev strategy.state (helperAgreementAverageOperator params strategy H)) := by
    unfold helperBoundednessGap helperBoundednessOperator
    rw [ev_sub]
    ring
  rw [hgap_decomp, hslack]

/-- Helper-stage boundedness from the scalar comparison and the off-diagonal
estimate.

The helper boundedness gap decomposes as
`⟨Z ⊗ I⟩ - ⟨I ⊗ Hhat.total⟩` plus the off-diagonal average from
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`.  Thus the comparison
`⟨Z ⊗ I⟩ - ⟨I ⊗ Hhat.total⟩ ≤ 3 √δ`, together with the off-diagonal estimate
`≤ 4 √ζ_variance`, gives the helper threshold after applying
`helper_boundedness_error_le_selfImprovementHelperError`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta)
    (hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤
        4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  calc
    helperBoundednessGap params strategy Hhat Z =
        (ev strategy.state (helperUpperOperator params Z) -
            ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)) +
          avgOver (uniformDistribution (Point params)) (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a)
                    (Hhat.outcome h))) :=
      helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg params strategy Hhat Z
    _ ≤ 3 * Real.sqrt delta +
        4 * Real.sqrt (selfImprovementVarianceError params eps delta) :=
      add_le_add hZ_vs_H hoffdiag
    _ ≤ selfImprovementHelperError params eps delta :=
      helper_boundedness_error_le_selfImprovementHelperError params eps delta heps hdelta

-- This bound combines the off-diagonal add-in-u transfer with the boundedness
-- gap decomposition.
/-- Helper-stage boundedness from the scalar comparison and the
point-consistency `add-in-u` transfer.

This theorem composes the off-diagonal estimate supplied by
`pointConsistencyAddInUSelection` with
`helper_boundedness_gap_le_selfImprovementHelperError`.  It is the formal
statement of the sentence "combined with the explicit `A`-consistency bound" in the
boundedness paragraph of the self-improvement proof. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  have hoffdiag_addInU :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤ addInUError params eps delta :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T Hhat htransfer
  have hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤
        4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
    simpa [addInUError, Real.sqrt_eq_rpow] using hoffdiag_addInU
  exact
    helper_boundedness_gap_le_selfImprovementHelperError
      params strategy eps delta heps hdelta hZ_vs_H hoffdiag

-- This comparison transports the helper-completeness scalar through the
-- left/right tensor swap on the permutation-invariant state.
/-- Convert the helper-completeness `Hhat`-versus-`Z` comparison to the
right-placed total comparison used in the boundedness gap.

The helper-completeness paragraph naturally proves
`⟨ψ, Z ⊗ I⟩ - 3√δ ≤ subMeasMass ψ Hhat.liftLeft`. The boundedness decomposition,
however, uses the right-placed total `⟨ψ, I ⊗ Hhat.total⟩`. On the
permutation-invariant strategy state these scalars agree, so the comparison
becomes `⟨ψ, Z ⊗ I⟩ - ⟨ψ, I ⊗ Hhat.total⟩ ≤ 3√δ`. -/
theorem helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (helperUpperOperator params Z) -
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
      3 * Real.sqrt delta := by
  have hleft :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft :=
    helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
      params strategy eps delta hhelper hssc hslack
  have hmass :
      subMeasMass strategy.state Hhat.liftLeft =
        ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) := rfl
  have hswap :
      ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) =
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) :=
    strategy.permInvState.swap_ev Hhat.total
  unfold helperUpperOperator
  rw [hmass, hswap] at hleft
  linarith

/-- Helper-stage boundedness from the actual helper comparison and the
point-consistency `add-in-u` transfer.

This theorem composes the helper-completeness comparison `Hhat`-versus-`Z`
with the boundedness off-diagonal estimate. Complementary slackness remains an
explicit hypothesis because the reduced `SelfImprovementHelperConclusion`
records only the presently formalized SDP facts. The off-diagonal transfer is
likewise explicit: it is the formal statement of the `add-in-u` application
with `S_u = {(a,h) : h(u) ≠ a}`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  have hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta :=
    helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
      params strategy eps delta hhelper hssc hslack
  exact
    helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
      params strategy eps delta heps hdelta hZ_vs_H htransfer

/-- Transport the helper boundedness gap through the data-processing
approximation between `Hhat` and `H`.

The input `hdata` is exactly the data-processing SDD bound already produced
inside `selfImprovement`. The conclusion says that replacing the helper
polynomial family in the point-agreement average by the projective family costs
at most `sqrt ε`, matching Proposition `easy-approx-from-approx-delta` in the
boundedness paragraph of the paper. -/
theorem helper_boundedness_gap_transport_through_data_processing
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (ε : Error)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        ε) :
    helperBoundednessGap params strategy H.toSubMeas Z ≤
      helperBoundednessGap params strategy Hhat Z + Real.sqrt ε := by
  have hdata_right :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftRight)
        ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
        ε := by
    simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight]
      using
        sddRel_liftRight_of_liftLeft_permInv
          strategy.permInvState (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Hhat)
          (polynomialEvaluationFamily params H.toSubMeas) ε hdata
  have happrox :=
    Preliminaries.easyApproxFromApproxDelta
      strategy.state strategy.isNormalized
      (uniformDistribution (Point params))
      (uniformDistribution_weight_sum_le_one (Point params))
      ((polynomialEvaluationFamily params Hhat).liftRight)
      ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      ε hdata_right
  have hscalar :
      |ev strategy.state (helperAgreementAverageOperator params strategy Hhat) -
        ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas)| ≤
        Real.sqrt ε := by
    rw [helper_agreement_average_ev_eq_avg params strategy Hhat,
      helper_agreement_average_ev_eq_avg params strategy H.toSubMeas]
    simpa [polynomialEvaluationFamily, evaluateAt, IdxSubMeas.liftRight,
      IdxSubMeas.liftLeft, IdxProjMeas.toIdxSubMeas,
      rightTensor_mul_leftTensor_eq_opTensor] using happrox
  unfold helperBoundednessGap helperBoundednessOperator
  rw [ev_sub, ev_sub]
  have hle := le_abs_self
    (ev strategy.state (helperAgreementAverageOperator params strategy Hhat) -
      ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas))
  linarith


/-- Compare the final projective residual with the helper boundedness gap for the
same projective family.

This is the SDP dual-slack step in the projective boundedness paragraph of
`thm:self-improvement` (`references/ldt-paper/self_improvement.tex`, lines
742--749): the term `Z ⊗ H_h` in the projective residual dominates
`(E_u A^u_{h(u)}) ⊗ H_h` for each polynomial `h`, and summing these inequalities
turns `Z ⊗ (I - H)` into the helper-stage defect
`Z ⊗ I - E_u Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
theorem projective_boundedness_gap_le_helper_boundedness_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ h : Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z h) :
    projectiveBoundednessGap params strategy H Z ≤
      helperBoundednessGap params strategy H.toSubMeas Z := by
  classical
  have hprojective_eq :
      projectiveBoundednessGap params strategy H Z =
        ev strategy.state (leftTensor (ι₂ := ι) Z) -
          ∑ h : Polynomial params,
            ev strategy.state (opTensor Z (H.toSubMeas.outcome h)) := by
    have hsub_tensor :
        opTensor Z (1 - H.toSubMeas.total) =
          opTensor Z (1 : MIPStarRE.Quantum.Op ι) -
            opTensor Z H.toSubMeas.total := by
      ext x y
      simp [opTensor, sub_eq_add_neg, mul_add]
    have htotal_tensor :
        opTensor Z H.toSubMeas.total =
          ∑ h : Polynomial params, opTensor Z (H.toSubMeas.outcome h) := by
      rw [← H.toSubMeas.sum_eq_total, opTensor_sum_right_univ]
    unfold projectiveBoundednessGap projectiveResidualOperator
    calc
      ev strategy.state (leftTensor (ι₂ := ι) Z *
          rightTensor (ι₁ := ι) (1 - H.toSubMeas.total))
          = ev strategy.state (opTensor Z (1 - H.toSubMeas.total)) := by
            rw [leftTensor_mul_rightTensor_eq_opTensor]
      _ = ev strategy.state
            (opTensor Z (1 : MIPStarRE.Quantum.Op ι) -
              opTensor Z H.toSubMeas.total) := by
            rw [hsub_tensor]
      _ = ev strategy.state (opTensor Z (1 : MIPStarRE.Quantum.Op ι)) -
            ev strategy.state (opTensor Z H.toSubMeas.total) := by
            rw [ev_sub]
      _ = ev strategy.state (leftTensor (ι₂ := ι) Z) -
            ev strategy.state (opTensor Z H.toSubMeas.total) := rfl
      _ = ev strategy.state (leftTensor (ι₂ := ι) Z) -
            ∑ h : Polynomial params,
              ev strategy.state (opTensor Z (H.toSubMeas.outcome h)) := by
            rw [htotal_tensor, ev_sum]
  have hhelper_agreement_eq :
      ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas) =
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor (averagedPointOperator params strategy h)
              (H.toSubMeas.outcome h)) := by
    rw [helper_agreement_average_ev_eq_polynomial_sum]
    rw [avgOver_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    exact (ev_opTensor_averageOperatorOverDistribution_left strategy.state
      (uniformDistribution (Point params))
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h)
      (H.toSubMeas.outcome h)).symm
  have hhelper_eq :
      helperBoundednessGap params strategy H.toSubMeas Z =
        ev strategy.state (leftTensor (ι₂ := ι) Z) -
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor (averagedPointOperator params strategy h)
                (H.toSubMeas.outcome h)) := by
    unfold helperBoundednessGap helperBoundednessOperator helperUpperOperator
    rw [ev_sub, hhelper_agreement_eq]
  have hsum_le :
      (∑ h : Polynomial params,
          ev strategy.state
            (opTensor (averagedPointOperator params strategy h) (H.toSubMeas.outcome h))) ≤
        ∑ h : Polynomial params,
          ev strategy.state (opTensor Z (H.toSubMeas.outcome h)) := by
    refine Finset.sum_le_sum ?_
    intro h _
    apply ev_mono
    exact opTensor_mono_left
      (sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hdual h))
      (H.toSubMeas.outcome_pos h)
  rw [hprojective_eq, hhelper_eq]
  linarith

/-- Natural-error projective-residual construction.

Given the helper-stage boundedness estimate for `Hhat`, the dual-slack
comparator above and the existing data-processing transport produce the final
projective residual at the paper's natural error
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError`. The
separate numerical absorption into the literal `selfImprovementError` threshold
is intentionally not hidden in this theorem.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755.
This is a source-faithful construction step for the final-fields boundedness
conclusion. -/
theorem final_fields_projective_residual_bound_natural
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) := by
  have hcompare :=
    projective_boundedness_gap_le_helper_boundedness_gap params strategy H Z
      hhelper.sdpWitness.dualFeasible
  have htransport :=
    helper_boundedness_gap_transport_through_data_processing params strategy Hhat H Z
      (selfImprovementDataProcessingError params eps delta) hdata
  linarith

/-- Literal-threshold projective-residual construction.

This theorem combines `final_fields_projective_residual_bound_natural` with a separately
named numerical absorption lemma. The analytic inputs are only the helper-stage
boundedness estimate, dual feasibility from `SelfImprovementHelperConclusion`,
and the data-processing SDD output already produced inside `selfImprovement`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755.
This is a source-faithful construction step for the final-fields boundedness
conclusion. -/
theorem final_fields_projective_residual_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        selfImprovementError params eps delta) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta :=
  le_trans
    (final_fields_projective_residual_bound_natural params strategy eps delta
      hhelper hhelperBounded hdata)
    habsorb

/-- Literal-threshold projective-residual construction under the standard
unit-interval smallness hypotheses.

This derived theorem follows from
`final_fields_projective_residual_bound`: the numerical absorption input is
provided by
`final_fields_projective_residual_error_le_selfImprovementError`, so callers
only need the helper-stage boundedness estimate, data-processing output, and
the usual smallness assumptions on `eps`, `delta`, and `d/q`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755.
This is a source-faithful construction step for the final-fields boundedness
conclusion. -/
theorem final_fields_projective_residual_bound_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta :=
  final_fields_projective_residual_bound params strategy eps delta hhelper hhelperBounded hdata
    (final_fields_projective_residual_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q)

/-- Final projective-residual construction from helper outputs and the
point-consistency `add-in-u` transfer.

The theorem proves the boundedness part of the final-fields construction once the
orthonormalization data-processing estimate is available. It supplies the
helper-stage boundedness estimate from the helper comparison, complementary
slackness, point self-consistency, and the off-diagonal `add-in-u` transfer,
then applies the standard data-processing transport and numerical absorption
into `selfImprovementError`.

**Paper source:** `references/ldt-paper/self_improvement.tex` lines 742--755.
This is a source-faithful construction step for the final-fields boundedness
conclusion. -/
theorem final_fields_projective_residual_bound_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta := by
  have hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta :=
    helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
      params strategy eps delta heps hdelta hhelper hssc hslack htransfer
  exact
    final_fields_projective_residual_bound_of_small_errors
      params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
      hhelper hhelperBounded hdata




end MIPStarRE.LDT.SelfImprovement

end

end LIDT


