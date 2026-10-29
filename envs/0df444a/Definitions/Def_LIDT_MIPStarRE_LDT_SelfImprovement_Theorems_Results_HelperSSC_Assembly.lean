-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Assembly
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Assembly
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:56:10.795545+00:00
-- url     : https://prove2.me/theorems/609ac126-6fe5-4142-8627-9321cd97f220
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / HelperSSC / Assembly
-- statement:
--   This bundle assembles the helper-stage strong self-consistency conclusion from the scalar residual estimates. It links lower bounds, the paper-shaped residual chain, point-consistency transfer, and the named variance transports.
--
--   Principal definitions:
--   - `helper_residualLowerBound_of_offDiagonal_bound`: the residual lower bound reduced to an off-diagonal residual estimate.
--   - `helper_residualLowerBound_of_paper_chain_bound`: the residual lower bound reduced to the paper-shaped scalar chain.
--   - `helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer`: the lower bound obtained after moving over the auxiliary point and adding the point-consistency defect.
--   - `helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports`: the final off-diagonal scalar bound assembled from the displayed transports.
--   - `helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_paperChain`: helper-stage bounds from the paper residual chain.
--   - `helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_scalarTransports`: helper-stage bounds from direct scalar transports.
--   - `helper_ssc_bounds_of_scalarTransports_pointTransfer`: helper strong-self-consistency bounds using point transfer and scalar transports.
--   - `helper_strong_self_consistency_of_helper_conclusion`: the strong self-consistency conclusion from the helper construction and named add-in-u and variance estimates.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/Assembly.lean#L30-L804

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperSSC/Assembly.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_BoundednessGap
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_Decomposition
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistency
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_BoundednessTransport_PointConsistencyLiteral
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_CommonHelpers
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_PostDeleteA
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
# Helper strong self-consistency bounds: residual assembly

Residual lower-bound reductions, scalar-chain bound constructors, and
the final helper-stage strong self-consistency assembly theorems.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reduce the residual lower bound to the off-diagonal residual scalar
bound.

For the actual helper output, the equality
`Hhat = E_u A^u_{h(u)} T_h A^u_{h(u)}` identifies the left-hand side of
`HelperStrongSelfConsistencyBounds.residualLowerBound` with the
off-diagonal quantity isolated by
`helper_mass_sub_release_eq_polynomial_off_diagonal`.  Thus the remaining
analytic work may be stated as a bound on that concrete polynomial-pair sum,
rather than as a direct bound on the record field itself. -/
theorem helper_residualLowerBound_of_offDiagonal_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
            Real.sqrt (2 * delta) +
            ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
          addInUError params eps delta) :
    subMeasMass strategy.state Hhat.liftLeft -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
        addInUError params eps delta := by
  rw [hhelper.averagedConstruction]
  rw [helper_mass_sub_release_eq_polynomial_off_diagonal]
  simpa [helperOffDiagonalBareQuantity] using hoffdiag

/-- Reduce the residual lower bound to the paper-shaped residual-chain bound.

After `eq:release-the-kraken`, `eq:threw-in-h-prime`, `eq:delete-an-A`, and
`eq:move-over-v`, the paper bounds the expanded residual by
`7√ζ_variance + √(2δ) + md/q`.  Since
`addInUError = 4√ζ_variance`, this is exactly the pre-absorption bound
`11√ζ_variance + √(2δ) + md/q - addInUError`. -/
theorem helper_residualLowerBound_of_paper_chain_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) :
    subMeasMass strategy.state Hhat.liftLeft -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
        addInUError params eps delta := by
  refine helper_residualLowerBound_of_offDiagonal_bound
    params strategy eps delta hhelper ?_
  have hrewrite :
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
        addInUError params eps delta =
      7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error)) := by
    rw [addInUError]
    have hsqrt :
        Real.rpow (selfImprovementVarianceError params eps delta) (1 / (2 : Error)) =
          Real.sqrt (selfImprovementVarianceError params eps delta) := by
      exact (Real.sqrt_eq_rpow (selfImprovementVarianceError params eps delta)).symm
    rw [hsqrt]
    ring
  rw [hrewrite]
  exact hoffdiag

-- This transport lower bound expands the post-delete and move-over-v scalar
-- quantities before applying the variance-transfer estimates.
/-- Paper line `eq:move-over-v` yields a lower bound on the moved quantity in
terms of the helper mass and the explicit `A`-consistency defect.

This is the algebraic/slackness part of `self_improvement.tex:579-589`: average
over `v`, replace `T_h · E_v A^v_{h(v)}` by `T_h · Z` using complementary
slackness, collapse the `T`-sum to `Z`, compare `Z` to the averaged point
operator by dual feasibility, and then subtract the off-diagonal helper
agreement defect controlled by the point-consistency `add-in-u` transfer. -/
theorem helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
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
    subMeasMass strategy.state Hhat.liftLeft ≤
      helperMoveOverVQuantity params strategy T.toSubMeas + addInUError params eps delta := by
  let 𝒟 := uniformDistribution (Point params)
  let Hu : Point params → Polynomial params → MIPStarRE.Quantum.Op ι :=
    fun u h => (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h
  have hmul_avg :
      ∀ h : Polynomial params,
        averageOperatorOverDistribution 𝒟
            (fun v => T.toSubMeas.outcome h *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h v) =
          T.toSubMeas.outcome h * averagedPointOperator params strategy h := by
    intro h
    calc
      averageOperatorOverDistribution 𝒟
          (fun v => T.toSubMeas.outcome h *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
        = ∑ v ∈ 𝒟.support,
            𝒟.weight v •
              (T.toSubMeas.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h v) := by
            rfl
      _ = ∑ v ∈ 𝒟.support,
            T.toSubMeas.outcome h *
              (𝒟.weight v • pointConditionedOutcomeOperatorAtPolynomial params strategy h v) := by
            refine Finset.sum_congr rfl ?_
            intro v _
            rw [mul_smul_comm]
      _ = T.toSubMeas.outcome h *
            (∑ v ∈ 𝒟.support,
              𝒟.weight v • pointConditionedOutcomeOperatorAtPolynomial params strategy h v) := by
            rw [Matrix.mul_sum]
      _ = T.toSubMeas.outcome h * averagedPointOperator params strategy h := by
            rfl
  have hmove_eq :
      helperMoveOverVQuantity params strategy T.toSubMeas =
        avgOver 𝒟 (fun u =>
          ∑ h' : Polynomial params,
            ev strategy.state (opTensor (Hu u h') Z)) := by
    have hprod :=
      (avgOver_uniform_prod (α := Point params) (β := Point params)
        (fun u v =>
          ∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h')
                  (T.toSubMeas.outcome h *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h v)))).symm
    rw [show helperMoveOverVQuantity params strategy T.toSubMeas =
          avgOver 𝒟 (fun u =>
            avgOver 𝒟 (fun v =>
              ∑ h : Polynomial params,
                ∑ h' : Polynomial params,
                  ev strategy.state
                    (opTensor (Hu u h')
                      (T.toSubMeas.outcome h *
                        pointConditionedOutcomeOperatorAtPolynomial params strategy h v)))) from by
          unfold helperMoveOverVQuantity
          exact hprod.symm]
    refine avgOver_congr 𝒟 _ _ ?_
    intro u
    calc
      avgOver 𝒟 (fun v =>
          ∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h')
                  (T.toSubMeas.outcome h *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h v)))
        = avgOver 𝒟 (fun v =>
            ∑ h' : Polynomial params,
              ∑ h : Polynomial params,
                ev strategy.state
                  (opTensor (Hu u h')
                    (T.toSubMeas.outcome h *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h v))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro v
            rw [Finset.sum_comm]
      _ = ∑ h' : Polynomial params,
            avgOver 𝒟 (fun v =>
              ∑ h : Polynomial params,
                ev strategy.state
                  (opTensor (Hu u h')
                    (T.toSubMeas.outcome h *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h v))) := by
            rw [avgOver_sum]
      _ = ∑ h' : Polynomial params,
            ∑ h : Polynomial params,
              avgOver 𝒟 (fun v =>
                ev strategy.state
                  (opTensor (Hu u h')
                    (T.toSubMeas.outcome h *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h v))) := by
            refine Finset.sum_congr rfl ?_
            intro h' _
            rw [avgOver_sum]
      _ = ∑ h' : Polynomial params,
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h')
                  (T.toSubMeas.outcome h * averagedPointOperator params strategy h)) := by
            refine Finset.sum_congr rfl ?_
            intro h' _
            refine Finset.sum_congr rfl ?_
            intro h _
            calc
              avgOver 𝒟 (fun v =>
                  ev strategy.state
                    (opTensor (Hu u h')
                      (T.toSubMeas.outcome h *
                        pointConditionedOutcomeOperatorAtPolynomial params strategy h v)))
                = ev strategy.state
                    (opTensor (Hu u h')
                      (averageOperatorOverDistribution 𝒟
                        (fun v => T.toSubMeas.outcome h *
                          pointConditionedOutcomeOperatorAtPolynomial params strategy h v))) := by
                    exact
                      (ev_opTensor_averageOperatorOverDistribution_right strategy.state 𝒟
                        (Hu u h')
                        (fun v => T.toSubMeas.outcome h *
                          pointConditionedOutcomeOperatorAtPolynomial params strategy h v)).symm
              _ = ev strategy.state
                    (opTensor (Hu u h')
                      (T.toSubMeas.outcome h * averagedPointOperator params strategy h)) := by
                    rw [hmul_avg h]
      _ = ∑ h' : Polynomial params,
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h') (T.toSubMeas.outcome h * Z)) := by
            refine Finset.sum_congr rfl ?_
            intro h' _
            refine Finset.sum_congr rfl ?_
            intro h _
            rw [hslack h]
      _ = ∑ h' : Polynomial params,
            ev strategy.state (opTensor (Hu u h') Z) := by
            refine Finset.sum_congr rfl ?_
            intro h' _
            rw [← ev_sum strategy.state]
            congr 1
            rw [← opTensor_sum_right_univ, ← Finset.sum_mul, T.toSubMeas.sum_eq_total,
              T.total_eq_one, Matrix.one_mul]
  have hagree_eq :
      ev strategy.state (helperAgreementAverageOperator params strategy Hhat) =
        avgOver 𝒟 (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor (Hu u h) (averagedPointOperator params strategy h))) := by
    rw [hhelper.averagedConstruction]
    calc
      ev strategy.state
          (helperAgreementAverageOperator params strategy
            (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas))
        = avgOver 𝒟 (fun v =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  ((averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).outcome h))) :=
            helper_agreement_average_ev_eq_polynomial_sum params strategy _
      _ = avgOver 𝒟 (fun v =>
            ∑ h : Polynomial params,
              avgOver 𝒟 (fun u =>
                ev strategy.state (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (Hu u h)))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro v
            refine Finset.sum_congr rfl ?_
            intro h _
            simpa [Hu, averagedSandwichedPolynomialSubMeas,
              sandwichedPolynomialSubMeasAt, sandwichedPolynomialOutcomeOperatorAt] using
              (ev_opTensor_averageOperatorOverDistribution_right strategy.state 𝒟
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T.toSubMeas u h))
      _ = avgOver 𝒟 (fun u =>
            avgOver 𝒟 (fun v =>
              ∑ h : Polynomial params,
                ev strategy.state (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (Hu u h)))) := by
            rw [show avgOver 𝒟 (fun v =>
                  ∑ h : Polynomial params,
                    avgOver 𝒟 (fun u =>
                      ev strategy.state (opTensor
                        (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                        (Hu u h)))) =
                avgOver 𝒟 (fun v =>
                  avgOver 𝒟 (fun u =>
                    ∑ h : Polynomial params,
                      ev strategy.state (opTensor
                        (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                        (Hu u h)))) by
                refine avgOver_congr 𝒟 _ _ ?_
                intro v
                rw [avgOver_sum]]
            exact avgOver_uniform_comm (fun v u =>
              ∑ h : Polynomial params,
                ev strategy.state (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (Hu u h)))
      _ = avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              avgOver 𝒟 (fun v =>
                ev strategy.state (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (Hu u h)))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro u
            rw [avgOver_sum]
      _ = avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor (averagedPointOperator params strategy h) (Hu u h))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro u
            refine Finset.sum_congr rfl ?_
            intro h _
            exact
              (ev_opTensor_averageOperatorOverDistribution_left strategy.state 𝒟
                (fun v => pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                (Hu u h)).symm
      _ = avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h) (averagedPointOperator params strategy h))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro u
            refine Finset.sum_congr rfl ?_
            intro h _
            exact ev_opTensor_swap_of_density_fixed strategy.state strategy.densityFixed _ _
  have hmove_ge :
      avgOver 𝒟 (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor (Hu u h) (averagedPointOperator params strategy h))) ≤
        helperMoveOverVQuantity params strategy T.toSubMeas := by
    rw [hmove_eq]
    refine avgOver_mono 𝒟 _ _ ?_
    intro u
    refine Finset.sum_le_sum ?_
    intro h _
    exact ev_mono strategy.state _ _ <|
      opTensor_mono_right
        ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome_pos h)
        (sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hhelper.sdpWitness.dualFeasible h))
  have hoffdiag :
      avgOver 𝒟 (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a) (Hhat.outcome h))) ≤
        addInUError params eps delta :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T.toSubMeas Hhat htransfer
  have hdecomp :=
    helper_boundedness_slack_average_ev_eq_off_diagonal_avg params strategy Hhat
  have hmass_eq :
      subMeasMass strategy.state Hhat.liftLeft =
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) := by
    change ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) = _
    rw [strategy.permInvState.swap_ev Hhat.total]
  have htotal_eq :
      ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) =
        ev strategy.state (helperAgreementAverageOperator params strategy Hhat) +
          avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a) (Hhat.outcome h))) := by
    linarith [hdecomp]
  calc
    subMeasMass strategy.state Hhat.liftLeft =
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) := hmass_eq
    _ = ev strategy.state (helperAgreementAverageOperator params strategy Hhat) +
          avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor
                    ((strategy.pointMeasurement u).outcome a)
                    (Hhat.outcome h))) := htotal_eq
    _ ≤ helperMoveOverVQuantity params strategy T.toSubMeas +
          avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a) (Hhat.outcome h))) := by
            linarith [hagree_eq, hmove_ge]
    _ ≤ helperMoveOverVQuantity params strategy T.toSubMeas + addInUError params eps delta := by
            linarith [hoffdiag]

/-- Assemble the paper's final residual-chain estimate from the displayed scalar
transport bounds.

The first two hypotheses are the two variance swaps used to pass from
`eq:added-indicator` to the Schwartz--Zippel endpoint.  The next two hypotheses
are the transports from `eq:delete-an-A` to `eq:move-over-v`.  The final
hypothesis is the lower bound on the `move-over-v` endpoint obtained after
substituting the averaged operator `Z` and using the explicit point-consistency
bound for the point measurement. -/
theorem helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hclone :
      |helperDeleteAQuantity params strategy T.toSubMeas -
        helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T.toSubMeas -
        helperMoveOverVQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (2 * delta))
    (hmoveLower :
      subMeasMass strategy.state Hhat.liftLeft ≤
        helperMoveOverVQuantity params strategy T.toSubMeas +
          4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
      7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) +
        ((params.m : Error) * (params.d : Error) / (params.q : Error)) := by
  let release :=
    addInURightQuantity params strategy
      (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
      T.toSubMeas
      (selfConsistencyAddInUSelection params)
  let ζsqrt := Real.sqrt (selfImprovementVarianceError params eps delta)
  let sqrtTwoDelta := Real.sqrt (2 * delta)
  let mdq := ((params.m : Error) * (params.d : Error) / (params.q : Error))
  have houter :
      helperOffDiagonalOuterSandwichQuantity params strategy T.toSubMeas ≤
        2 * ζsqrt + mdq := by
    simpa [ζsqrt, mdq] using
      helperOffDiagonalOuterSandwichQuantity_le_two_sqrt_variance_add_mdq_of_abs_transports
        params strategy eps delta T.toSubMeas hleft hright
  have hmove_to_delete :
      helperMoveOverVQuantity params strategy T.toSubMeas ≤
        helperDeleteAQuantity params strategy T.toSubMeas + ζsqrt + sqrtTwoDelta := by
    simpa [ζsqrt, sqrtTwoDelta] using
      helperMoveOverVQuantity_le_deleteA_of_abs_transports
        params strategy eps delta T.toSubMeas hclone hmove
  have hmove_to_full :
      helperMoveOverVQuantity params strategy T.toSubMeas ≤
        helperFullOuterSandwichQuantity params strategy T.toSubMeas + ζsqrt + sqrtTwoDelta := by
    simpa [helperFullOuterSandwichQuantity_eq_deleteAQuantity params strategy T.toSubMeas]
      using hmove_to_delete
  have hmove_to_release :
      helperMoveOverVQuantity params strategy T.toSubMeas ≤
        release + 3 * ζsqrt + sqrtTwoDelta + mdq := by
    have hfull_split :
        helperFullOuterSandwichQuantity params strategy T.toSubMeas =
          release + helperOffDiagonalOuterSandwichQuantity params strategy T.toSubMeas := by
      simpa [release] using
        helperFullOuterSandwichQuantity_eq_release_add_offDiagonalOuterSandwichQuantity
          params strategy T.toSubMeas
    linarith
  have hresidual :
      subMeasMass strategy.state Hhat.liftLeft - release ≤
        7 * ζsqrt + sqrtTwoDelta + mdq := by
    linarith
  rw [hhelper.averagedConstruction] at hresidual
  rw [helper_mass_sub_release_eq_polynomial_off_diagonal] at hresidual
  simpa [release, ζsqrt, sqrtTwoDelta, mdq, helperOffDiagonalBareQuantity] using hresidual



/-- Construct the helper-stage bounds from the paper's final residual
chain estimate.

This variant lets downstream work target the paper's natural bound
`7√ζ_variance + √(2δ) + md/q` on the expanded off-diagonal residual.  The
conversion to the record's `11√ζ_variance + √(2δ) + md/q - addInUError`
form is performed internally. -/
lemma helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_paperChain
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) :
    HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta := by
  exact helper_strong_self_consistency_bounds_of_selfConsistency_localVariance
    params strategy eps delta hssc hlocal
    (helper_residualLowerBound_of_paper_chain_bound
      params strategy eps delta hhelper hoffdiag)

/-- Construct the helper-stage bounds directly from the scalar
transport estimates appearing in the paper.

Compared with
`helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_paperChain`,
this version does not ask for the already assembled residual-chain estimate.
It consumes the two off-diagonal variance swaps, the two post-`delete-an-A`
transports, and the final lower bound on the `move-over-v` endpoint, then
assembles the residual estimate internally. -/
lemma helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_scalarTransports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hclone :
      |helperDeleteAQuantity params strategy T.toSubMeas -
        helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T.toSubMeas -
        helperMoveOverVQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (2 * delta))
    (hmoveLower :
      subMeasMass strategy.state Hhat.liftLeft ≤
        helperMoveOverVQuantity params strategy T.toSubMeas +
          4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta := by
  exact
    helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_paperChain
      params strategy eps delta hhelper hssc hlocal
      (helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports
        params strategy eps delta hhelper hleft hright hclone hmove hmoveLower)

/-- Construct the helper-stage bounds from the paper's scalar transports and
the point-consistency add-in-`u` transfer.

This is the same residual-chain constructor as
`helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_scalarTransports`,
but it discharges the two off-diagonal variance swaps from local variance and
the final `move-over-v` lower-bound input from complementary slackness, dual
feasibility, and the point-consistency transfer. It packages the paper lines
after `eq:move-over-v` together with the two post-`delete-an-A` scalar
transports. -/
lemma helper_ssc_bounds_of_scalarTransports_pointTransfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hclone :
      |helperDeleteAQuantity params strategy T.toSubMeas -
        helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T.toSubMeas -
        helperMoveOverVQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (2 * delta))
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hpointTransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta := by
  have hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta) :=
    helperOffDiagonalIndicatorQuantity_abs_sub_oneSidedSwappedIndicator_le_sqrt
      params strategy eps delta T.toSubMeas hlocal
  have hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta) :=
    helperOffDiagonalOneSidedSwappedIndicator_abs_sub_swappedIndicator_le_sqrt
      params strategy eps delta T.toSubMeas hlocal
  have hmoveLower :
      subMeasMass strategy.state Hhat.liftLeft ≤
        helperMoveOverVQuantity params strategy T.toSubMeas +
          4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
    have hlower :=
      helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer
        params strategy eps delta hhelper hslack hpointTransfer
    simpa [addInUError, Real.sqrt_eq_rpow] using hlower
  exact
    helper_strong_self_consistency_bounds_of_selfConsistency_localVariance_scalarTransports
      params strategy eps delta hhelper hssc hlocal hleft hright hclone hmove hmoveLower

/-- Produce the helper-stage strong self-consistency conclusion from the actual
helper construction together with the named add-in-`u`/variance transports.

The theorem consumes the reduced helper output
`SelfImprovementHelperConclusion params strategy T Hhat Z eps delta` and the
four named scalar chain bounds together with the final lower bound on the
released right-hand side. It then assembles the diagonal transfer
using `add_in_u_simplified_transfer_of_cs_chain_sqrt_form`, upgrades it to the
paper's released right-hand side via
`selfConsistencyDiagonalAddInU_of_simplifiedTransfer`, and applies the closing
arithmetic absorption
`helper_strong_self_consistency_error_le_selfImprovementHelperError`.

This is the complete route from the actual helper construction and the named
scalar bounds to helper-stage strong self-consistency. The analytic work is
therefore stated as named bounds, rather than left as an
unstructured `BipartiteSSCRel` assumption. -/
theorem helper_strong_self_consistency_of_helper_conclusion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hbounds : HelperStrongSelfConsistencyBounds
      params strategy T Hhat eps delta) :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) := by
  have htransfer_simplified :
      |qBipartiteMatchMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas)
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas) -
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h)
                (T.toSubMeas.outcome h)))| ≤
        addInUError params eps delta :=
    add_in_u_simplified_transfer_of_cs_chain_sqrt_form
      params strategy eps delta heps hdelta T.toSubMeas
      hbounds.step01Bound hbounds.step12Bound
      hbounds.step23Bound hbounds.step34Bound
  have htransfer_release :
      |qBipartiteMatchMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas)
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas) -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params)| ≤
        addInUError params eps delta := by
    simpa [addInURightQuantity_selfConsistencySelection_eq_release] using
      selfConsistencyDiagonalAddInU_of_simplifiedTransfer
        params strategy eps delta T.toSubMeas htransfer_simplified
  have htransfer_release_hhat :
      |qBipartiteMatchMass strategy.state Hhat Hhat -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params)| ≤
        addInUError params eps delta := by
    simpa [hhelper.averagedConstruction] using htransfer_release
  have hhelperGap :
      subMeasMass strategy.state Hhat.liftLeft -
          qBipartiteMatchMass strategy.state Hhat Hhat ≤
        11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error)) := by
    have hreleaseGap :
        addInURightQuantity params strategy
            (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
            T.toSubMeas
            (selfConsistencyAddInUSelection params) -
          qBipartiteMatchMass strategy.state Hhat Hhat ≤
        addInUError params eps delta := by
      linarith [(abs_le.mp htransfer_release_hhat).1]
    linarith [hbounds.residualLowerBound, hreleaseGap]
  have hhelperGap_absorbed :
      subMeasMass strategy.state Hhat.liftLeft -
          qBipartiteMatchMass strategy.state Hhat Hhat ≤
        selfImprovementHelperError params eps delta := by
    have habsorb :=
      helper_strong_self_consistency_error_le_selfImprovementHelperError
        params eps delta heps hdelta hd_le_q
    linarith
  have hhelperErr_nonneg :
      0 ≤ selfImprovementHelperError params eps delta := by
    exact selfImprovementHelperError_nonneg params eps delta
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily,
    qBipartiteSSCDefect, qBipartiteMatchMass, subMeasMass, SubMeas.liftLeft] using
    (max_le hhelperErr_nonneg hhelperGap_absorbed)

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


