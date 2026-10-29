-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_Core
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:57:39.272179+00:00
-- url     : https://prove2.me/theorems/99fc8a19-0a91-4d3f-81f1-51beff3cdfee
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / SelfImprovementTop / Core
-- statement:
--   This bundle defines the top-level self-improvement results and their large-error fallback. It connects a slackness-carrying SDP conclusion to the helper theorem, then derives the full self-improvement statement and its specialization using only the axis-parallel and point self-consistency hypotheses.
--
--   Principal definitions:
--   - `self_improvement_helper_with_slackness_of_sdp_statement_with_slackness`: derives the helper result from an SDP slackness statement.
--   - `self_improvement_helper_with_slackness`: the helper result under complementary slackness.
--   - `selfImprovement_of_error_ge_one`: handles the large-error fallback.
--   - `selfImprovement`: the formal main self-improvement statement.
--   - `selfImprovement_of_axisParallel_selfConsistency`: specializes self-improvement to the needed self-consistency components.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean#L48-L694

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_ErrorBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_AddInUFullStatement
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Assembly
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_PostDeleteA
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_FinalFields
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_SelfCloseness
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
# Self-improvement theorem variants

The main `selfImprovementHelper` and the `selfImprovement` theorem corresponding
to `thm:self-improvement` in the blueprint.

## Contents

- **selfImprovementHelper** — `lem:self-improvement-helper`, with the paper's
  input consistency hypothesis and four helper conclusions.
- **self_improvement_helper_with_slackness** — companion helper producing the
  slackness-carrying helper conclusion from the Section 9 SDP statement.
- **selfImprovement** — the statement corresponding to `thm:self-improvement`.

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

/-- Conditional form of the helper lemma from a slackness-carrying SDP
conclusion.

This is the companion to `selfImprovementHelper` when the Section 9
strong-duality conclusion has already been supplied as
`SdpStatementWithSlackness`.  The helper output therefore carries the
complementary-slackness equations needed by the helper-completeness chain. -/
lemma self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hsdp : SdpStatementWithSlackness params strategy)
    (hgood : strategy.IsGood eps delta gamma)
    (_nu : Error)
    -- These arguments keep the slackness-carrying conclusion aligned with the
    -- helper theorem; the constructed SDP measurement is independent of `G`.
    (_G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta := by
  obtain ⟨T, Z, hsdpPair⟩ := hsdp.witness
  let Hhat : SubMeas (Polynomial params) ι :=
    averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  refine ⟨T, Hhat, Z, ?_⟩
  refine
    { toHelperConclusion := ?_
      complementarySlackness := ?_ }
  · refine
      { sdpWitness := ?_
        averagedConstruction := rfl
        addInUVarianceBound := ?_ }
    · exact hsdpPair.toSdpOptimalPair
    · exact addInU (ι := ι) params strategy eps delta gamma hgood T
  · intro g
    exact hsdpPair.complementarySlackness g

/-- Helper lemma driven by the Section 9 SDP statement with complementary
slackness.

This applies the Section 9 statement `sdp_statement_with_slackness`, which
records the strong-duality conclusion with complementary slackness. -/
lemma self_improvement_helper_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (nu : Error)
    (G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusionWithSlackness params strategy T H Z eps delta :=
  self_improvement_helper_with_slackness_of_sdp_statement_with_slackness
    params strategy eps delta gamma
    (sdp_statement_with_slackness (ι := ι) params strategy)
    hgood nu G



/-- Internal large-error fallback for `selfImprovement`.

When the literal threshold `selfImprovementError` is at least `1`, the paper
conclusion is trivial: take the zero projective submeasurement and the identity
dual witness. -/
lemma selfImprovement_of_error_ge_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (_hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (herror_ge_one : 1 ≤ selfImprovementError params eps delta)
    (hnu_nonneg : 0 ≤ nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  let H : ProjSubMeas (Polynomial params) ι := zeroProjSubMeas
  let Z : MIPStarRE.Quantum.Op ι := 1
  have herror_nonneg : 0 ≤ selfImprovementError params eps delta := by
    linarith
  refine ⟨H, Z, ?_⟩
  refine
    { completeness := ?_
      pointConsistency := ?_
      selfCloseness := ?_
      positiveSemidefiniteWitness := ?_
      dualDominatesAveragedPoint := ?_
      projectiveResidualBound := ?_ }
  · refine ⟨?_⟩
    have hbound : (1 - nu) - selfImprovementError params eps delta ≤ 0 := by
      linarith
    have hmass_zero : subMeasMass strategy.state H.toSubMeas.liftLeft = 0 := by
      simp [H, subMeasMass, zeroProjSubMeas, SubMeas.liftLeft, leftTensor,
        ev_zero]
    rw [hmass_zero]
    linarith
  · exact
      ConsRel.mono herror_ge_one
        ⟨bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params H.toSubMeas)⟩
  · refine ⟨?_⟩
    have hsdd_zero :
        sddError strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ι) H.toSubMeas)) = 0 := by
      simp [H, zeroProjSubMeas, constSubMeasFamily, leftPlacedSubMeas,
        rightPlacedSubMeas, sddError, avgOver, uniformDistribution, qSDD,
        qSDDCore, leftTensor, rightTensor, ev_zero]
    rw [hsdd_zero]
    exact herror_nonneg
  · simp [Z]
  · intro g
    simpa [Z, sdpDualSlackOperator] using
      (sub_nonneg.mpr (averagedPointOperator_le_one params strategy g))
  · have hgap_one : projectiveBoundednessGap params strategy H Z = 1 := by
      simp [H, Z, projectiveBoundednessGap, projectiveResidualOperator,
        zeroProjSubMeas, leftTensor, rightTensor,
        ev_one_of_isNormalized strategy.state strategy.isNormalized]
    rw [hgap_one]
    exact herror_ge_one

/--
Formal statement corresponding to the blueprint theorem `thm:self-improvement`,
with the input consistency hypothesis from the LDT paper.

The theorem assumes a measurement `G` whose polynomial evaluation family is
consistent with the point measurement at error `nu`. It must produce a
projective polynomial submeasurement satisfying the four self-improvement
conclusions. The paper and blueprint impose the `(eps, delta, gamma)`-good
strategy condition as a standing hypothesis for the self-improvement section
(`blueprint/src/chapter/ch07_self_improvement.tex`, line 4); Lean records it
here as the explicit hypothesis `hgood`. The source-facing theorem remains
visible with the paper statement; the intermediate estimates are assembled by
named internal construction lemmas rather than hidden in a conditional theorem
with extra hypotheses. -/
theorem selfImprovement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  have heps : 0 ≤ eps := eps_nonneg_of_isGood params strategy hgood
  have hdelta : 0 ≤ delta := delta_nonneg_of_isGood params strategy hgood
  have hnu_nonneg : 0 ≤ nu := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas))
      hcons.offDiagonalBound
  by_cases heps_le_one : eps ≤ 1
  · by_cases hdelta_le_one : delta ≤ 1
    · by_cases hd_le_q : (params.d : Error) ≤ (params.q : Error)
      · rcases self_improvement_helper_with_slackness params strategy eps delta gamma
            hgood nu G with
          ⟨T, Hhat, Z, hhelperWithSlackness⟩
        let hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta :=
          hhelperWithSlackness.toHelperConclusion
        have hpointSSC :
            BipartiteSSCRel strategy.state (uniformDistribution (Point params))
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
          exact ⟨by
            simpa [SymStrat.selfConsistencyFailureProbability] using
              hgood.selfConsistencyTest⟩
        have haddInUFull : AddInUFullStatement params strategy T eps delta :=
          addInUFullStatement_of_isGood (ι := ι) params strategy eps delta gamma hgood T
        have htransfer :
            |addInULeftQuantity params strategy
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                Hhat
                (pointConsistencyAddInUSelection params) -
              addInURightQuantity params strategy
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                T.toSubMeas
                (pointConsistencyAddInUSelection params)| ≤
              addInUError params eps delta := by
          have htransfer :=
            haddInUFull.selectionDependentTransfer
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              (pointConsistencyAddInUSelection params)
          simpa [hhelper.averagedConstruction] using htransfer
        have hhelperCompleteness :
            CompletenessAtLeast strategy.state Hhat.liftLeft
              ((1 - nu) - selfImprovementHelperError params eps delta) :=
          helper_completeness_of_self_consistency_helper_slackness_input_consistency
            params strategy G eps delta nu heps hdelta hhelperWithSlackness hpointSSC hcons
        have hlocal :
            (∑ g : Polynomial params,
              localVarianceDeviationAtPolynomial params strategy strategy.state
                T.toSubMeas g) ≤
              localVarianceOfPointsError params eps delta :=
          localVarianceDeviation_sum_le_localVarianceOfPointsError
            params strategy eps delta gamma hgood T.toSubMeas
        have hclone :
            |helperDeleteAQuantity params strategy T.toSubMeas -
              helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
                Real.sqrt (selfImprovementVarianceError params eps delta) :=
          helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
            params strategy eps delta T.toSubMeas hlocal
        have hmove :
            |helperDeleteAClonedQuantity params strategy T.toSubMeas -
              helperMoveOverVQuantity params strategy T.toSubMeas| ≤
                Real.sqrt (2 * delta) :=
          helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
            params strategy delta T.toSubMeas hpointSSC
        have hslack :
            ∀ h : Polynomial params,
              T.toSubMeas.outcome h * averagedPointOperator params strategy h =
                T.toSubMeas.outcome h * Z :=
          fun h =>
            helper_slackness_eq_of_helper_with_slackness
              params strategy eps delta hhelperWithSlackness h
        have hsscBounds :
            HelperStrongSelfConsistencyBounds params strategy T Hhat eps delta :=
          helper_ssc_bounds_of_scalarTransports_pointTransfer
            params strategy eps delta hhelper hpointSSC hlocal hclone hmove
            hslack htransfer
        have hhelperSSC :
            BipartiteSSCRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily Hhat)
              (selfImprovementHelperError params eps delta) :=
          helper_strong_self_consistency_of_helper_conclusion
            params strategy eps delta heps hdelta hd_le_q hhelper hsscBounds
        rcases MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization
            strategy.state strategy.permInvState strategy.isNormalized
            Hhat (selfImprovementHelperError params eps delta) hhelperSSC with
          ⟨H, horth⟩
        have hprojectiveUpperGap :
            ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
              ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
                2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
          let Pconst : IdxProjSubMeas Unit (Polynomial params) (ι × ι) :=
            fun _ => ProjSubMeas.liftLeft H
          have hcomp :
              Preliminaries.CompTransferStmt strategy.state
                (uniformDistribution Unit)
                (constSubMeasFamily Hhat.liftLeft)
                Pconst
                (selfImprovementOrthogonalizationError params eps delta) := by
            apply Preliminaries.completenessTransferProjectiveP
              strategy.state (uniformDistribution Unit) strategy.isNormalized
              (uniformDistribution_weight_sum_le_one Unit)
              (constSubMeasFamily Hhat.liftLeft)
              Pconst
              (selfImprovementOrthogonalizationError params eps delta)
            change SDDRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily Hhat.liftLeft)
              (constSubMeasFamily H.toSubMeas.liftLeft)
              (orthonormalizationError (selfImprovementHelperError params eps delta))
            exact horth
          have hleft :
              ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) ≥
                ev strategy.state (leftTensor (ι₂ := ι) H.toSubMeas.total) -
                  2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
            simpa [idxSubMeasMass, avgOver, uniformDistribution, subMeasMass,
              constSubMeasFamily, Pconst, IdxProjSubMeas.toIdxSubMeas,
              ProjSubMeas.liftLeft, SubMeas.liftLeft, mkLeftPlacedSubMeas_total] using
              hcomp.completenessTransfer
          have hleft' :
              ev strategy.state (leftTensor (ι₂ := ι) H.toSubMeas.total) -
                ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) ≤
                  2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
            linarith
          rw [strategy.permInvState.swap_ev H.toSubMeas.total,
            strategy.permInvState.swap_ev Hhat.total] at hleft'
          exact hleft'
        have hhelperUpperGap :
            ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) -
              ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) ≤
                selfImprovementHelperError params eps delta +
                  2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
          have horthIdx :
              SDDRel strategy.state (uniformDistribution Unit)
                (IdxSubMeas.liftLeft (constSubMeasFamily Hhat))
                (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
                (selfImprovementOrthogonalizationError params eps delta) := by
            change SDDRel strategy.state (uniformDistribution Unit)
              (constSubMeasFamily Hhat.liftLeft)
              (constSubMeasFamily H.toSubMeas.liftLeft)
              (orthonormalizationError (selfImprovementHelperError params eps delta))
            exact horth
          have hcomp :=
            Preliminaries.completenessTransferSelfConsistentA
              strategy.state strategy.permInvState strategy.isNormalized
              (uniformDistribution Unit)
              (uniformDistribution_weight_sum_le_one Unit)
              (constSubMeasFamily Hhat)
              (constSubMeasFamily H.toSubMeas)
              (selfImprovementHelperError params eps delta)
              (selfImprovementOrthogonalizationError params eps delta)
              hhelperSSC horthIdx
          have hleft :
              ev strategy.state (leftTensor (ι₂ := ι) H.toSubMeas.total) ≥
                ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) -
                  selfImprovementHelperError params eps delta -
                    2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
            simpa [idxSubMeasMass, avgOver, uniformDistribution, subMeasMass,
              constSubMeasFamily, IdxSubMeas.liftLeft, SubMeas.liftLeft,
              mkLeftPlacedSubMeas_total] using hcomp
          have hleft' :
              ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) -
                ev strategy.state (leftTensor (ι₂ := ι) H.toSubMeas.total) ≤
                  selfImprovementHelperError params eps delta +
                    2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
            linarith
          rw [strategy.permInvState.swap_ev Hhat.total,
            strategy.permInvState.swap_ev H.toSubMeas.total] at hleft'
          exact hleft'
        have hhelperError_nonneg :
            0 ≤ selfImprovementHelperError params eps delta :=
          selfImprovementHelperError_nonneg params eps delta
        have hTotalDiff :
            |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
              ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| ≤
                selfImprovementHelperError params eps delta +
                  2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
          refine abs_le.mpr ?_
          constructor
          · linarith [hhelperUpperGap]
          · linarith [hprojectiveUpperGap, hhelperError_nonneg]
        have hhelperSSCPoint :
            BipartiteSSCRel strategy.state (uniformDistribution (Point params))
              (fun _ : Point params => Hhat)
              (selfImprovementHelperError params eps delta) :=
          bipartiteSSCRel_uniform_const strategy.state Hhat
            (selfImprovementHelperError params eps delta) hhelperSSC
        have horthPoint :
            SDDRel strategy.state (uniformDistribution (Point params))
              (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas (fun _ : Point params => H)))
              (IdxSubMeas.liftLeft (fun _ : Point params => Hhat))
              (selfImprovementOrthogonalizationError params eps delta) := by
          change SDDRel strategy.state (uniformDistribution (Point params))
            (fun _ : Point params => H.toSubMeas.liftLeft)
            (fun _ : Point params => Hhat.liftLeft)
            (selfImprovementOrthogonalizationError params eps delta)
          exact sddRel_uniform_const strategy.state H.toSubMeas.liftLeft Hhat.liftLeft
            (selfImprovementOrthogonalizationError params eps delta)
            (MIPStarRE.LDT.Preliminaries.sddRel_symm strategy.state
              (uniformDistribution Unit)
              (constSubMeasFamily Hhat.liftLeft)
              (constSubMeasFamily H.toSubMeas.liftLeft)
              (selfImprovementOrthogonalizationError params eps delta) horth)
        have hdataRev :
            SDDRel strategy.state (uniformDistribution (Point params))
              ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
              ((polynomialEvaluationFamily params Hhat).liftLeft)
              (selfImprovementDataProcessingError params eps delta) := by
          rw [selfImprovementDataProcessingError_eq params eps delta]
          change SDDRel strategy.state (uniformDistribution (Point params))
            (IdxSubMeas.liftLeft
              (fun q : Point params => postprocess H.toSubMeas (fun g => g q)))
            (IdxSubMeas.liftLeft
              (fun q : Point params => postprocess Hhat (fun g => g q)))
            (8 * selfImprovementHelperError params eps delta +
              8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta))
          exact Preliminaries.selfConsistencyImpliesDataProcessing
            strategy.state strategy.permInvState strategy.isNormalized
            (uniformDistribution (Point params))
            (uniformDistribution_weight_sum_le_one (Point params))
            (fun _ : Point params => Hhat)
            (fun _ : Point params => H)
            (selfImprovementHelperError params eps delta)
            (selfImprovementOrthogonalizationError params eps delta)
            (fun u g => g u)
            hhelperSSCPoint horthPoint
        have hdata :
            SDDRel strategy.state (uniformDistribution (Point params))
              ((polynomialEvaluationFamily params Hhat).liftLeft)
              ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
              (selfImprovementDataProcessingError params eps delta) :=
          MIPStarRE.LDT.Preliminaries.sddRel_symm strategy.state
            (uniformDistribution (Point params))
            ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
            ((polynomialEvaluationFamily params Hhat).liftLeft)
            (selfImprovementDataProcessingError params eps delta) hdataRev
        have hfinal : SelfImprovementFinalFields params strategy H Z eps delta nu :=
          final_fields_of_helper_outputs_of_total_difference
            params strategy eps delta nu
            (selfImprovementHelperError params eps delta +
              2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta))
            heps heps_le_one hdelta hdelta_le_one hd_le_q
            hhelper hhelperCompleteness hhelperSSC hpointSSC hslack htransfer
            horth hdata hTotalDiff
            (by
              have hbase :=
                final_fields_point_consistency_total_difference_error_le_selfImprovementError
                  params eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
              nlinarith)
        exact ⟨H, Z,
          { completeness := hfinal.completeness
            pointConsistency := hfinal.pointConsistency
            selfCloseness := hfinal.selfCloseness
            positiveSemidefiniteWitness := hhelper.sdpWitness.dualPositive
            dualDominatesAveragedPoint := hhelper.sdpWitness.dualFeasible
            projectiveResidualBound := hfinal.projectiveResidualBound }⟩
      · have hdq_ge_one : 1 ≤ ((params.d : Error) / (params.q : Error)) := by
          exact (one_le_div₀ params.q_cast_pos).2 (le_of_lt (lt_of_not_ge hd_le_q))
        have hdq_pow_ge_one :
            1 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) := by
          have hpow :=
            Real.rpow_le_rpow (show (0 : Error) ≤ 1 by positivity) hdq_ge_one
              (by positivity : 0 ≤ (1 / (32 : Error)))
          simpa using hpow
        have hsum_ge_one :
            1 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) := by
          unfold finalStagePowerSum
          have heps_pow_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
            Real.rpow_nonneg heps _
          have hdelta_pow_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
            Real.rpow_nonneg hdelta _
          nlinarith
        have herror_ge_one : 1 ≤ selfImprovementError params eps delta := by
          rw [selfImprovementError_eq_finalStagePowerSum]
          nlinarith [one_le_m_cast params, hsum_ge_one]
        exact selfImprovement_of_error_ge_one
          params strategy eps delta gamma nu hgood G herror_ge_one hnu_nonneg
    · have hdelta_ge_one : 1 ≤ delta := le_of_lt (lt_of_not_ge hdelta_le_one)
      have hdelta_pow_ge_one : 1 ≤ Real.rpow delta (1 / (32 : Error)) := by
        have hpow :=
          Real.rpow_le_rpow (show (0 : Error) ≤ 1 by positivity) hdelta_ge_one
            (by positivity : 0 ≤ (1 / (32 : Error)))
        simpa using hpow
      have hsum_ge_one : 1 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) := by
        unfold finalStagePowerSum
        have heps_pow_nonneg : 0 ≤ Real.rpow eps (1 / (32 : Error)) :=
          Real.rpow_nonneg heps _
        have hdq_pow_nonneg :
            0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) :=
          Real.rpow_nonneg (d_q_ratio_nonneg params) _
        nlinarith
      have herror_ge_one : 1 ≤ selfImprovementError params eps delta := by
        rw [selfImprovementError_eq_finalStagePowerSum]
        nlinarith [one_le_m_cast params, hsum_ge_one]
      exact selfImprovement_of_error_ge_one
        params strategy eps delta gamma nu hgood G herror_ge_one hnu_nonneg
  · have heps_ge_one : 1 ≤ eps := le_of_lt (lt_of_not_ge heps_le_one)
    have heps_pow_ge_one : 1 ≤ Real.rpow eps (1 / (32 : Error)) := by
      have hpow :=
        Real.rpow_le_rpow (show (0 : Error) ≤ 1 by positivity) heps_ge_one
          (by positivity : 0 ≤ (1 / (32 : Error)))
      simpa using hpow
    have hsum_ge_one : 1 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) := by
      unfold finalStagePowerSum
      have hdelta_pow_nonneg : 0 ≤ Real.rpow delta (1 / (32 : Error)) :=
        Real.rpow_nonneg hdelta _
      have hdq_pow_nonneg :
          0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) := by
        exact Real.rpow_nonneg (d_q_ratio_nonneg params) _
      nlinarith
    have herror_ge_one : 1 ≤ selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]
      nlinarith [one_le_m_cast params, hsum_ge_one]
    exact selfImprovement_of_error_ge_one
      params strategy eps delta gamma nu hgood G herror_ge_one hnu_nonneg

/-- Self-improvement only uses the axis-parallel and point self-consistency
parts of the good-strategy hypothesis.

Paper origin: `references/ldt-paper/self_improvement.tex:24-60` and
`references/ldt-paper/self_improvement.tex:631-811`.

The displayed Section 9 construction is written in terms of the point
measurement \(A^u\), the input polynomial measurement \(G\), and the scalar
bounds `eps` and `delta`; the diagonal-line error parameter `gamma` is part of
the paper's standing good-strategy context but does not occur in
`selfImprovementError` or in `SelfImprovementConclusion`.  This wrapper makes
that independence explicit: it supplies the diagonal component of `IsGood` by
taking the actual diagonal failure as the auxiliary parameter, applies the
source theorem, and then reindexes the conclusion at the caller's `gamma`. -/
theorem selfImprovement_of_axisParallel_selfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  let gamma₀ : Error := strategy.diagonalFailureProbability
  have hgood₀ : strategy.IsGood eps delta gamma₀ :=
    { axisParallelTest := haxis
      selfConsistencyTest := hself
      diagonalLineTest := le_rfl }
  rcases selfImprovement params strategy eps delta gamma₀ nu hgood₀ G hcons with
    ⟨H, Z, hHZ⟩
  exact ⟨H, Z,
    { completeness := hHZ.completeness
      pointConsistency := hHZ.pointConsistency
      selfCloseness := hHZ.selfCloseness
      positiveSemidefiniteWitness := hHZ.positiveSemidefiniteWitness
      dualDominatesAveragedPoint := hHZ.dualDominatesAveragedPoint
      projectiveResidualBound := hHZ.projectiveResidualBound }⟩

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


