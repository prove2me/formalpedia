-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_MainTheorems
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_MainTheorems
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:13:34.734667+00:00
-- url     : https://prove2.me/theorems/25966788-e453-4106-92e1-381ddd022065
-- title:
--   LIDT definitions: LDT / GlobalVariance / Theorems / MainTheorems
-- statement:
--   This bundle collects the main reductions for global variance in the LDT strategy state. It derives local and global variance from deviation expressions, proves the local-to-global factor, and combines the transport-chain estimate with the paper's final error term.
--
--   Principal definitions:
--   - `localVarianceOfPointsFromEdgeDeviation`: reduces the local variance-of-points statement from edge deviation.
--   - `globalVarianceOfPointsFromLocalDeviation`: reduces global variance from local deviation.
--   - `globalVarianceDeviation_sum_le_m_mul_localVarianceDeviation_sum`: gives the sum-level local-to-global factor.
--   - `globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le`: transfers a local sum bound to the global sum bound.
--   - `globalVarianceOfPointsFromTransportChainBound`: derives the strategy-state global-variance bound from the six-step transport chain.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Theorems/MainTheorems.lean#L29-L261

-- Generated from MIPStarRE/LDT/GlobalVariance/Theorems/MainTheorems.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_SumForm
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-! # Main variance theorem reductions

This module contains the high-level theorem reductions for
`lem:local-variance-of-points`, `lem:global-variance-of-points`, and
`lem:generalize-b`. These combine the algebraic identities, collision
expansions, and transport estimates from the preceding modules into the final
statement records used by downstream consumers.
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section


/-! ## Strategy-state reductions -/

/-- Strict reduction for `lem:local-variance-of-points` on the strategy state.

Compared with the former supplied-bounds reduction, this theorem does not require
the local-variance bound as a separate hypothesis: it derives it from
the edgewise weighted squared-norm estimate using
`localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial`.
The remaining analytic input is exactly the paper's six-step edge transport
bound, not a conclusion-shaped local-variance hypothesis. -/
lemma localVarianceOfPointsFromEdgeDeviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (G : SubMeas (Polynomial params) ι)
    (hedge :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceOfPointsError params eps delta) :
    LocalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  refine
    { aggregateEdgeComparison := by
        exact sddRel_unit_family_of_pointwise strategy.state
          (rerandomizeCoord params)
          (localVarianceLeftFamily params strategy G)
          (localVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [localVarianceLeftFamily])
          (by
            intro uv
            simp [localVarianceRightFamily])
          (localVarianceOfPointsError params eps delta) (by
            intro g
            simpa [localVarianceDeviationAtPolynomial] using hedge g)
      pointwiseEdgeNormBound := hedge
      pointwiseLocalVarianceBound :=
        fun g => pointConditionedLocalVarianceAtPolynomial_le_of_deviation
          params strategy G (hedge g)
      averagedLocalVarianceBound :=
        avgOver_polynomialDistribution_le_of_pointwise params
          (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
          (localVarianceOfPointsError params eps delta)
          (fun g => pointConditionedLocalVarianceAtPolynomial_le_of_deviation
            params strategy G (hedge g)) }

-- This lemma builds the global-variance record from the local record and the
-- expansion transfer, expanding several indexed operator families.
/-- Reduction for `lem:global-variance-of-points` on the strategy state.

This theorem proves the independent-points norm bound from the local edge norm
estimate by applying `lem:local-to-global` to the weighted state and using the
exact norm/variance identities above. The remaining analytic input is the local
edge transport estimate from `lem:local-variance-of-points`. -/
lemma globalVarianceOfPointsFromLocalDeviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (G : SubMeas (Polynomial params) ι)
    (hlocalDev :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceOfPointsError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  let hlocal := localVarianceOfPointsFromEdgeDeviation params strategy eps delta G hlocalDev
  have hglobalNorm :
      ∀ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          globalVarianceOfPointsError params eps delta :=
    globalVarianceOfPoints_bound_of_local params eps delta
      (fun g => globalVarianceDeviationAtPolynomial params strategy strategy.state G g)
      (fun g => localVarianceDeviationAtPolynomial params strategy strategy.state G g)
      (globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial
        params strategy G)
      hlocalDev
  have hglobalVariance :
      ∀ g : Polynomial params,
        pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
          globalVarianceOfPointsError params eps delta :=
    globalVarianceOfPoints_bound_of_local params eps delta
      (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
      (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
      (pointConditionedExpansionTransfer params strategy G)
      hlocal.pointwiseLocalVarianceBound
  refine
    { aggregateGlobalComparison := by
        exact sddRel_unit_family_of_pointwise strategy.state
          (independentPointPair params)
          (globalVarianceLeftFamily params strategy G)
          (globalVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [globalVarianceLeftFamily, localVarianceLeftFamily])
          (by
            intro uv
            simp [globalVarianceRightFamily, localVarianceRightFamily])
          (globalVarianceOfPointsError params eps delta) (by
            intro g
            simpa [globalVarianceDeviationAtPolynomial] using hglobalNorm g)
      pointwiseGlobalNormBound := hglobalNorm
      pointwiseExpansionTransfer := pointConditionedExpansionTransfer params strategy G
      pointwiseGlobalVarianceBound := hglobalVariance
      averagedGlobalVarianceBound :=
        avgOver_polynomialDistribution_le_of_pointwise params
          (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
          (globalVarianceOfPointsError params eps delta) hglobalVariance }

-- The sum-level transfer expands both the global and local deviation families
-- over all polynomials.
/-- Sum-level local-to-global transfer for the polynomial-indexed squared-norm
form of `lem:global-variance-of-points`.

This is the unnormalized analogue of the pointwise
`globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial`:
the independent-points deviation summed over all polynomials is at most `m`
times the corresponding edge-deviation sum. -/
lemma globalVarianceDeviation_sum_le_m_mul_localVarianceDeviation_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      (params.m : Error) *
        ∑ g : Polynomial params,
          localVarianceDeviationAtPolynomial params strategy strategy.state G g := by
  calc
    (∑ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g)
        ≤ ∑ g : Polynomial params,
            (params.m : Error) *
              localVarianceDeviationAtPolynomial params strategy strategy.state G g :=
          Finset.sum_le_sum fun g _ =>
            globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial
              params strategy G g
    _ = (params.m : Error) *
        ∑ g : Polynomial params,
          localVarianceDeviationAtPolynomial params strategy strategy.state G g := by
          rw [Finset.mul_sum]

-- This polynomial-sum lemma combines the previous transfer with the public
-- error normalization, and its expanded statement has a large checked form.
/-- A polynomial-sum local-variance bound implies the corresponding sum-form
global-variance bound with the paper's `24m(ε + δ + md/q)` error term.

The hypothesis `hlocal` is the paper's `eq:equivalent-local-variance`
(`references/ldt-paper/expansion.tex:317--321`). The conclusion is the
sum-form squared-norm bound underlying `eq:global-variance-of-points-equation`
(`references/ldt-paper/expansion.tex:325--353`). -/
lemma globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (G : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
        localVarianceOfPointsError params eps delta) :
    (∑ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g) ≤
      globalVarianceOfPointsError params eps delta := by
  calc
    (∑ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy strategy.state G g)
        ≤ (params.m : Error) *
            ∑ g : Polynomial params,
              localVarianceDeviationAtPolynomial params strategy strategy.state G g :=
          globalVarianceDeviation_sum_le_m_mul_localVarianceDeviation_sum
            params strategy G
    _ ≤ (params.m : Error) * localVarianceOfPointsError params eps delta :=
          mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = globalVarianceOfPointsError params eps delta := by
          simp only [globalVarianceOfPointsError, localVarianceOfPointsError]
          ring

-- This theorem applies the post-triangle transport-chain bound to the
-- strategy-state local-variance record.


-- This theorem composes the transport-chain bound with the global-variance
-- reduction and therefore checks both record structures.
/-- Strategy-state global-variance reduction from the post-triangle six-step
local-variance transport-chain bound. -/
lemma globalVarianceOfPointsFromTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (hchain :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceTransportChainError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  refine globalVarianceOfPointsFromLocalDeviation params strategy eps delta G ?_
  intro g
  exact le_trans (hchain g)
    (localVarianceTransportChainError_le_localVarianceOfPointsError
      params strategy hgood)

-- The paper-facing theorem invokes the transport-chain theorem and the
-- strategy-state global-variance record constructor.


end

end MIPStarRE.LDT.GlobalVariance

end LIDT


