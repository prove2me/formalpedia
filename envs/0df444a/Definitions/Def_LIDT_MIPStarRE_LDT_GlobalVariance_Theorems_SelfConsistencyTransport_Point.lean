-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:04:42.223012+00:00
-- url     : https://prove2.me/theorems/754fd2a6-a4d9-493b-9de0-c18b2a67876d
-- title:
--   LIDT definitions: LDT / GlobalVariance / Theorems / SelfConsistencyTransport / Point
-- statement:
--   This bundle transports the strategy's point self-consistency to events determined by the value of a fixed polynomial. The weighted forms insert the square root of a polynomial submeasurement outcome and the grouped form sums over all polynomials sharing the same point value, preparing the local-variance-of-points argument.
--
--   Principal definitions:
--   - `pointConditionedEventSelfConsistency`: For a good strategy and polynomial $g$, the point events asserting answer $g(u)$ on the two registers satisfy an SDD bound of $2\delta$ under uniform points.
--   - `pointConditionedEventSelfConsistency_weighted_point`: After multiplying by the square-root weight from a submeasurement outcome $G_g$, the averaged squared distance between the left and right weighted point events remains at most $2\delta$.
--   - `pointConditionedEventSelfConsistency_weighted_point_sum`: Summing the preceding weighted estimate over all polynomial outcomes preserves the $2\delta$ bound, using the submeasurement inequality on each evaluation fiber.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/Point.lean#L27-L224

-- Generated from MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/Point.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
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

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-! # Point-event self-consistency transport

This module contains the point self-consistency endpoints for the six-step
local-variance transport chain in `lem:local-variance-of-points`
(`expansion.tex`, lines 300--311).  These are the first and last `2δ`
moves; the point-line `2ε` moves live in `PointLine.lean`.
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section

/-! ## Good-strategy interfaces for the local-variance transport chain -/

/-- The `2δ` self-consistency interface for the point event
`A^u_{g(u)}`.

This is the evaluated, two-outcome version of the first/last moves in
`lem:local-variance-of-points` (`expansion.tex`, lines 305--306 and 310--311):
postprocess the point measurement by the event `a = g(u)`, then apply
`prop:two-notions-of-self-consistency-after-evaluation` to the good-strategy
self-consistency branch. The remaining six-step proof still has to pull this
point-distribution estimate to the hypercube-edge sampling and weight it by
`(G_g)^{1/2}` via `prop:cab-approx-delta`. -/
lemma pointConditionedEventSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (g : Polynomial params) :
    SDDRel strategy.state (uniformDistribution (Point params))
      (IdxSubMeas.liftLeft
        (fun u : Point params =>
          pointConditionedEventSubMeasAtPolynomial params strategy g u))
      (IdxSubMeas.liftRight
        (fun u : Point params =>
          pointConditionedEventSubMeasAtPolynomial params strategy g u))
      (2 * delta) := by
  have hssc :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
    refine ⟨?_⟩
    simpa [SymStrat.selfConsistencyFailureProbability] using
      hgood.selfConsistencyTest
  change SDDRel strategy.state (uniformDistribution (Point params))
    (IdxSubMeas.liftLeft
      (fun u : Point params =>
        postprocess (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement u)
          (fun a : Fq params => if a = g u then some () else none)))
    (IdxSubMeas.liftRight
      (fun u : Point params =>
        postprocess (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement u)
          (fun a : Fq params => if a = g u then some () else none)))
    (2 * delta)
  exact
    twoNotionsOfSelfConsistencyAfterEvaluation
      strategy.state strategy.permInvState
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      delta
      (fun u a => if a = g u then some () else none)
      hssc

/-- The first self-consistency move in `lem:local-variance-of-points`, after
applying `prop:cab-approx-delta` with the multiplier `I ⊗ (G_g)^{1/2}` but
before pulling the point marginal to the hypercube-edge distribution.

This proves the weighted native-distribution version of `expansion.tex`,
lines 305--306:
`A^u_{g(u)} ⊗ (G_g)^{1/2} ≈_{2δ} I ⊗ (G_g)^{1/2} A^u_{g(u)}`. -/
lemma pointConditionedEventSelfConsistency_weighted_point
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (uniformDistribution (Point params))
      (fun u =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
        ev strategy.state (Dᴴ * D)) ≤
      2 * delta := by
  classical
  let pointEvent : IdxSubMeas (Point params) (Option Unit) ι :=
    fun u => pointConditionedEventSubMeasAtPolynomial params strategy g u
  let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
  let R : MIPStarRE.Quantum.Op (ι × ι) := rightTensor (ι₁ := ι) S
  let C : Point params → Unit → Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    fun _ _ _ => R
  have hbase := pointConditionedEventSelfConsistency params strategy eps delta gamma hgood g
  have hbaseBound :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          qSDDCore strategy.state
            (fun a : Option Unit => ((IdxSubMeas.liftLeft pointEvent) u).outcome a)
            (fun a : Option Unit => ((IdxSubMeas.liftRight pointEvent) u).outcome a)) ≤
        2 * delta := by
    simpa [sddError, qSDD, pointEvent] using hbase.squaredDistanceBound
  have hselected_le :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          qSDDCore strategy.state
            (fun _ : Unit => ((IdxSubMeas.liftLeft pointEvent) u).outcome (some ()))
            (fun _ : Unit => ((IdxSubMeas.liftRight pointEvent) u).outcome (some ()))) ≤
        avgOver (uniformDistribution (Point params))
          (fun u =>
            qSDDCore strategy.state
              (fun a : Option Unit => ((IdxSubMeas.liftLeft pointEvent) u).outcome a)
              (fun a : Option Unit => ((IdxSubMeas.liftRight pointEvent) u).outcome a)) := by
    exact qSDDCore_optionUnit_some_le strategy.state (uniformDistribution (Point params))
      (fun u a => ((IdxSubMeas.liftLeft pointEvent) u).outcome a)
      (fun u a => ((IdxSubMeas.liftRight pointEvent) u).outcome a)
  have hAB :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          qSDDCore strategy.state
            (fun _ : Unit => ((IdxSubMeas.liftLeft pointEvent) u).outcome (some ()))
            (fun _ : Unit => ((IdxSubMeas.liftRight pointEvent) u).outcome (some ()))) ≤
        2 * delta := le_trans hselected_le hbaseBound
  have hC : ∀ u a, ∑ b : Unit, (C u a b)ᴴ * C u a b ≤ 1 := by
    intro u a
    simpa [C, R, S] using rightPolynomialWeightSqrt_contraction
      (params := params) (G := G) (g := g)
  have hcab :=
    cabApproxDelta strategy.state (uniformDistribution (Point params))
      (fun u _ => ((IdxSubMeas.liftLeft pointEvent) u).outcome (some ()))
      (fun u _ => ((IdxSubMeas.liftRight pointEvent) u).outcome (some ()))
      C (2 * delta) hAB hC
  simpa [qSDDCore, C, R, S, pointEvent, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
    weightedPointConditionedOperatorAtPolynomial,
    weightedPointConditionedRightOperatorAtPolynomial,
    rightTensor_mul_leftTensor_eq_opTensor, rightTensor_mul_rightTensor] using hcab

/-- Grouped-by-evaluation-value endpoint for the first self-consistency move in
`lem:local-variance-of-points`.

This is the sum-level analogue of `pointConditionedEventSelfConsistency_weighted_point`.
It follows the transport at `references/ldt-paper/expansion.tex`, lines
305--306, but first groups all polynomials with the same value `g(u)`.  The
multiplier family is `0` away from the fiber `a = g(u)` and is
`I ⊗ (G_g)^{1/2}` on that fiber, so the `cabApproxDelta` contraction is supplied
by the submeasurement inequality `∑_{g : g(u)=a} G_g ≤ I`.  Consequently the
bound is `2δ` for the polynomial sum, with no polynomial-cardinality loss. -/
lemma pointConditionedEventSelfConsistency_weighted_point_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
          ev strategy.state (Dᴴ * D))) ≤
      2 * delta := by
  classical
  let pointMeas : IdxSubMeas (Point params) (Fq params) ι :=
    fun u => (strategy.pointMeasurement u).toSubMeas
  have hbase :
      SDDRel strategy.state (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft pointMeas)
        (IdxSubMeas.liftRight pointMeas)
        (2 * delta) := by
    have hssc :
        BipartiteSSCRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
      refine ⟨?_⟩
      simpa [SymStrat.selfConsistencyFailureProbability] using
        hgood.selfConsistencyTest
    change SDDRel strategy.state (uniformDistribution (Point params))
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (2 * delta)
    exact
      twoNotionsOfSelfConsistency strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta
        ⟨strategy.permInvState, hssc⟩
  have hbaseBound :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          qSDDCore strategy.state
            (fun a : Fq params => ((IdxSubMeas.liftLeft pointMeas) u).outcome a)
            (fun a : Fq params => ((IdxSubMeas.liftRight pointMeas) u).outcome a)) ≤
        2 * delta := by
    simpa [sddError, qSDD, pointMeas] using hbase.squaredDistanceBound
  simpa using
    cabApproxDelta_sum_from_sdd params strategy.state
      (uniformDistribution (Point params))
      (fun u => u)
      (fun u a => ((IdxSubMeas.liftLeft pointMeas) u).outcome a)
      (fun u a => ((IdxSubMeas.liftRight pointMeas) u).outcome a)
      (fun u g => weightedPointConditionedOperatorAtPolynomial params strategy G g u)
      (fun u g => weightedPointConditionedRightOperatorAtPolynomial params strategy G g u)
      G (2 * delta) hbaseBound
      (by
        intro u g
        let A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u
        let S := polynomialWeightSqrtOperator params G g
        change rightTensor (ι₁ := ι) S * leftTensor (ι₂ := ι) A = opTensor A S
        exact rightTensor_mul_leftTensor_eq_opTensor A S)
      (by
        intro u g
        let A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u
        let S := polynomialWeightSqrtOperator params G g
        change rightTensor (ι₁ := ι) S * rightTensor (ι₁ := ι) A =
          rightTensor (ι₁ := ι) (S * A)
        exact rightTensor_mul_rightTensor S A)








end

end MIPStarRE.LDT.GlobalVariance

end LIDT


