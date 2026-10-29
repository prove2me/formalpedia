-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:04:26.415038+00:00
-- url     : https://prove2.me/theorems/0a91e555-14aa-45da-abc6-681271a5b9f0
-- title:
--   LIDT definitions: LDT / GlobalVariance / Theorems / SelfConsistencyTransport / PointLine
-- statement:
--   This bundle transports point self-consistency to axis-line events. It defines the selected point and line events, identifies the line event with its evaluated operator, and records the symmetric and weighted forms needed for the rebasing argument.
--
--   Principal definitions:
--   - `axisParallelBaseEventConsistency`: The base-point event asserting that a point answer agrees with the polynomial evaluated at that point is self-consistent at the strategy's point error.
--   - `axisParallelBaseEventApproximation_swapped`: The same event after swapping the two registers is related by the corresponding state-dependent approximation.
--   - `axisParallelBaseEventApproximation_weighted_sample`: Inserting the square-root polynomial weight preserves the approximation bound under the sampled line distribution.
--   - `generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt`: The evaluated line operator is invariant under rebasing when its parameter is translated by the line point.
--   - `weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt`: The weighted evaluated operator has the same rebasing invariance.
--   - `axisParallelPointLineConsistency_weighted_leftToRightLineQuestion`: Transports the weighted point event to the left-to-right line question.
--   - `axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion`: Gives the corresponding right-to-left transport.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/PointLine.lean#L25-L416

-- Generated from MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/PointLine.lean by skeleton subtraction.
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

/-! # Axis-parallel point-line self-consistency transport

This module contains the point-line consistency and rebasing interfaces used in
the middle two `2ε` moves of the local-variance transport chain in
`lem:local-variance-of-points` (`expansion.tex`, lines 306--307 and
309--310).
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section

/-- The `ε` consistency interface for the point-line event at the base point of
an axis-parallel test sample.

For a sample `(u,i)`, the point side is the event `A^u_{g(u)}` and the line side
is the line-answer event obtained by evaluating the line polynomial at the base
parameter and testing equality with `g(u)`. This is the consistency input that
feeds the `2ε` approximation step at `expansion.tex`, line 307; the later
edge-transport proof still has to reindex from the base-point test sampling to
an arbitrary incident pair `(ℓ,u)` (using axis-line rebasing covariance) and then
apply `prop:simeq-to-approx`/`prop:cab-approx-delta`. -/
lemma axisParallelBaseEventConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (g : Polynomial params) :
    ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
      (fun s : AxisParallelTestSample params =>
        pointConditionedEventSubMeasAtPolynomial params strategy g s.1)
      (fun s : AxisParallelTestSample params =>
        postprocess (axisParallelLineAnswerFamily strategy s)
          (fun a : Fq params => if a = g s.1 then some () else none))
      eps := by
  have haxis :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy) eps := by
    refine ⟨?_⟩
    simpa [SymStrat.axisParallelFailureProbability] using
      hgood.axisParallelTest
  simpa [axisParallelPointAnswerFamily, pointConditionedEventSubMeasAtPolynomial] using
    (consRelDataProcessing_questionDependent
      strategy.state (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)
      eps
      (fun s a => if a = g s.1 then some () else none)
      haxis)

/-- Point-event measurement used by the base-point point-line consistency step. -/
private noncomputable def axisParallelBasePointEventMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) :
    IdxMeas (AxisParallelTestSample params) (Option Unit) ι :=
  fun s => (pointConditionedEventSubMeasAtPolynomial params strategy g s.1).toMeasurement (by
    unfold pointConditionedEventSubMeasAtPolynomial
    rw [postprocess_total]
    exact (strategy.pointMeasurement s.1).total_eq_one)

/-- Line-event measurement used by the base-point point-line consistency step. -/
private noncomputable def axisParallelBaseLineEventMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) :
    IdxMeas (AxisParallelTestSample params) (Option Unit) ι :=
  fun s =>
    (postprocess (axisParallelLineAnswerFamily strategy s)
      (fun a : Fq params => if a = g s.1 then some () else none)).toMeasurement (by
      rw [postprocess_total]
      unfold axisParallelLineAnswerFamily
      rw [postprocess_total]
      exact (strategy.axisParallelMeasurement { base := s.1, direction := s.2 }).total_eq_one)

/-- At a base-point sample, the selected line event is the left operator used
in the weighted point-line comparison. -/
private lemma axisParallelBaseLineEvent_some
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (s : AxisParallelTestSample params) :
    (postprocess (axisParallelLineAnswerFamily strategy s)
        (fun a : Fq params => if a = g s.1 then some () else none)).outcome (some ()) =
      generalizeBLeftOperatorAtPolynomial params strategy g
        ({ base := s.1, direction := s.2 }, s.1) := by
  classical
  simp [axisParallelLineAnswerFamily, axisParallelLineAnswerFamilyOf,
    generalizeBLeftOperatorAtPolynomial, generalizeBLeftEventSubMeasAtPolynomial,
    axisParallelLineQuestionParameter, subCoord, zeroCoord, postprocess,
    Finset.sum_filter, Finset.sum_comm, eq_comm]

/-- The symmetric `2ε` approximation interface for the point-line event.

This is the orientation used in `expansion.tex`, lines 306--307 and 309--310:
the line event is placed on the left register and the point event on the right
register.  It is obtained from `axisParallelBaseEventConsistency` by first
swapping the two prover roles using the symmetric strategy state, then applying
`prop:simeq-to-approx`. -/
lemma axisParallelBaseEventApproximation_swapped
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (g : Polynomial params) :
    SDDRel strategy.state (uniformDistribution (AxisParallelTestSample params))
      (IdxSubMeas.liftLeft
        (fun s : AxisParallelTestSample params =>
          postprocess (axisParallelLineAnswerFamily strategy s)
            (fun a : Fq params => if a = g s.1 then some () else none)))
      (IdxSubMeas.liftRight
        (fun s : AxisParallelTestSample params =>
          pointConditionedEventSubMeasAtPolynomial params strategy g s.1))
      (2 * eps) := by
  let pointMeas := axisParallelBasePointEventMeasurement params strategy g
  let lineMeas := axisParallelBaseLineEventMeasurement params strategy g
  have hcons :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas pointMeas) (IdxMeas.toIdxSubMeas lineMeas) eps := by
    change ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
      (fun s : AxisParallelTestSample params =>
        pointConditionedEventSubMeasAtPolynomial params strategy g s.1)
      (fun s : AxisParallelTestSample params =>
        postprocess (axisParallelLineAnswerFamily strategy s)
          (fun a : Fq params => if a = g s.1 then some () else none))
      eps
    exact axisParallelBaseEventConsistency params strategy eps delta gamma hgood g
  have hcons_swapped :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas lineMeas)
        (IdxMeas.toIdxSubMeas pointMeas) eps :=
    MIPStarRE.LDT.consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (AxisParallelTestSample params))
      (IdxMeas.toIdxSubMeas pointMeas) (IdxMeas.toIdxSubMeas lineMeas) eps hcons
  have happrox :
      BipartiteSDDRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas lineMeas)
        (IdxMeas.toIdxSubMeas pointMeas) (2 * eps) :=
    simeqToApprox strategy.state (uniformDistribution (AxisParallelTestSample params))
      lineMeas pointMeas eps hcons_swapped
  refine ⟨?_⟩
  change sddError strategy.state (uniformDistribution (AxisParallelTestSample params))
    (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas))
    (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) ≤ 2 * eps
  exact happrox.leftRightSquaredDistanceBound

/-- The selected, square-root weighted point-line approximation on the native
axis-parallel base-point sample distribution.

After `prop:cab-approx-delta` with multiplier `I ⊗ (G_g)^{1/2}`, the swapped
base-event approximation gives the paper's line-306 to line-307 move at a
sample `(u,i)`: the line question is represented by the rebased line with base
`u` and direction `i`. -/
lemma axisParallelBaseEventApproximation_weighted_sample
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (uniformDistribution (AxisParallelTestSample params))
      (fun s =>
        let qu : AxisParallelLineQuestion params :=
          ({ base := s.1, direction := s.2 }, s.1)
        let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
        ev strategy.state (Dᴴ * D)) ≤
      2 * eps := by
  classical
  let pointEvent : IdxSubMeas (AxisParallelTestSample params) (Option Unit) ι :=
    fun s => pointConditionedEventSubMeasAtPolynomial params strategy g s.1
  let lineEvent : IdxSubMeas (AxisParallelTestSample params) (Option Unit) ι :=
    fun s => postprocess (axisParallelLineAnswerFamily strategy s)
      (fun a : Fq params => if a = g s.1 then some () else none)
  let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
  let R : MIPStarRE.Quantum.Op (ι × ι) := rightTensor (ι₁ := ι) S
  let C : AxisParallelTestSample params → Unit → Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    fun _ _ _ => R
  have hbase := axisParallelBaseEventApproximation_swapped
    params strategy eps delta gamma hgood g
  have hbaseBound :
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          qSDDCore strategy.state
            (fun a : Option Unit => ((IdxSubMeas.liftLeft lineEvent) s).outcome a)
            (fun a : Option Unit => ((IdxSubMeas.liftRight pointEvent) s).outcome a)) ≤
        2 * eps := by
    simpa [sddError, qSDD, pointEvent, lineEvent] using hbase.squaredDistanceBound
  have hselected_le :
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          qSDDCore strategy.state
            (fun _ : Unit => ((IdxSubMeas.liftLeft lineEvent) s).outcome (some ()))
            (fun _ : Unit => ((IdxSubMeas.liftRight pointEvent) s).outcome (some ()))) ≤
        avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s =>
            qSDDCore strategy.state
              (fun a : Option Unit => ((IdxSubMeas.liftLeft lineEvent) s).outcome a)
              (fun a : Option Unit => ((IdxSubMeas.liftRight pointEvent) s).outcome a)) := by
    exact qSDDCore_optionUnit_some_le strategy.state
      (uniformDistribution (AxisParallelTestSample params))
      (fun s a => ((IdxSubMeas.liftLeft lineEvent) s).outcome a)
      (fun s a => ((IdxSubMeas.liftRight pointEvent) s).outcome a)
  have hAB :
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          qSDDCore strategy.state
            (fun _ : Unit => ((IdxSubMeas.liftLeft lineEvent) s).outcome (some ()))
            (fun _ : Unit => ((IdxSubMeas.liftRight pointEvent) s).outcome (some ()))) ≤
        2 * eps := le_trans hselected_le hbaseBound
  have hC : ∀ s a, ∑ b : Unit, (C s a b)ᴴ * C s a b ≤ 1 := by
    intro s a
    simpa [C, R, S] using rightPolynomialWeightSqrt_contraction
      (params := params) (G := G) (g := g)
  have hcab :=
    cabApproxDelta strategy.state (uniformDistribution (AxisParallelTestSample params))
      (fun s _ => ((IdxSubMeas.liftLeft lineEvent) s).outcome (some ()))
      (fun s _ => ((IdxSubMeas.liftRight pointEvent) s).outcome (some ()))
      C (2 * eps) hAB hC
  calc
    avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          let qu : AxisParallelLineQuestion params :=
            ({ base := s.1, direction := s.2 }, s.1)
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
          ev strategy.state (Dᴴ * D)) =
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          qSDDCore strategy.state
            (fun ab : Unit × Unit =>
              C s ab.1 ab.2 *
                ((IdxSubMeas.liftLeft lineEvent) s).outcome (some ()))
            (fun ab : Unit × Unit =>
              C s ab.1 ab.2 *
                ((IdxSubMeas.liftRight pointEvent) s).outcome (some ()))) := by
          apply avgOver_congr
          intro s
          simp only [qSDDCore, Fintype.sum_prod_type, Fintype.sum_unique]
          rw [show ((IdxSubMeas.liftLeft lineEvent) s).outcome (some ()) =
              leftTensor (ι₂ := ι)
                (generalizeBLeftOperatorAtPolynomial params strategy g
                  ({ base := s.1, direction := s.2 }, s.1)) by
                change leftTensor (ι₂ := ι)
                    ((postprocess (axisParallelLineAnswerFamily strategy s)
                      (fun a : Fq params => if a = g s.1 then some () else none)).outcome
                        (some ())) = _
                exact congrArg (leftTensor (ι₂ := ι))
                  (axisParallelBaseLineEvent_some params strategy g s)]
          rw [show ((IdxSubMeas.liftRight pointEvent) s).outcome (some ()) =
              rightTensor (ι₁ := ι)
                (pointConditionedOutcomeOperatorAtPolynomial params strategy g s.1) by
                simp [pointEvent, IdxSubMeas.liftRight]]
          simp only [C, R, S, weightedGeneralizeBLeftOperatorAtPolynomial,
            weightedPointConditionedRightOperatorAtPolynomial,
            rightTensor_mul_leftTensor_eq_opTensor, rightTensor_mul_rightTensor]
    _ ≤ 2 * eps := hcab

/-- Rebasing an incident axis-parallel line question at its sampled point does
not change the evaluated line event operator.

The left operator is the event `f(t)=g(ℓ(t))` for the line measurement on `ℓ`.
After rebasing `ℓ` at `t`, the sampled point is the new base point and the same
event is read as `f(0)=g(ℓ(t))`.  This is exactly the strategy's axis-parallel
measurement covariance, via `AxisParallelCovariantMeasurement.reparamInvariant`,
and is the operator-level reindexing used in `expansion.tex:300-307`. -/
lemma generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    generalizeBLeftOperatorAtPolynomial params strategy g (ℓ, ℓ.pointAt t) =
      generalizeBLeftOperatorAtPolynomial params strategy g
        (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) := by
  unfold generalizeBLeftOperatorAtPolynomial generalizeBLeftEventSubMeasAtPolynomial
  rw [axisParallelLineQuestionParameter_pointAt]
  have hparam_rebase :
      axisParallelLineQuestionParameter
        (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) = zeroCoord := by
    simp [axisParallelLineQuestionParameter, AxisParallelLine.rebaseAt, AxisParallelLine.pointAt,
      subCoord, zeroCoord]
  rw [hparam_rebase]
  have h := AxisParallelCovariantMeasurement.reparamInvariant strategy.axisParallelMeasurement
      ℓ t (g (ℓ.pointAt t))
  simp only [postprocess, ite_eq_left_iff, reduceCtorEq, imp_false, not_not] at h ⊢
  convert h.symm

/-- Weighted version of
`generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt`.

Tensoring the line event with the fixed polynomial weight `(G_g)^{1/2}` preserves
the rebasing equality.  This is the exact weighted operator identity needed to
transport the `2ε` base-point estimate to arbitrary incident line questions in
steps 2 and 5 of `lem:local-variance-of-points`. -/
lemma weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g (ℓ, ℓ.pointAt t) =
      weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
        (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) := by
  simp [weightedGeneralizeBLeftOperatorAtPolynomial,
    generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt]

/-- The weighted line-to-point approximation after reindexing the base-point test
sample to an arbitrary incident line question.

This is the paper's step 5 (`expansion.tex`, line 309--310), before coupling the
line question with the second endpoint of the hypercube-edge presentation: for
`v ∈ ℓ`, `B^ℓ_[f(v)=g(v)] ⊗ (G_g)^{1/2}` is `2ε`-close to
`I ⊗ (G_g)^{1/2} A^v_{g(v)}`. -/
lemma axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
        ev strategy.state (Dᴴ * D)) ≤
      2 * eps := by
  let F : AxisParallelTestSample params → Error := fun s =>
    let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
    let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
      weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
    ev strategy.state (Dᴴ * D)
  calc
    avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          ev strategy.state (Dᴴ * D))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu => F (qu.2, qu.1.direction)) := by
          apply MIPStarRE.LDT.avgOver_congr_on_support
          intro qu hqu
          have hline : pointOnLine (params := params) qu := by
            simpa [axisParallelLineQuestionDistribution] using hqu
          rcases qu with ⟨ℓ, u⟩
          rcases hline with ⟨t, ht⟩
          change ℓ.pointAt t = u at ht
          symm at ht
          subst u
          dsimp [F]
          rw [weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt]
          simp [AxisParallelLine.rebaseAt]
    _ = avgOver (uniformDistribution (AxisParallelTestSample params)) F :=
        avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample params F
    _ ≤ 2 * eps := axisParallelBaseEventApproximation_weighted_sample
      params strategy eps delta gamma hgood G g

/-- The reverse weighted point-to-line approximation after incident-line
reindexing.

This is the paper's step 2 (`expansion.tex`, line 306--307):
`I ⊗ (G_g)^{1/2} A^u_{g(u)}` is `2ε`-close to
`B^ℓ_[f(u)=g(u)] ⊗ (G_g)^{1/2}` for an incident line question `(ℓ,u)`. -/
lemma axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
          weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
        ev strategy.state (Dᴴ * D)) ≤
      2 * eps := by
  calc
    avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev strategy.state (Dᴴ * D))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu =>
            let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
            ev strategy.state (Dᴴ * D)) := by
          apply avgOver_congr
          intro qu
          exact ev_adjoint_sub_swap strategy.state
            (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
            (weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2)
    _ ≤ 2 * eps := axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
      params strategy eps delta gamma hgood G g

end

end MIPStarRE.LDT.GlobalVariance

end LIDT


