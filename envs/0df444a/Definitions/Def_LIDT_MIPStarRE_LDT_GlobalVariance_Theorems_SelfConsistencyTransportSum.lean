-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:07:01.074514+00:00
-- url     : https://prove2.me/theorems/7ff7caf1-7682-44de-8819-ff56ec97b0fa
-- title:
--   LIDT definitions: LDT / GlobalVariance / Theorems / SelfConsistencyTransportSum
-- statement:
--   This bundle gives sum-level self-consistency transport for the axis-parallel point-line test. It defines the point and line answer measurements, identifies their lifted outcomes with the expected tensor placements, and records both orientations of the weighted approximation chain.
--
--   Principal definitions:
--   - `axisParallelPointAnswerMeasurement`: the point-answer measurement for the axis-parallel test.
--   - `axisParallelLineAnswerMeasurement`: the line-answer measurement.
--   - `liftLeft_lineAnswerMeasurement_outcome_at_g`: identifies a lifted line outcome with the left operator.
--   - `liftRight_pointAnswerMeasurement_outcome_at_g`: identifies a lifted point outcome with the right point-conditioned operator.
--   - `axisParallelBaseEventApproximation_weighted_sample_sum`: the sum-level weighted base-event approximation.
--   - `axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum`: the line-to-point weighted approximation sum.
--   - `axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum`: the reverse point-to-line weighted approximation sum.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransportSum.lean#L31-L330

-- Generated from MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransportSum.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
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

/-! ## Sum-form (cardinality-free) `2ε` axis-parallel consistency endpoints

The lemmas below are the polynomial-sum (i.e. unnormalized `∑_g`) analogues of
the per-`g` `2ε` endpoints above.  They keep the answer space at `Fq params`
rather than postprocessing to the per-`g` `Option Unit` event, then group
polynomials by the common value `g(u)` via the `cabApproxDelta` multiplier
`if a = g s.1 then rightTensor (G_g)^{1/2} else 0`.  Combined with the
submeasurement contraction `∑_{g : g(u) = a} G_g ≤ I` from
`rightPolynomialWeightSqrt_grouped_contraction`, this gives `2ε` for the full
polynomial sum, with no polynomial-cardinality loss.  These are the steps 2 and
5 sum-level inputs to `eq:equivalent-local-variance`
(`references/ldt-paper/expansion.tex:317--321`).
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section

private noncomputable def axisParallelPointAnswerMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s => (axisParallelPointAnswerFamily strategy s).toMeasurement (by
    unfold axisParallelPointAnswerFamily
    exact (strategy.pointMeasurement s.1).total_eq_one)

private noncomputable def axisParallelLineAnswerMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s => (axisParallelLineAnswerFamily strategy s).toMeasurement (by
    unfold axisParallelLineAnswerFamily
    rw [postprocess_total]
    exact (strategy.axisParallelMeasurement
      { base := s.1, direction := s.2 }).total_eq_one)

/-- The lifted line-answer family outcome at value `a = g(s.1)` reduces to the
left-tensor of the `lem:generalize-b` left operator at the incident question
`(ℓ, s.1)` with `ℓ = {base := s.1, direction := s.2}`.

This is the operator identity bridging the un-postprocessed `Fq params`-valued
line answer family to the per-`g` line operator used in
`weightedGeneralizeBLeftOperatorAtPolynomial`.  The two sides differ only by
rewriting `axisParallelLineQuestionParameter` at the diagonal sample point. -/
private lemma liftLeft_lineAnswerMeasurement_outcome_at_g
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (s : AxisParallelTestSample params) :
    ((IdxSubMeas.liftLeft
        (IdxMeas.toIdxSubMeas (axisParallelLineAnswerMeasurement params strategy))) s).outcome
        (g s.1) =
      leftTensor (ι₂ := ι)
        (generalizeBLeftOperatorAtPolynomial params strategy g
          ({ base := s.1, direction := s.2 }, s.1)) := by
  classical
  simp only [IdxSubMeas.liftLeft, IdxMeas.toIdxSubMeas,
    axisParallelLineAnswerMeasurement, axisParallelLineAnswerFamily,
    axisParallelLineAnswerFamilyOf,
    generalizeBLeftOperatorAtPolynomial, generalizeBLeftEventSubMeasAtPolynomial,
    axisParallelLineQuestionParameter,
    SubMeas.toMeasurement_toSubMeas, mkLeftPlacedSubMeas_outcome, postprocess]
  congr 1
  congr 1
  apply Finset.ext
  intro a
  have hzero : subCoord (s.1 s.2) (s.1 s.2) = zeroCoord := by
    simp [subCoord, zeroCoord]
  simp only [hzero]
  simp

/-- The lifted point-answer family outcome at value `a = g(s.1)` reduces to the
right-tensor of the `point-conditioned` operator at base point `s.1`. -/
private lemma liftRight_pointAnswerMeasurement_outcome_at_g
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (s : AxisParallelTestSample params) :
    ((IdxSubMeas.liftRight
        (IdxMeas.toIdxSubMeas (axisParallelPointAnswerMeasurement params strategy))) s).outcome
        (g s.1) =
      rightTensor (ι₁ := ι)
        (pointConditionedOutcomeOperatorAtPolynomial params strategy g s.1) := by
  simp [IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas,
    axisParallelPointAnswerMeasurement, axisParallelPointAnswerFamily,
    pointConditionedOutcomeOperatorAtPolynomial,
    SubMeas.toMeasurement_toSubMeas, mkRightPlacedSubMeas_outcome]

/-- Sum-level base-sample form of the `2ε` axis-parallel consistency move,
oriented with the line event on the left register and the point event on the
right register.

This is the polynomial-sum version of
`axisParallelBaseEventApproximation_weighted_sample`: instead of fixing `g`
and postprocessing both sides to the `Option Unit` event `a = g(u)`, we keep
the full `Fq params` answer space and use the multiplier
`C s a g := if a = g s.1 then rightTensor (G_g)^{1/2} else 0` inside
`prop:cab-approx-delta`.  The contraction
`∀ s a, ∑_g (C s a g)ᴴ * (C s a g) ≤ I` is supplied by
`rightPolynomialWeightSqrt_grouped_contraction`, which uses the submeasurement
inequality `∑_{g : g(s.1) = a} G_g ≤ I`.  Consequently the bound is `2ε` for
the polynomial sum, with no polynomial-cardinality loss. -/
lemma axisParallelBaseEventApproximation_weighted_sample_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          let qu : AxisParallelLineQuestion params :=
            ({ base := s.1, direction := s.2 }, s.1)
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
          ev strategy.state (Dᴴ * D))) ≤
      2 * eps := by
  classical
  let pointMeas : IdxMeas (AxisParallelTestSample params) (Fq params) ι :=
    axisParallelPointAnswerMeasurement params strategy
  let lineMeas : IdxMeas (AxisParallelTestSample params) (Fq params) ι :=
    axisParallelLineAnswerMeasurement params strategy
  have hcons :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas pointMeas) (IdxMeas.toIdxSubMeas lineMeas) eps :=
    by
      have haxis :
          ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
            (axisParallelPointAnswerFamily strategy)
            (axisParallelLineAnswerFamily strategy) eps := by
        refine ⟨?_⟩
        simpa [SymStrat.axisParallelFailureProbability] using
          hgood.axisParallelTest
      change ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy) eps
      exact haxis
  have hcons_swapped :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas lineMeas) (IdxMeas.toIdxSubMeas pointMeas) eps :=
    MIPStarRE.LDT.consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (AxisParallelTestSample params))
      (IdxMeas.toIdxSubMeas pointMeas) (IdxMeas.toIdxSubMeas lineMeas) eps hcons
  have happrox :
      BipartiteSDDRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas lineMeas) (IdxMeas.toIdxSubMeas pointMeas) (2 * eps) :=
    simeqToApprox strategy.state (uniformDistribution (AxisParallelTestSample params))
      lineMeas pointMeas eps hcons_swapped
  have hbase :
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          qSDDCore strategy.state
            (fun a : Fq params =>
              ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome a)
            (fun a : Fq params =>
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome a)) ≤
        2 * eps := by
    simpa [sddError, qSDD] using happrox.leftRightSquaredDistanceBound
  simpa using
    cabApproxDelta_sum_from_sdd params strategy.state
      (uniformDistribution (AxisParallelTestSample params))
      (fun s => s.1)
      (fun s a => ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome a)
      (fun s a => ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome a)
      (fun s g =>
        let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
        weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
      (fun s g => weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1)
      G (2 * eps) hbase
      (by
        intro s g
        let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
        let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
        let L : MIPStarRE.Quantum.Op ι :=
          generalizeBLeftOperatorAtPolynomial params strategy g qu
        have hline_outcome :
            ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome (g s.1) =
              leftTensor (ι₂ := ι) L :=
          liftLeft_lineAnswerMeasurement_outcome_at_g params strategy g s
        change rightTensor (ι₁ := ι) S *
            ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome (g s.1) =
          weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
        rw [hline_outcome]
        change rightTensor (ι₁ := ι) S * leftTensor (ι₂ := ι) L = opTensor L S
        exact rightTensor_mul_leftTensor_eq_opTensor L S)
      (by
        intro s g
        let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
        let A : MIPStarRE.Quantum.Op ι :=
          pointConditionedOutcomeOperatorAtPolynomial params strategy g s.1
        have hpoint_outcome :
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome (g s.1) =
              rightTensor (ι₁ := ι) A :=
          liftRight_pointAnswerMeasurement_outcome_at_g params strategy g s
        change rightTensor (ι₁ := ι) S *
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome (g s.1) =
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
        rw [hpoint_outcome]
        change rightTensor (ι₁ := ι) S * rightTensor (ι₁ := ι) A =
          rightTensor (ι₁ := ι) (S * A)
        exact rightTensor_mul_rightTensor S A)

/-- Sum-level form of the weighted line-to-point approximation
(`expansion.tex:309--310`, paper step 5) on the
`axisParallelLineQuestionDistribution` distribution.

This is the polynomial-sum analogue of
`axisParallelPointLineConsistency_weighted_leftToRightLineQuestion`.  After
reindexing the line-question sampling along its incident-pair structure (using
the existing rebasing covariance for the line operator), it reduces to the
sum-level base-sample bound `axisParallelBaseEventApproximation_weighted_sample_sum`. -/
lemma axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          ev strategy.state (Dᴴ * D))) ≤
      2 * eps := by
  classical
  let F : Polynomial params → AxisParallelTestSample params → Error := fun g s =>
    let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
    let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
      weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
    ev strategy.state (Dᴴ * D)
  calc
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          ev strategy.state (Dᴴ * D)))
      = ∑ g : Polynomial params,
          avgOver (axisParallelLineQuestionDistribution params)
            (fun qu => F g (qu.2, qu.1.direction)) := by
          refine Finset.sum_congr rfl ?_
          intro g _
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
          have hrebase :
              weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (ℓ, ℓ.pointAt t) =
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) :=
            weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt
              params strategy G g ℓ t
          rw [hrebase]
          simp [AxisParallelLine.rebaseAt]
    _ = ∑ g : Polynomial params,
          avgOver (uniformDistribution (AxisParallelTestSample params)) (F g) := by
          refine Finset.sum_congr rfl ?_
          intro g _
          exact avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
            params (F g)
    _ ≤ 2 * eps :=
        axisParallelBaseEventApproximation_weighted_sample_sum
          params strategy eps delta gamma hgood G

/-- Sum-level form of the reverse weighted point-to-line approximation
(`expansion.tex:306--307`, paper step 2) on the
`axisParallelLineQuestionDistribution` distribution.

This is the polynomial-sum analogue of
`axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion`.  Each
summand is unchanged after swapping the two endpoint operators, so this reduces
to `axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum`. -/
lemma axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev strategy.state (Dᴴ * D))) ≤
      2 * eps := by
  calc
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev strategy.state (Dᴴ * D)))
      = ∑ g : Polynomial params,
          avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl ?_
          intro g _
          apply avgOver_congr
          intro qu
          exact ev_adjoint_sub_swap strategy.state
            (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
            (weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2)
    _ ≤ 2 * eps :=
        axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
          params strategy eps delta gamma hgood G

end

end MIPStarRE.LDT.GlobalVariance

end LIDT


