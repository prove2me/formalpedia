-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:19:28.114881+00:00
-- url     : https://prove2.me/theorems/8c488e7f-63cc-46fc-8cc9-3a83924afdc8
-- title:
--   LIDT definitions: LDT / SelfImprovement / Theorems / Results / SdpMatrixBridge
-- statement:
--   This bundle bridges the abstract self-improvement SDP and its concrete matrix realization for a strategy. It constructs the point-measurement matrix data, identifies the averaged and slack operators, and converts saturated or strong-duality witnesses into abstract slackness statements.
--
--   Principal definitions:
--   - `matrixSdpPointRealizationOfStrategy`: the matrix SDP realization of a strategy's point measurements.
--   - `matrixAveragedPointOperator_ofPointRealization`: identifies its averaged point operator.
--   - `matrixSdpDualSlackOperator_ofPointRealization`: identifies its matrix dual slack.
--   - `MatrixSdpCanonicalOptimalPair`: records canonical primal-dual data with slackness.
--   - `ofFeasibleStrongDualitySaturateSlackBlock`: completes a feasible pair to a saturated canonical pair.
--   - `toMatrixSdpStatementWithSlackness`: extracts the matrix-level slackness statement.
--   - `toSdpOptimalPairWithSlackness`: converts a matrix optimal witness to an abstract SDP pair.
--   - `toSdpStatementWithSlackness`: derives the abstract slackness statement from matrix strong duality.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean#L46-L298

-- Generated from MIPStarRE/LDT/SelfImprovement/Theorems/Results/SdpMatrixBridge.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_NaimarkCore
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Matrix SDP comparison

This file compares the concrete matrix-level SDP slackness interface with the
abstract self-improvement SDP statement interface.

The comparison is intentionally split into two interfaces.  The source-shaped
matrix optimal witness supplies dual feasibility, complementary slackness, and
the saturated canonical slack block needed for the abstract Section 9 statement.
No auxiliary dominance bound `I ≤ Z` is part of this comparison theorem.

Mathlib provides the underlying finite-dimensional matrix order and convex-cone
infrastructure used throughout this project, but it does not yet provide a
ready-made finite-dimensional semidefinite-programming strong-duality theorem
with complementary slackness in the shape needed here.  Consequently this file
does not reprove SDP duality.  It only transports the project-local matrix
witness `MatrixSdpStatementWithSlackness` to the abstract Section 9 interface.
If a Mathlib SDP theorem is later available, its output should replace the
project-local witness while the comparison theorem below should remain the
comparison with the self-improvement notation.

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

/-- The point-measurement part of the matrix SDP realization associated to a strategy.

The present comparison only uses the point-measurement fields of
`MatrixSdpRealization`, through `matrixAveragedPointOperator` and
`matrixSdpDualSlackOperator`.  The state field is therefore filled by the zero
positive operator.  This construction should not be used for state-dependent
matrix expressions such as `matrixExpectation`; such expressions would compute
with the zero operator rather than with `strategy.state`. -/
noncomputable def matrixSdpPointRealizationOfStrategy (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) : MatrixSdpRealization params where
  space := {
    carrier := ι
    instFintype := inferInstance
    instDecidableEq := inferInstance
    instNonempty := ⟨(Classical.choice strategy.isNormalized.nonempty).1⟩
  }
  state := {
    matrix := 0
    positive := le_rfl
  }
  pointMeasurement := fun u => {
    effect := fun a => (strategy.pointMeasurement u).toSubMeas.outcome a
    pos := fun a => (strategy.pointMeasurement u).toSubMeas.outcome_pos a
    sum_le_one := le_of_eq ((strategy.pointMeasurement u).toSubMeas.sum_eq_total.trans
      (strategy.pointMeasurement u).total_eq_one)
  }

/-- The averaged point operator for the point-measurement matrix realization is
the abstract averaged point operator. -/
theorem matrixAveragedPointOperator_ofPointRealization (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) (g : Polynomial params) :
    matrixAveragedPointOperator params
        (matrixSdpPointRealizationOfStrategy params strategy) g =
      averagedPointOperator params strategy g := by
  unfold matrixAveragedPointOperator averagedPointOperator
  refine averageOperatorOverDistribution_congr _ _ _ ?_
  intro u
  simp [matrixAveragedPointOperatorContribution,
    pointConditionedOutcomeOperatorAtPolynomial, matrixSdpPointRealizationOfStrategy]

/-- The matrix dual slack operator for the point-measurement matrix realization
is the abstract dual slack operator. -/
theorem matrixSdpDualSlackOperator_ofPointRealization (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Z : MIPStarRE.Quantum.Op ι) (g : Polynomial params) :
    matrixSdpDualSlackOperator params
        (matrixSdpPointRealizationOfStrategy params strategy) Z g =
      sdpDualSlackOperator params strategy Z g := by
  unfold matrixSdpDualSlackOperator sdpDualSlackOperator
  rw [matrixAveragedPointOperator_ofPointRealization]
  rfl

/-- Canonical primal-dual data with complementary slackness and zero slack
block.

This is the paper-faithful canonical output still required from the
strong-duality argument in `lem:sdp`: a feasible canonical primal matrix, a
dual-feasible operator with the same objective value, canonical complementary
slackness, and vanishing of the extra slack block \(X_{\mathrm{none},\mathrm{none}}\).
The dominance condition \(I \le Z\) is not part of this structure. -/
structure MatrixSdpCanonicalOptimalPair
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (Z : MatrixOperator model.space) : Prop where
  feasible : MatrixSdpCanonicalPrimalFeasible params model X
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g
  strongDuality :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) =
      matrixSdpDualObjective model Z
  complementarySlackness :
    X * (matrixSdpCanonicalDualOperator params model Z -
          matrixSdpCanonicalObjectiveOperator params model) =
      0
  slackBlock_eq_zero :
    matrixSdpCanonicalDiagonalBlock params model X none = 0

namespace MatrixSdpCanonicalOptimalPair

/-- Build a saturated canonical optimal pair by completing the primal slack
block at `sdpDistinguishedPolynomial params`.

Paper origin: `references/ldt-paper/self_improvement.tex:177-190`.  This is the
source-faithful strong-duality slice: from a feasible canonical primal matrix,
dual feasibility, and primal-dual objective equality, first move the `none`
slack block into the distinguished polynomial block.  The saturated matrix is
still feasible, has zero `none` block, and keeps objective equality by objective
monotonicity plus canonical weak duality.  No auxiliary dominance hypothesis
`I ≤ Z` is used. -/
theorem ofFeasibleStrongDualitySaturateSlackBlock
    {params : Parameters}
    [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {Z : MatrixOperator model.space}
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) =
        matrixSdpDualObjective model Z) :
    MatrixSdpCanonicalOptimalPair params model
      (matrixSdpCanonicalSaturateSlackBlockMatrix params model X) Z := by
  let Xsat := matrixSdpCanonicalSaturateSlackBlockMatrix params model X
  have hXsat : MatrixSdpCanonicalPrimalFeasible params model Xsat :=
    matrixSdpCanonicalSaturateSlackBlockMatrix_feasible params model X hX
  have hstrongSat :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * Xsat)) =
        matrixSdpDualObjective model Z :=
    matrixSdpCanonicalSaturateSlackBlockMatrix_strongDuality
      params model X hX Z hdual hstrong
  exact {
    feasible := hXsat
    dualFeasible := hdual
    strongDuality := hstrongSat
    complementarySlackness :=
      matrixSdpCanonicalComplementarySlackness_of_strongDuality
        params model Xsat hXsat Z hdual hstrongSat
    slackBlock_eq_zero :=
      matrixSdpCanonicalDiagonalBlock_saturateSlackBlockMatrix_none params model X }

/-- A saturated canonical optimal pair gives the matrix-level slackness
statement without adding the auxiliary dominance condition. -/
theorem toMatrixSdpStatementWithSlackness
    {params : Parameters}
    [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpCanonicalOptimalPair params model X Z) :
    MatrixSdpStatementWithSlackness params model :=
  matrixSdpStatementWithSlackness_of_canonicalFeasibleSaturatedComplementarySlackness
    params model X h.feasible Z h.dualFeasible h.strongDuality
    h.complementarySlackness h.slackBlock_eq_zero

end MatrixSdpCanonicalOptimalPair

namespace MatrixSdpOptimalWitness

/-- A matrix optimal witness gives the abstract slackness-carrying SDP pair. -/
theorem toSdpOptimalPairWithSlackness
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params)
      (matrixSdpPointRealizationOfStrategy params strategy).space}
    {Z : MIPStarRE.Quantum.Op ι}
    (h : MatrixSdpOptimalWitness params
      (matrixSdpPointRealizationOfStrategy params strategy) T Z) :
    SdpOptimalPairWithSlackness params strategy (MatrixSubmeasurement.toSubMeas T) Z := by
  have hSlack :
      ∀ g : Polynomial params,
        sdpComplementarySlacknessEquation params strategy
          (MatrixSubmeasurement.toSubMeas T) Z g := by
    intro g
    dsimp [MatrixSubmeasurement.toSubMeas, sdpComplementarySlacknessEquation,
      sdpDualSlackOperator, matrixSdpPointRealizationOfStrategy]
    rw [← matrixAveragedPointOperator_ofPointRealization params strategy g]
    exact h.complementarySlacknessEquation g
  exact {
    toSdpOptimalPair := {
      primalTotalOperator := h.primalTotalEqOne
      dualFeasible := fun g =>
        (matrixSdpDualSlackOperator_ofPointRealization params strategy Z g).symm ▸ h.dualFeasible g
    }
    complementarySlackness := hSlack }

end MatrixSdpOptimalWitness

namespace MatrixSdpStatementWithSlackness

/-- A matrix strong-duality statement for the point-measurement realization of
a strategy implies the abstract slackness statement. -/
theorem toSdpStatementWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (h : MatrixSdpStatementWithSlackness params
      (matrixSdpPointRealizationOfStrategy params strategy)) :
    SdpStatementWithSlackness params strategy := by
  obtain ⟨T, Z, hopt⟩ := h.witness
  exact ⟨MatrixMeasurement.toMeasurement T, Z, by
    simpa [MatrixMeasurement.toMeasurement] using hopt.toSdpOptimalPairWithSlackness⟩

end MatrixSdpStatementWithSlackness

/-- Canonical strong-duality and complementary-slackness construction for the
point-measurement realization of the Section 9 SDP.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--190
(`\label{lem:sdp}` and the proof using Slater's condition).  The paper first
rewrites the primal and dual SDPs in canonical block form, invokes strong
duality, and then applies complementary slackness to obtain a saturated
canonical optimal pair.

This is the source-faithful construction for the formalized SDP route.  Its
conclusion is the native canonical block-SDP output: a feasible canonical primal
matrix, a dual-feasible operator with equal objective value, canonical
complementary slackness, and a vanishing slack block.  It does not
assume the auxiliary dominance condition `I ≤ Z`; the saturated slack block is
part of the expected strong-duality output.  The matrix statement
`matrixSdpPointRealization_statementWithSlackness` follows by extracting the
diagonal polynomial blocks.

Tracked by issue #1230 and documented in
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`. -/
theorem matrixSdpPointRealization_canonicalOptimalPair
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params
        (matrixSdpPointRealizationOfStrategy params strategy)),
      ∃ Z : MIPStarRE.Quantum.Op ι,
        MatrixSdpCanonicalOptimalPair params
          (matrixSdpPointRealizationOfStrategy params strategy) X Z := by
  let model := matrixSdpPointRealizationOfStrategy params strategy
  obtain ⟨X, Z, hX, hdual, hstrong⟩ := matrixSdpCanonicalStrongDuality params model
  refine ⟨matrixSdpCanonicalSaturateSlackBlockMatrix params model X, Z, ?_⟩
  exact MatrixSdpCanonicalOptimalPair.ofFeasibleStrongDualitySaturateSlackBlock
    (params := params) (model := model) (X := X) (Z := Z) hX hdual hstrong

/-- Matrix-level strong-duality and complementary-slackness statement for the
point-measurement realization of the Section 9 SDP.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--190
(`\label{lem:sdp}`), documented by
`docs/paper-gaps/issue-1230-self-improvement-sdp-usage.tex`.

**Source-faithful transport:** This declaration is a proved extraction from the
canonical optimal-pair construction for `lem:sdp`; it is not a conditional
replacement for the SDP strong-duality theorem.

This theorem is a proved transport from the native canonical optimal-pair
construction `matrixSdpPointRealization_canonicalOptimalPair`.  It contains no
additional dominance, bridge, residual, or package hypothesis. -/
theorem matrixSdpPointRealization_statementWithSlackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    MatrixSdpStatementWithSlackness params
      (matrixSdpPointRealizationOfStrategy params strategy) := by
  rcases matrixSdpPointRealization_canonicalOptimalPair params strategy with
    ⟨X, Z, hpair⟩
  exact hpair.toMatrixSdpStatementWithSlackness

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


