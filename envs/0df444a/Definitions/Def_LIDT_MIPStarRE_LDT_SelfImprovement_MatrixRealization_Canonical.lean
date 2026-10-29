-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:09:52.634106+00:00
-- url     : https://prove2.me/theorems/61e83a65-9d0c-4e10-beb7-be2f33351aa4
-- title:
--   LIDT definitions: LDT / SelfImprovement / MatrixRealization / Canonical
-- statement:
--   This bundle defines the canonical block-matrix realization of the self-improvement SDP. It packages the objective and dual operators, the dual slack, explicit feasible bounds, and the complementary-slackness defect for the canonical primal and dual data.
--
--   Principal definitions:
--   - `matrixSdpCanonicalObjectiveBlockFamily`: the block family for the canonical objective matrix.
--   - `matrixSdpCanonicalObjectiveOperator`: the canonical objective operator.
--   - `matrixSdpCanonicalDualOperatorBlockFamily`: the block family for a canonical dual operator.
--   - `matrixSdpCanonicalDualOperator`: the canonical dual operator.
--   - `matrixSdpCanonicalDualSlackBlockFamily`: the block family for the dual slack.
--   - `matrixSdpCanonicalDualOperator_sub_objectiveOperator`: identifies the dual slack as dual minus objective.
--   - `MatrixSdpCanonicalFeasibleBounds`: records the canonical feasible bounds.
--   - `matrixSdpComplementarySlacknessDefect`: defines the concrete complementary-slackness defect.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical.lean#L29-L780

-- Generated from MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 9 — Canonical matrix SDP dual and slackness layer

This module contains the canonical objective and dual operators, the dual slack
block identities, and the slack-block saturation step used to extract the
paper-form primal normalization.  The optimal-witness packages built from these
canonical facts live in `MatrixRealization/Canonical/Witness.lean`.

## References

- `references/ldt-paper/self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

/-- The canonical objective matrix `C = diag(A_g, 0)` in the paper's block SDP. -/
noncomputable def matrixSdpCanonicalObjectiveBlockFamily (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space
  | none => 0
  | some g => matrixAveragedPointOperator params model g

/-- The canonical objective operator of the block SDP. -/
noncomputable def matrixSdpCanonicalObjectiveOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  matrixSdpCanonicalBlockDiagonal params model
    (matrixSdpCanonicalObjectiveBlockFamily params model)

@[simp] theorem matrixSdpCanonicalObjectiveBlockFamily_none (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalObjectiveBlockFamily params model none = 0 :=
  rfl

@[simp] theorem matrixSdpCanonicalObjectiveBlockFamily_some (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    matrixSdpCanonicalObjectiveBlockFamily params model (some g) =
      matrixAveragedPointOperator params model g :=
  rfl

@[simp] theorem matrixSdpCanonicalDiagonalBlock_objectiveOperator_none
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalObjectiveOperator params model) none =
      0 := by
  simp [matrixSdpCanonicalObjectiveOperator]

@[simp] theorem matrixSdpCanonicalDiagonalBlock_objectiveOperator_some
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalObjectiveOperator params model) (some g) =
      matrixAveragedPointOperator params model g := by
  simp [matrixSdpCanonicalObjectiveOperator]

/-- The block family representing the canonical dual operator associated to a
paper dual variable `Z`.

In the paper calculation this is
`∑_{i,j} z_{ij} D_{ij}`, which is the block-diagonal matrix with the same
operator `Z` on every canonical block. -/
noncomputable def matrixSdpCanonicalDualOperatorBlockFamily (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space :=
  fun _ => Z

/-- The canonical dual operator corresponding to a paper dual variable `Z`. -/
noncomputable def matrixSdpCanonicalDualOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  matrixSdpCanonicalBlockDiagonal params model
    (matrixSdpCanonicalDualOperatorBlockFamily params model Z)

@[simp] theorem matrixSdpCanonicalDualOperatorBlockFamily_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDualOperatorBlockFamily params model Z b = Z :=
  rfl

@[simp] theorem matrixSdpCanonicalDiagonalBlock_dualOperator
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalDualOperator params model Z) b =
      Z := by
  simp [matrixSdpCanonicalDualOperator]

/-- The block family for the canonical dual slack operator.

It has polynomial blocks `Z - A_g` and slack block `Z`, exactly as in the
canonical dual constraint obtained from the paper SDP. -/
noncomputable def matrixSdpCanonicalDualSlackBlockFamily (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space
  | none => Z
  | some g => matrixSdpDualSlackOperator params model Z g

@[simp] theorem matrixSdpCanonicalDualSlackBlockFamily_none (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    matrixSdpCanonicalDualSlackBlockFamily params model Z none = Z :=
  rfl

@[simp] theorem matrixSdpCanonicalDualSlackBlockFamily_some (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) :
    matrixSdpCanonicalDualSlackBlockFamily params model Z (some g) =
      matrixSdpDualSlackOperator params model Z g :=
  rfl

/-- The canonical dual slack is the difference between the canonical dual
operator and the canonical objective operator. -/
theorem matrixSdpCanonicalDualOperator_sub_objectiveOperator
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model =
      matrixSdpCanonicalBlockDiagonal params model
        (matrixSdpCanonicalDualSlackBlockFamily params model Z) := by
  rw [matrixSdpCanonicalDualOperator, matrixSdpCanonicalObjectiveOperator,
    ← matrixSdpCanonicalBlockDiagonal_sub]
  congr
  funext b
  cases b with
  | none =>
      simp
  | some g =>
      simp [matrixSdpDualSlackOperator]

/-- The canonical dual slack block matrix is positive semidefinite under paper
dual feasibility.

The canonical dual constraint for the block SDP is the positivity of the block
diagonal operator with blocks `Z - A_g` on the polynomial summands and `Z` on
the slack summand.  The polynomial blocks are precisely the paper dual
feasibility inequalities, while the slack block follows from the same
inequalities because the averaged point operators are positive. -/
theorem matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_of_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ matrixSdpCanonicalBlockDiagonal params model
      (matrixSdpCanonicalDualSlackBlockFamily params model Z) := by
  refine matrixSdpCanonicalBlockDiagonal_nonneg params model
    (matrixSdpCanonicalDualSlackBlockFamily params model Z) ?_
  intro b
  cases b with
  | none =>
      simpa [matrixSdpCanonicalDualSlackBlockFamily] using
        matrixSdpDualPositive_of_dualFeasible params model Z hdual
  | some g =>
      simpa [matrixSdpCanonicalDualSlackBlockFamily] using hdual g

/-- Positivity of the canonical dual slack block matrix is equivalent to the
paper dual feasibility inequalities `Z ≥ A_g`. -/
theorem matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_iff_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    0 ≤ matrixSdpCanonicalBlockDiagonal params model
        (matrixSdpCanonicalDualSlackBlockFamily params model Z) ↔
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g := by
  constructor
  · intro hcanonical g
    have hblocks :=
      (matrixSdpCanonicalBlockDiagonal_nonneg_iff params model
        (matrixSdpCanonicalDualSlackBlockFamily params model Z)).mp hcanonical
    simpa using hblocks (some g)
  · exact matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_of_dualFeasible params model Z

/-- The canonical dual constraint for `Z` is equivalent to the paper dual
constraints `Z ≥ A_g`. -/
theorem matrixSdpCanonicalDualConstraint_nonneg_iff_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model ↔
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g := by
  rw [matrixSdpCanonicalDualOperator_sub_objectiveOperator]
  exact matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_iff_dualFeasible params model Z

/-- Paper dual feasibility implies feasibility of the canonical block dual
constraint. -/
theorem matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model :=
  (matrixSdpCanonicalDualConstraint_nonneg_iff_dualFeasible params model Z).mpr hdual

/-- Feasibility of the canonical block dual constraint recovers the paper dual
inequalities. -/
theorem matrixSdpDualFeasible_of_canonicalDualConstraint_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hcanonical :
      0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g :=
  (matrixSdpCanonicalDualConstraint_nonneg_iff_dualFeasible params model Z).mp hcanonical







/-- The canonical block matrix associated to the strict primal witness is
feasible for the canonical primal SDP. -/
theorem matrixSdpCanonicalStrictPrimalBlockMatrix_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalPrimalBlockMatrix params model
        (matrixSdpStrictPrimalSubmeasurement params model)) :=
  matrixSdpCanonicalPrimalBlockMatrix_feasible params model
    (matrixSdpStrictPrimalSubmeasurement params model)



/-- Canonical block-SDP feasible bounds supplied by the explicit paper
Slater-type witnesses.

This is not an optimality statement.  It records the primal canonical
feasibility of the uniform family, the strict slack block `(1/2)I`, the
canonical dual constraint for `Z = 2I`, and the corresponding paper dual
feasibility data. -/
structure MatrixSdpCanonicalFeasibleBounds (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) : Prop where
  primalFeasible :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalPrimalBlockMatrix params model
        (matrixSdpStrictPrimalSubmeasurement params model))
  primalSlackHalf :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpStrictPrimalSubmeasurement params model)) none =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space))
  canonicalDualFeasible :
    0 ≤ matrixSdpCanonicalDualOperator params model (matrixSdpStrictDualWitness model) -
        matrixSdpCanonicalObjectiveOperator params model
  paperDualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model (matrixSdpStrictDualWitness model) g
  paperDualSlackDominatesIdentity :
    ∀ g : Polynomial params,
      (1 : MatrixOperator model.space) ≤
        matrixSdpDualSlackOperator params model (matrixSdpStrictDualWitness model) g
  dualDominatesIdentity :
    (1 : MatrixOperator model.space) ≤ matrixSdpStrictDualWitness model
  canonicalDualSlackDominatesIdentity :
    (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) ≤
      matrixSdpCanonicalDualOperator params model (matrixSdpStrictDualWitness model) -
        matrixSdpCanonicalObjectiveOperator params model







/-- The canonical block objective evaluated on an arbitrary feasible canonical
primal matrix is the paper primal objective of its extracted submeasurement.

This is the converse objective identity to
`matrixSdpCanonicalObjective_trace_primalBlockMatrix`: once a canonical feasible
matrix `X` is given, reading the polynomial diagonal blocks as `T_g = X_{gg}`
preserves the SDP objective value. -/
theorem matrixSdpCanonicalObjective_trace_extractedPrimalSubmeasurement
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) =
      matrixSdpPrimalObjective params model
        (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) := by
  rw [matrixSdpCanonicalObjectiveOperator]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul_left]
  rw [Fintype.sum_option]
  simp only [matrixSdpCanonicalObjectiveBlockFamily_none, zero_mul, Matrix.trace_zero,
    matrixSdpCanonicalObjectiveBlockFamily_some, zero_add, Complex.re_sum]
  unfold matrixSdpPrimalObjective matrixSdpPrimalContributionOperator
  rw [Matrix.trace_sum]
  simp only [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [matrixSdpCanonicalExtractedPrimalSubmeasurement_effect]
  rw [Matrix.trace_mul_comm]



/-- Pairing the canonical dual operator with a feasible canonical primal
matrix gives the paper dual objective.

The canonical equality constraint says that the sum of the diagonal blocks of
`X` is the identity.  Since the canonical dual operator has the same block `Z`
on every summand, the trace pairing collapses to `Tr Z`, exactly the paper
dual objective. -/
theorem matrixSdpCanonicalDualOperator_trace_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalDualOperator params model Z * X)) =
      matrixSdpDualObjective model Z := by
  have hconstraint :
      ∑ b : MatrixSdpCanonicalBlockIndex params,
          matrixSdpCanonicalDiagonalBlock params model X b =
        (1 : MatrixOperator model.space) := by
    simpa [matrixSdpCanonicalConstraintOperator] using hX.constraintEqOne
  rw [matrixSdpCanonicalDualOperator]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul_left]
  simp only [matrixSdpCanonicalDualOperatorBlockFamily_apply]
  rw [← Matrix.trace_sum]
  rw [← Finset.mul_sum]
  rw [hconstraint]
  simp [matrixSdpDualObjective]

/-- The canonical primal-dual gap is the trace pairing with the canonical dual
slack operator.

This is the algebraic identity behind weak duality for the canonical SDP: after
the dual trace pairing is identified with the paper dual objective, subtracting
the canonical objective leaves the trace pairing against `D(Z)-C`. -/
theorem matrixSdpCanonicalDualGap_trace
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space) :
    matrixSdpDualObjective model Z -
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) =
      Complex.re (Matrix.trace
        ((matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) * X)) := by
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  rw [matrixSdpCanonicalDualOperator_trace_feasible params model X hX Z]

/-- Canonical weak duality for the self-improvement SDP.

For a feasible canonical primal matrix \(X\) and a feasible canonical dual
operator \(D(Z)-C\), the primal-dual gap is the trace pairing of two positive
semidefinite operators.  The preceding trace identity and positivity of this
pairing give the usual weak-duality inequality. -/
theorem matrixSdpCanonicalWeakDuality
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hdual :
      0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
      matrixSdpDualObjective model Z := by
  rw [← sub_nonneg]
  rw [matrixSdpCanonicalDualGap_trace params model X hX Z]
  exact MIPStarRE.Quantum.trace_mul_nonneg_of_nonneg hdual hX.nonnegative

/-- Zero duality gap gives canonical complementary slackness.

This is the local algebraic consequence used after the Watrous strong-duality
theorem supplies an optimal feasible primal-dual pair with equal objective
values.  The remaining hard part is producing such a pair from Slater's
condition; once it is available, this theorem converts the zero gap into the
product equation `X * (D(Z) - C) = 0`. -/
theorem matrixSdpCanonicalComplementarySlackness_of_strongDuality
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g)
    (hstrong :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) =
        matrixSdpDualObjective model Z) :
    X * (matrixSdpCanonicalDualOperator params model Z -
          matrixSdpCanonicalObjectiveOperator params model) =
      0 := by
  let S := matrixSdpCanonicalDualOperator params model Z -
    matrixSdpCanonicalObjectiveOperator params model
  have hS : 0 ≤ S := by
    simpa [S] using
      matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model Z hdual
  have hgap_zero :
      matrixSdpDualObjective model Z -
          Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) =
        0 := by
    rw [hstrong, sub_self]
  have htrace_SX : Complex.re (Matrix.trace (S * X)) = 0 := by
    rw [← matrixSdpCanonicalDualGap_trace params model X hX Z]
    exact hgap_zero
  have htrace_XS : Complex.re (Matrix.trace (X * S)) = 0 := by
    rw [Matrix.trace_mul_comm X S]
    exact htrace_SX
  simpa [S] using
    MIPStarRE.Quantum.mul_eq_zero_of_nonneg_of_trace_mul_eq_zero
      hX.nonnegative hS htrace_XS

/-- The diagonal block of a canonical primal-dual slack product is the product
of the corresponding primal diagonal block and canonical dual slack block. -/
theorem matrixSdpCanonicalDiagonalBlock_mul_dualSlack
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (Z : MatrixOperator model.space)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (X * (matrixSdpCanonicalDualOperator params model Z -
          matrixSdpCanonicalObjectiveOperator params model)) b =
      matrixSdpCanonicalDiagonalBlock params model X b *
        matrixSdpCanonicalDualSlackBlockFamily params model Z b := by
  rw [matrixSdpCanonicalDualOperator_sub_objectiveOperator]
  exact matrixSdpCanonicalDiagonalBlock_mul_blockDiagonal_right params model X
    (matrixSdpCanonicalDualSlackBlockFamily params model Z) b

/-- The concrete complementary-slackness defect `T_g (Z - A_g)`. -/
noncomputable def matrixSdpComplementarySlacknessDefect (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  (T.effect g) * matrixSdpDualSlackOperator params model Z g

/-- Multiplying the canonical primal block matrix by the canonical dual slack
keeps only the blockwise products.

This is the formal block-diagonal calculation behind the paper's passage from
canonical complementary slackness to the equations
`T_g (Z - A_g) = 0`. -/
theorem matrixSdpCanonicalPrimalBlockMatrix_mul_dualSlack
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) :
    matrixSdpCanonicalPrimalBlockMatrix params model T *
        (matrixSdpCanonicalDualOperator params model Z -
          matrixSdpCanonicalObjectiveOperator params model) =
      matrixSdpCanonicalBlockDiagonal params model
        (fun b =>
          matrixSdpCanonicalPrimalBlockFamily params model T b *
            matrixSdpCanonicalDualSlackBlockFamily params model Z b) := by
  rw [matrixSdpCanonicalDualOperator_sub_objectiveOperator,
    matrixSdpCanonicalPrimalBlockMatrix,
    matrixSdpCanonicalBlockDiagonal_mul]

/-- If a feasible canonical primal matrix satisfies canonical complementary
slackness, then the block-diagonal matrix obtained from its polynomial diagonal
blocks also satisfies canonical complementary slackness.

This is the formal version of the reduction in the SDP proof which permits one
to replace an optimal canonical matrix by its block-diagonal part. -/
theorem matrixSdpCanonicalPrimalBlockMatrix_extracted_mul_dualSlack_of_canonical
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0) :
    matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) *
        (matrixSdpCanonicalDualOperator params model Z -
          matrixSdpCanonicalObjectiveOperator params model) =
      0 := by
  rw [matrixSdpCanonicalPrimalBlockMatrix_mul_dualSlack]
  ext x y
  rcases x with ⟨b, i⟩
  rcases y with ⟨c, j⟩
  by_cases hbc : b = c
  · subst c
    have hentry :
        (matrixSdpCanonicalDiagonalBlock params model X b *
            matrixSdpCanonicalDualSlackBlockFamily params model Z b) i j = 0 := by
      have hblock :=
        congrArg (fun Y => matrixSdpCanonicalDiagonalBlock params model Y b)
          hcanonical
      change matrixSdpCanonicalDiagonalBlock params model
          (X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model)) b =
        matrixSdpCanonicalDiagonalBlock params model 0 b at hblock
      have hzero :
          matrixSdpCanonicalDiagonalBlock params model
              (0 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) b =
            0 := by
        ext i j
        rfl
      rw [matrixSdpCanonicalDiagonalBlock_mul_dualSlack] at hblock
      rw [hzero] at hblock
      exact congrFun (congrFun hblock i) j
    cases b with
    | none =>
        simpa [matrixSdpCanonicalPrimalBlockFamily,
          matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement] using
          hentry.trans
            (show (0 : ℂ) =
                (0 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
                  (none, i) (none, j) by
              rfl)
    | some g =>
        simpa [matrixSdpCanonicalPrimalBlockFamily] using
          hentry.trans
            (show (0 : ℂ) =
                (0 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
                  (some g, i) (some g, j) by
              rfl)
  · change (if b = c then
          (matrixSdpCanonicalPrimalBlockFamily params model
              (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) b *
            matrixSdpCanonicalDualSlackBlockFamily params model Z b) i j
        else 0) = (0 : ℂ)
    simp [hbc]

/-- Canonical complementary slackness implies the paper-form defect equation
`T_g (Z - A_g) = 0` on each polynomial block. -/
theorem matrixSdpComplementarySlacknessDefect_of_canonical
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (hcanonical :
      matrixSdpCanonicalPrimalBlockMatrix params model T *
          (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (g : Polynomial params) :
    matrixSdpComplementarySlacknessDefect params model T Z g = 0 := by
  have hblock :=
    congrArg
      (fun X => matrixSdpCanonicalDiagonalBlock params model X (some g))
      hcanonical
  have hzero :
      matrixSdpCanonicalDiagonalBlock params model
          (0 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) (some g) =
        0 := by
    ext i j
    rfl
  rw [matrixSdpCanonicalPrimalBlockMatrix_mul_dualSlack] at hblock
  rw [hzero] at hblock
  simpa [matrixSdpComplementarySlacknessDefect] using hblock





/-- Vanishing of the canonical slack block is exactly saturation of the paper
primal submeasurement. -/
theorem matrixSdpPrimalTotalEqOne_of_canonicalSlackOperator_eq_zero
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (hSlack : matrixSdpCanonicalSlackOperator params model T = 0) :
    ∑ g : Polynomial params, T.effect g = 1 := by
  have hsub : (1 : MatrixOperator model.space) - ∑ g : Polynomial params, T.effect g = 0 := by
    simpa [matrixSdpCanonicalSlackOperator] using hSlack
  exact (sub_eq_zero.mp hsub).symm

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


