-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:15:31.890158+00:00
-- url     : https://prove2.me/theorems/8702294b-ee59-4b58-936f-3c37bf178bfe
-- title:
--   LIDT definitions: LDT / SelfImprovement / MatrixRealization / Canonical / Saturated
-- statement:
--   This bundle defines saturation of the canonical primal SDP by moving the none slack block into a distinguished polynomial block. It proves preservation of block structure, feasibility, the exact objective formula, monotonicity of the objective, and survival of strong duality.
--
--   Principal definitions:
--   - `matrixSdpCanonicalSaturateSlackBlockFamily`: moves the canonical slack into the distinguished polynomial block.
--   - `matrixSdpCanonicalSaturateSlackBlockMatrix`: the resulting saturated canonical matrix.
--   - `matrixSdpCanonicalDiagonalBlock_saturateSlackBlockMatrix_none`: identifies the saturated none block.
--   - `matrixSdpCanonicalDiagonalBlock_saturateSlackBlockMatrix_some`: identifies the polynomial blocks after saturation.
--   - `matrixSdpCanonicalSaturateSlackBlockMatrix_feasible`: proves feasibility is preserved.
--   - `matrixSdpCanonicalObjective_trace_saturateSlackBlockMatrix`: gives the exact saturated objective.
--   - `matrixSdpCanonicalObjective_trace_le_saturateSlackBlockMatrix`: proves saturation does not decrease the objective.
--   - `matrixSdpCanonicalSaturateSlackBlockMatrix_strongDuality`: proves strong-duality equality survives saturation.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/Saturated.lean#L30-L482

-- Generated from MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/Saturated.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
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
# Section 9 — Saturated canonical SDP witnesses

This module contains the zero-slack variant of the canonical SDP output used in
the self-improvement argument.  The canonical block SDP supplies a feasible
matrix `X`; when its slack diagonal block is zero, the extracted polynomial
blocks form a complete measurement without using the auxiliary dominance
condition \(I \le Z\).

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

/-- Move the canonical primal slack block into the distinguished polynomial block.

Paper origin: `references/ldt-paper/self_improvement.tex:177-190`.  The paper
passes from an optimal canonical block matrix to a saturated paper primal
measurement.  This block family implements the source-faithful completion step:
the `none` block is set to zero, and its positive mass is added to the fixed
polynomial block `sdpDistinguishedPolynomial params`.  This avoids the auxiliary
route which proves saturation from an additional bound `I ≤ Z`. -/
noncomputable def matrixSdpCanonicalSaturateSlackBlockFamily
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space
  | none => 0
  | some g =>
      matrixSdpCanonicalDiagonalBlock params model X (some g) +
        if g = sdpDistinguishedPolynomial params then
          matrixSdpCanonicalDiagonalBlock params model X none
        else 0

@[simp] theorem matrixSdpCanonicalSaturateSlackBlockFamily_none
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalSaturateSlackBlockFamily params model X none = 0 :=
  rfl

@[simp] theorem matrixSdpCanonicalSaturateSlackBlockFamily_some
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (g : Polynomial params) :
    matrixSdpCanonicalSaturateSlackBlockFamily params model X (some g) =
      matrixSdpCanonicalDiagonalBlock params model X (some g) +
        if g = sdpDistinguishedPolynomial params then
          matrixSdpCanonicalDiagonalBlock params model X none
        else 0 :=
  rfl

/-- The saturated canonical matrix obtained by completing the slack at the
distinguished polynomial block.

This is a source-faithful replacement for the Lean-only saturation route through
`I ≤ Z`: it changes only the primal matrix, setting the extra canonical slack
block to zero and adding that block to `sdpDistinguishedPolynomial params`. -/
noncomputable def matrixSdpCanonicalSaturateSlackBlockMatrix
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  matrixSdpCanonicalBlockDiagonal params model
    (matrixSdpCanonicalSaturateSlackBlockFamily params model X)

/-- The saturated canonical matrix has zero extra slack block. -/
@[simp] theorem matrixSdpCanonicalDiagonalBlock_saturateSlackBlockMatrix_none
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalSaturateSlackBlockMatrix params model X) none =
      0 := by
  simp [matrixSdpCanonicalSaturateSlackBlockMatrix]

/-- The polynomial blocks of the saturated canonical matrix agree with the
original diagonal blocks, except that the distinguished polynomial receives the
old `none` slack block. -/
@[simp] theorem matrixSdpCanonicalDiagonalBlock_saturateSlackBlockMatrix_some
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (g : Polynomial params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalSaturateSlackBlockMatrix params model X) (some g) =
      matrixSdpCanonicalDiagonalBlock params model X (some g) +
        if g = sdpDistinguishedPolynomial params then
          matrixSdpCanonicalDiagonalBlock params model X none
        else 0 := by
  simp [matrixSdpCanonicalSaturateSlackBlockMatrix]

/-- Feasibility is preserved by moving the `none` slack block into
`sdpDistinguishedPolynomial params`.

The proof uses only positivity of principal diagonal blocks of the original
feasible canonical matrix and the canonical equality constraint.  It is the
source-faithful saturation step corresponding to
`references/ldt-paper/self_improvement.tex:182-190`, avoiding any use of an
auxiliary dominance hypothesis `I ≤ Z`. -/
theorem matrixSdpCanonicalSaturateSlackBlockMatrix_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalSaturateSlackBlockMatrix params model X) :=
  have hnonnegative : 0 ≤ matrixSdpCanonicalSaturateSlackBlockMatrix params model X := by
    rw [matrixSdpCanonicalSaturateSlackBlockMatrix]
    refine matrixSdpCanonicalBlockDiagonal_nonneg params model
      (matrixSdpCanonicalSaturateSlackBlockFamily params model X) ?_
    intro b
    cases b with
    | none =>
        simp
    | some g =>
        have hsome :
            0 ≤ matrixSdpCanonicalDiagonalBlock params model X (some g) :=
          matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative (some g)
        by_cases hg : g = sdpDistinguishedPolynomial params
        · have hnone :
              0 ≤ matrixSdpCanonicalDiagonalBlock params model X none :=
            matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative none
          simpa [hg] using add_nonneg hsome hnone
        · simpa [hg] using hsome
  have hconstraintEqOne : matrixSdpCanonicalConstraintOperator params model
      (matrixSdpCanonicalSaturateSlackBlockMatrix params model X) = 1 := by
    classical
    have hconstraint :
        matrixSdpCanonicalDiagonalBlock params model X none +
            ∑ g : Polynomial params,
              matrixSdpCanonicalDiagonalBlock params model X (some g) =
          1 := by
      simpa [matrixSdpCanonicalConstraintOperator, Fintype.sum_option] using
        hX.constraintEqOne
    rw [matrixSdpCanonicalSaturateSlackBlockMatrix,
      matrixSdpCanonicalConstraintOperator_blockDiagonal, Fintype.sum_option]
    simp only [matrixSdpCanonicalSaturateSlackBlockFamily_none,
      matrixSdpCanonicalSaturateSlackBlockFamily_some, zero_add]
    rw [Finset.sum_add_distrib]
    have hsingle :
        (∑ g : Polynomial params,
            (if g = sdpDistinguishedPolynomial params then
              matrixSdpCanonicalDiagonalBlock params model X none
            else 0)) =
          matrixSdpCanonicalDiagonalBlock params model X none := by
      rw [Finset.sum_eq_single (sdpDistinguishedPolynomial params)]
      · simp
      · intro g _ hg
        simp [hg]
      · intro hnot
        simp at hnot
    simpa [hsingle, add_comm, add_left_comm, add_assoc] using hconstraint
  { nonnegative := hnonnegative, constraintEqOne := hconstraintEqOne }

/-- Exact objective formula for source-faithful slack saturation.

After the `none` block is moved to `sdpDistinguishedPolynomial params`, the
canonical objective increases by the trace pairing of the old slack block with
the averaged point operator for that distinguished polynomial.  The `none` block
itself has objective coefficient zero, which is why this completion is the
paper-faithful alternative to deriving saturation through an auxiliary `I ≤ Z`
hypothesis. -/
theorem matrixSdpCanonicalObjective_trace_saturateSlackBlockMatrix
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalSaturateSlackBlockMatrix params model X)) =
      Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) +
        Complex.re (Matrix.trace
          (matrixAveragedPointOperator params model
              (sdpDistinguishedPolynomial params) *
            matrixSdpCanonicalDiagonalBlock params model X none)) := by
  classical
  rw [matrixSdpCanonicalObjectiveOperator,
    matrixSdpCanonicalSaturateSlackBlockMatrix]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul_left]
  simp only [Complex.re_sum, Fintype.sum_option,
    matrixSdpCanonicalObjectiveBlockFamily_none,
    matrixSdpCanonicalSaturateSlackBlockFamily_none, zero_mul, Matrix.trace_zero,
    zero_add, matrixSdpCanonicalObjectiveBlockFamily_some,
    matrixSdpCanonicalSaturateSlackBlockFamily_some]
  calc
    ∑ g : Polynomial params,
        Complex.re (Matrix.trace
          (matrixAveragedPointOperator params model g *
            (matrixSdpCanonicalDiagonalBlock params model X (some g) +
              if g = sdpDistinguishedPolynomial params then
                matrixSdpCanonicalDiagonalBlock params model X none
              else 0))) =
        ∑ g : Polynomial params,
          (Complex.re (Matrix.trace
              (matrixAveragedPointOperator params model g *
                matrixSdpCanonicalDiagonalBlock params model X (some g))) +
            Complex.re (Matrix.trace
              (matrixAveragedPointOperator params model g *
                (if g = sdpDistinguishedPolynomial params then
                  matrixSdpCanonicalDiagonalBlock params model X none
                else 0)))) := by
          refine Finset.sum_congr rfl ?_
          intro g _
          rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    _ = (∑ g : Polynomial params,
          Complex.re (Matrix.trace
            (matrixAveragedPointOperator params model g *
              matrixSdpCanonicalDiagonalBlock params model X (some g)))) +
        ∑ g : Polynomial params,
          Complex.re (Matrix.trace
            (matrixAveragedPointOperator params model g *
              (if g = sdpDistinguishedPolynomial params then
                matrixSdpCanonicalDiagonalBlock params model X none
              else 0))) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ g : Polynomial params,
          Complex.re (Matrix.trace
            (matrixAveragedPointOperator params model g *
              matrixSdpCanonicalDiagonalBlock params model X (some g)))) +
        Complex.re (Matrix.trace
          (matrixAveragedPointOperator params model
              (sdpDistinguishedPolynomial params) *
            matrixSdpCanonicalDiagonalBlock params model X none)) := by
          congr 1
          rw [Finset.sum_eq_single (sdpDistinguishedPolynomial params)]
          · simp
          · intro g _ hg
            simp [hg]
          · intro hnot
            simp at hnot

/-- Saturating the canonical slack block cannot decrease the canonical primal
objective.

The added objective term is nonnegative because the distinguished averaged point
operator is positive semidefinite and the original `none` block is a positive
principal block of the feasible canonical matrix. -/
theorem matrixSdpCanonicalObjective_trace_le_saturateSlackBlockMatrix
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
      Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalSaturateSlackBlockMatrix params model X)) := by
  rw [matrixSdpCanonicalObjective_trace_saturateSlackBlockMatrix]
  exact le_add_of_nonneg_right
    (MIPStarRE.Quantum.trace_mul_nonneg_of_nonneg
      (matrixAveragedPointOperator_nonneg params model
        (sdpDistinguishedPolynomial params))
      (matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative none))

/-- Objective equality survives source-faithful slack saturation.

If a feasible canonical primal matrix and a dual-feasible `Z` have equal
objective values, then the saturated matrix obtained by moving the slack block
to `sdpDistinguishedPolynomial params` has the same objective value.  The proof
combines objective monotonicity of the completion with canonical weak duality;
it does not use the auxiliary dominance condition `I ≤ Z`. -/
theorem matrixSdpCanonicalSaturateSlackBlockMatrix_strongDuality
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
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalSaturateSlackBlockMatrix params model X)) =
      matrixSdpDualObjective model Z := by
  let Xsat := matrixSdpCanonicalSaturateSlackBlockMatrix params model X
  have hXsat : MatrixSdpCanonicalPrimalFeasible params model Xsat :=
    matrixSdpCanonicalSaturateSlackBlockMatrix_feasible params model X hX
  have hsat_le_dual :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * Xsat)) ≤
        matrixSdpDualObjective model Z :=
    matrixSdpCanonicalWeakDuality params model Xsat hXsat Z
      (matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model Z hdual)
  have hdual_le_sat :
      matrixSdpDualObjective model Z ≤
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * Xsat)) := by
    rw [← hstrong]
    exact matrixSdpCanonicalObjective_trace_le_saturateSlackBlockMatrix
      params model X hX
  exact le_antisymm hsat_le_dual hdual_le_sat



/-- Assemble a paper-form optimal witness from canonical complementary
slackness and an explicitly saturated slack block.

The hypotheses are precisely the canonical SDP data needed after the
block-diagonal reduction: dual feasibility, equality of the primal and dual
objectives, canonical complementary slackness, and zero slack block
`I - ∑_g T_g = 0`.  No dominance condition on the dual variable is used. -/
theorem matrixSdpOptimalWitness_of_canonicalSaturatedComplementarySlackness
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g)
    (hstrong :
      matrixSdpPrimalObjective params model T = matrixSdpDualObjective model Z)
    (hcanonical :
      matrixSdpCanonicalPrimalBlockMatrix params model T *
          (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hSlack : matrixSdpCanonicalSlackOperator params model T = 0) :
    MatrixSdpOptimalWitness params model T Z where
  primalTotalEqOne :=
    matrixSdpPrimalTotalEqOne_of_canonicalSlackOperator_eq_zero params model T hSlack
  dualFeasible := hdual
  strongDuality := hstrong
  complementarySlackness :=
    fun g =>
    have hzero :
        matrixSdpComplementarySlacknessDefect params model T Z g = 0 :=
      matrixSdpComplementarySlacknessDefect_of_canonical params model T Z hcanonical g
    sub_eq_zero.mp (by
      simpa [matrixSdpComplementarySlacknessDefect, matrixSdpDualSlackOperator,
        Matrix.mul_sub] using hzero)

/-- Assemble a paper-form optimal witness from an arbitrary feasible canonical
matrix with zero slack block.

The extracted polynomial diagonal blocks form the paper primal measurement.
The zero slack block supplies normalization; the canonical objective and
complementary-slackness equations are transported to the extracted
submeasurement. -/
theorem matrixSdpOptimalWitness_of_canonicalFeasibleSaturatedComplementarySlackness
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
        matrixSdpDualObjective model Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hSlack : matrixSdpCanonicalDiagonalBlock params model X none = 0) :
    MatrixSdpOptimalWitness params model
      (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) Z := by
  refine matrixSdpOptimalWitness_of_canonicalSaturatedComplementarySlackness
    params model (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) Z
    hdual ?_ ?_ ?_
  · calc
      matrixSdpPrimalObjective params model
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX)
          = Complex.re (Matrix.trace
              (matrixSdpCanonicalObjectiveOperator params model * X)) := by
              exact (matrixSdpCanonicalObjective_trace_extractedPrimalSubmeasurement
                params model X hX).symm
      _ = matrixSdpDualObjective model Z := hstrong
  · exact matrixSdpCanonicalPrimalBlockMatrix_extracted_mul_dualSlack_of_canonical
      params model X hX Z hcanonical
  · rw [matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement]
    exact hSlack



/-- Assemble the canonical block-SDP conclusions as the matrix-level statement
with zero slack block.

For a feasible canonical primal matrix `X`, the hypothesis
`X_none,none = 0` is exactly the saturated form of the paper's final slack
block assertion.  The theorem extracts the polynomial diagonal blocks and
records the resulting complete primal measurement and complementary-slackness
equations. -/
theorem matrixSdpStatementWithSlackness_of_canonicalFeasibleSaturatedComplementarySlackness
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
        matrixSdpDualObjective model Z)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hSlack : matrixSdpCanonicalDiagonalBlock params model X none = 0) :
    MatrixSdpStatementWithSlackness params model where
  witness :=
    let hopt :=
      matrixSdpOptimalWitness_of_canonicalFeasibleSaturatedComplementarySlackness
        params model X hX Z hdual hstrong hcanonical hSlack
    ⟨hopt.primalMeasurement, Z, by
      simpa [MatrixSdpOptimalWitness.primalMeasurement,
        MIPStarRE.Quantum.Measurement.ofSumEqOne] using hopt⟩

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


