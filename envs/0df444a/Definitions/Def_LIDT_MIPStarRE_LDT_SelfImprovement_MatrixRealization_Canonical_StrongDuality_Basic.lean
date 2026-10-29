-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
-- name    : LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:13:13.006978+00:00
-- url     : https://prove2.me/theorems/ff7c74da-b95a-4315-9582-0526324a31bc
-- title:
--   LIDT definitions: LDT / SelfImprovement / MatrixRealization / Canonical / StrongDuality / Basic
-- statement:
--   This bundle develops the analytic foundations for strong duality of the canonical matrix SDP. It proves feasibility and trace identities, controls feasible matrix norms, and packages the relevant diagonal-block, constraint, and objective maps as continuous real-linear maps.
--
--   Principal definitions:
--   - `matrixSdpCanonicalPrimalFeasible_nonempty`: exhibits a feasible canonical primal point.
--   - `matrixSdpCanonicalConstraintOperator_trace_eq`: identifies the trace of the constraint image.
--   - `matrixSdpCanonicalNonnegative_norm_le_constraint_trace_re`: controls a PSD variable by the real constraint trace.
--   - `matrixSdpCanonicalPrimalFeasible_trace_eq`: gives the trace of a feasible primal matrix.
--   - `matrixSdpCanonicalPrimalFeasible_norm_le`: gives a uniform norm bound for feasible matrices.
--   - `matrixSdpCanonicalDiagonalBlockCLM`: the continuous linear map extracting a diagonal block.
--   - `matrixSdpCanonicalConstraintOperatorCLM`: the continuous constraint map.
--   - `matrixSdpCanonicalPrimalObjectiveCLM`: the continuous primal objective functional.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Basic.lean#L30-L461

-- Generated from MIPStarRE/LDT/SelfImprovement/MatrixRealization/Canonical/StrongDuality/Basic.lean by skeleton subtraction.
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
# Section 9 -- Canonical SDP strong-duality preliminaries

This module contains the feasibility, compactness, closedness, and
objective-continuity lemmas used in the finite-dimensional strong-duality
argument for the canonical matrix SDP.

## References

- `references/ldt-paper/self_improvement.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder _root_.Matrix.Norms.Elementwise Topology

/-- The canonical primal SDP has a feasible point, supplied by the explicit
strict primal submeasurement. -/
theorem matrixSdpCanonicalPrimalFeasible_nonempty
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      MatrixSdpCanonicalPrimalFeasible params model X :=
  ⟨matrixSdpCanonicalPrimalBlockMatrix params model
      (matrixSdpStrictPrimalSubmeasurement params model),
    matrixSdpCanonicalStrictPrimalBlockMatrix_feasible params model⟩

/-- The canonical equality-constraint operator preserves trace. -/
theorem matrixSdpCanonicalConstraintOperator_trace_eq
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    Matrix.trace (matrixSdpCanonicalConstraintOperator params model X) =
      Matrix.trace X := by
  rw [matrixSdpCanonical_trace_eq_sum_diagonalBlock params model X]
  unfold matrixSdpCanonicalConstraintOperator
  rw [Matrix.trace_sum]

/-- A PSD canonical primal variable is norm-controlled by the real trace of its
constraint image. -/
theorem matrixSdpCanonicalNonnegative_norm_le_constraint_trace_re
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : 0 ≤ X) :
    ‖X‖ ≤ Complex.re
      (Matrix.trace (matrixSdpCanonicalConstraintOperator params model X)) := by
  rw [matrixSdpCanonicalConstraintOperator_trace_eq params model X]
  exact MIPStarRE.Quantum.norm_le_trace_re_of_nonneg hX

/-- A feasible canonical primal matrix has trace equal to the base Hilbert-space dimension. -/
theorem matrixSdpCanonicalPrimalFeasible_trace_eq
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Matrix.trace X = (Fintype.card model.space.carrier : ℂ) := by
  calc
    Matrix.trace X = Matrix.trace (matrixSdpCanonicalConstraintOperator params model X) := by
      exact (matrixSdpCanonicalConstraintOperator_trace_eq params model X).symm
    _ = Matrix.trace (1 : MatrixOperator model.space) := by rw [hX.constraintEqOne]
    _ = (Fintype.card model.space.carrier : ℂ) := by rw [Matrix.trace_one]

/-- Feasible canonical primal matrices have uniformly bounded elementwise norm. -/
theorem matrixSdpCanonicalPrimalFeasible_norm_le
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ‖X‖ ≤ (Fintype.card model.space.carrier : ℝ) := by
  have hnorm := MIPStarRE.Quantum.norm_le_trace_re_of_nonneg hX.nonnegative
  rw [matrixSdpCanonicalPrimalFeasible_trace_eq params model X hX] at hnorm
  simpa using hnorm

/-- The feasible set of the canonical primal SDP is bounded in the elementwise matrix norm. -/
theorem matrixSdpCanonicalPrimalFeasible_isBounded
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Bornology.IsBounded
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} := by
  rw [isBounded_iff_forall_norm_le]
  exact ⟨(Fintype.card model.space.carrier : ℝ), fun X hX =>
    matrixSdpCanonicalPrimalFeasible_norm_le params model X hX⟩

/-- The projection onto one diagonal block of the canonical primal matrix, as a
continuous real-linear map. -/
noncomputable def matrixSdpCanonicalDiagonalBlockCLM
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (b : MatrixSdpCanonicalBlockIndex params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →L[ℝ]
      MatrixOperator model.space :=
  ContinuousLinearMap.mk
    ((matrixSdpCanonicalDiagonalBlockLinearMap params model b).restrictScalars ℝ)
    (continuous_matrix fun i j => continuous_apply_apply (b, i) (b, j))

@[simp]
theorem matrixSdpCanonicalDiagonalBlockCLM_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (b : MatrixSdpCanonicalBlockIndex params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalDiagonalBlockCLM params model b X =
      matrixSdpCanonicalDiagonalBlock params model X b :=
  rfl

/-- The canonical equality-constraint operator as a continuous real-linear map. -/
noncomputable def matrixSdpCanonicalConstraintOperatorCLM
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →L[ℝ]
      MatrixOperator model.space :=
  ∑ b : MatrixSdpCanonicalBlockIndex params,
    matrixSdpCanonicalDiagonalBlockCLM params model b

@[simp]
theorem matrixSdpCanonicalConstraintOperatorCLM_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalConstraintOperatorCLM params model X =
      matrixSdpCanonicalConstraintOperator params model X := by
  simp [matrixSdpCanonicalConstraintOperatorCLM, matrixSdpCanonicalConstraintOperator]

/-- The canonical primal objective as a continuous real-linear functional. -/
noncomputable def matrixSdpCanonicalPrimalObjectiveCLM
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →L[ℝ] ℝ :=
  MIPStarRE.Quantum.realTracePairingCLM
    (matrixSdpCanonicalObjectiveOperator params model)

/-- The canonical primal equality-constraint operator is continuous. -/
theorem continuous_matrixSdpCanonicalConstraintOperator
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Continuous fun X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) =>
      matrixSdpCanonicalConstraintOperator params model X := by
  have h :
      (fun X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) =>
        matrixSdpCanonicalConstraintOperator params model X) =
        fun X => matrixSdpCanonicalConstraintOperatorCLM params model X := by
    funext X
    exact (matrixSdpCanonicalConstraintOperatorCLM_apply params model X).symm
  rw [h]
  exact (matrixSdpCanonicalConstraintOperatorCLM params model).continuous

/-- A canonical block-diagonal operator is Hermitian when all diagonal blocks are
Hermitian. -/
theorem matrixSdpCanonicalBlockDiagonal_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (hB : ∀ b, (B b).IsHermitian) :
    (matrixSdpCanonicalBlockDiagonal params model B).IsHermitian := by
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  exact (Matrix.isHermitian_blockDiagonal_iff.mpr hB).reindex
    (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))

/-- The canonical dual block operator is Hermitian when the paper dual matrix is
Hermitian. -/
theorem matrixSdpCanonicalDualOperator_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hZ : Z.IsHermitian) :
    (matrixSdpCanonicalDualOperator params model Z).IsHermitian := by
  rw [matrixSdpCanonicalDualOperator]
  exact matrixSdpCanonicalBlockDiagonal_isHermitian params model
    (matrixSdpCanonicalDualOperatorBlockFamily params model Z) fun _ => hZ

/-- The canonical objective block operator is Hermitian. -/
theorem matrixSdpCanonicalObjectiveOperator_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (matrixSdpCanonicalObjectiveOperator params model).IsHermitian := by
  rw [matrixSdpCanonicalObjectiveOperator]
  refine matrixSdpCanonicalBlockDiagonal_isHermitian params model
    (matrixSdpCanonicalObjectiveBlockFamily params model) ?_
  intro b
  cases b with
  | none => simp [matrixSdpCanonicalObjectiveBlockFamily]
  | some g =>
      exact (Matrix.nonneg_iff_posSemidef.mp
        (matrixAveragedPointOperator_nonneg params model g)).isHermitian

/-- The canonical dual slack block operator is Hermitian when the paper dual
matrix is Hermitian. -/
theorem matrixSdpCanonicalDualOperator_sub_objectiveOperator_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hZ : Z.IsHermitian) :
    (matrixSdpCanonicalDualOperator params model Z -
      matrixSdpCanonicalObjectiveOperator params model).IsHermitian :=
  (matrixSdpCanonicalDualOperator_isHermitian params model Z hZ).sub
    (matrixSdpCanonicalObjectiveOperator_isHermitian params model)

/-- The canonical dual block trace pairing equals the paper dual trace pairing
against the canonical constraint image. -/
theorem matrixSdpCanonicalDualOperator_trace_constraint
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (Z : MatrixOperator model.space) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalDualOperator params model Z * X)) =
      Complex.re (Matrix.trace
        (Z * matrixSdpCanonicalConstraintOperator params model X)) := by
  congr 1
  rw [matrixSdpCanonicalDualOperator]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul_left]
  simp only [matrixSdpCanonicalDualOperatorBlockFamily_apply]
  rw [← Matrix.trace_sum]
  rw [← Finset.mul_sum]
  rfl

/-- The canonical equality-constraint image of a positive canonical primal
matrix is positive semidefinite. -/
theorem matrixSdpCanonicalConstraintOperator_nonneg_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : 0 ≤ X) :
    0 ≤ matrixSdpCanonicalConstraintOperator params model X := by
  unfold matrixSdpCanonicalConstraintOperator
  exact Finset.sum_nonneg fun b _ =>
    matrixSdpCanonicalDiagonalBlock_nonneg params model hX b

/-- The canonical equality-constraint image of a positive canonical primal
matrix is Hermitian. -/
theorem matrixSdpCanonicalConstraintOperator_isHermitian_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : 0 ≤ X) :
    (matrixSdpCanonicalConstraintOperator params model X).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp
    (matrixSdpCanonicalConstraintOperator_nonneg_of_nonnegative params model hX)).isHermitian

/-- A trace-pairing separator against every positive semidefinite canonical primal
matrix can be converted into the paper-form dual feasibility inequalities.

This is a separator-conversion lemma for the later zero-gap argument, not the
strong-duality theorem itself. -/
theorem matrixSdpCanonicalDualConstraint_nonneg_of_trace_pairing_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hHerm :
      (matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model).IsHermitian)
    (htrace :
      ∀ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
        0 ≤ X →
          0 ≤ Complex.re (Matrix.trace
            ((matrixSdpCanonicalDualOperator params model Z -
                matrixSdpCanonicalObjectiveOperator params model) * X))) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g := by
  have hcanonical :
      0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model :=
    MIPStarRE.Quantum.nonneg_of_trace_mul_nonneg_of_isHermitian hHerm htrace
  exact matrixSdpDualFeasible_of_canonicalDualConstraint_nonneg params model Z hcanonical

/-- The feasible set of the canonical primal SDP is closed. -/
theorem matrixSdpCanonicalPrimalFeasible_isClosed
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsClosed
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} := by
  classical
  have hnonneg : IsClosed
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) | 0 ≤ X} :=
    MIPStarRE.Quantum.isClosed_op_nonnegative
      (ι := (matrixSdpCanonicalBlockHilbertSpace params model).carrier)
  have hconstraint : IsClosed
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        matrixSdpCanonicalConstraintOperator params model X = (1 : MatrixOperator model.space)} :=
    isClosed_eq (continuous_matrixSdpCanonicalConstraintOperator params model) continuous_const
  rw [show
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} =
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) | 0 ≤ X} ∩
        {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
          matrixSdpCanonicalConstraintOperator params model X =
            (1 : MatrixOperator model.space)} by
    ext X
    constructor
    · intro hX
      exact ⟨hX.nonnegative, hX.constraintEqOne⟩
    · intro hX
      exact ⟨hX.1, hX.2⟩]
  exact hnonneg.inter hconstraint

/-- The paper-form canonical dual feasible set is closed. -/
theorem matrixSdpCanonicalDualFeasible_isClosed
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsClosed
      {Z : MatrixOperator model.space |
        ∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g} := by
  classical
  rw [show
      {Z : MatrixOperator model.space |
        ∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g} =
      ⋂ g : Polynomial params,
        {Z : MatrixOperator model.space |
          0 ≤ matrixSdpDualSlackOperator params model Z g} by
    ext Z
    simp]
  refine isClosed_iInter fun g => ?_
  have hslack : Continuous fun Z : MatrixOperator model.space =>
      matrixSdpDualSlackOperator params model Z g := by
    unfold matrixSdpDualSlackOperator
    exact continuous_id.sub continuous_const
  simpa [Set.preimage] using
    (MIPStarRE.Quantum.isClosed_op_nonnegative (ι := model.space.carrier)).preimage hslack

/-- The paper-form canonical dual objective is continuous. -/
theorem continuous_matrixSdpDualObjective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Continuous fun Z : MatrixOperator model.space => matrixSdpDualObjective model Z := by
  unfold matrixSdpDualObjective
  exact Complex.continuous_re.comp continuous_id.matrix_trace

/-- The strict-witness-bounded dual feasible sublevel is closed. -/
theorem matrixSdpCanonicalDualFeasibleSublevel_isClosed
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsClosed
      {Z : MatrixOperator model.space |
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} := by
  have hfeasible := matrixSdpCanonicalDualFeasible_isClosed params model
  have hsublevel : IsClosed
      {Z : MatrixOperator model.space |
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} :=
    isClosed_le (continuous_matrixSdpDualObjective params model) continuous_const
  rw [show
      {Z : MatrixOperator model.space |
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} =
      {Z : MatrixOperator model.space |
        ∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g} ∩
      {Z : MatrixOperator model.space |
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} by
    ext Z
    rfl]
  exact hfeasible.inter hsublevel

/-- The strict-witness-bounded dual feasible sublevel is norm-bounded. -/
theorem matrixSdpCanonicalDualFeasibleSublevel_isBounded
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Bornology.IsBounded
      {Z : MatrixOperator model.space |
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨matrixSdpDualObjective model (matrixSdpStrictDualWitness model), fun Z hZ => ?_⟩
  calc
    ‖Z‖ ≤ Complex.re (Matrix.trace Z) :=
      MIPStarRE.Quantum.norm_le_trace_re_of_nonneg
        (matrixSdpDualPositive_of_dualFeasible params model Z hZ.1)
    _ = matrixSdpDualObjective model Z := by rfl
    _ ≤ matrixSdpDualObjective model (matrixSdpStrictDualWitness model) := hZ.2

/-- The strict-witness-bounded dual feasible sublevel is compact. -/
theorem matrixSdpCanonicalDualFeasibleSublevel_isCompact
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsCompact
      {Z : MatrixOperator model.space |
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} :=
  Metric.isCompact_of_isClosed_isBounded
    (matrixSdpCanonicalDualFeasibleSublevel_isClosed params model)
    (matrixSdpCanonicalDualFeasibleSublevel_isBounded params model)

/-- The paper-form canonical dual objective attains its minimum on the feasible set. -/
theorem matrixSdpCanonicalDualObjective_exists_isMinOn
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ Z : MatrixOperator model.space,
      (∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
      ∀ W : MatrixOperator model.space,
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model W g) →
        matrixSdpDualObjective model Z ≤ matrixSdpDualObjective model W := by
  let c := matrixSdpDualObjective model (matrixSdpStrictDualWitness model)
  let S : Set (MatrixOperator model.space) :=
    {Z | (∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
      matrixSdpDualObjective model Z ≤ c}
  have hScompact : IsCompact S := by
    simpa [S, c] using matrixSdpCanonicalDualFeasibleSublevel_isCompact params model
  have hSne : S.Nonempty := by
    refine ⟨matrixSdpStrictDualWitness model, ?_⟩
    exact ⟨matrixSdpStrictDualWitness_dualFeasible params model, le_rfl⟩
  obtain ⟨Z, hZS, hZmin⟩ := hScompact.exists_isMinOn hSne
    (continuous_matrixSdpDualObjective params model).continuousOn
  refine ⟨Z, hZS.1, fun W hW => ?_⟩
  by_cases hWc : matrixSdpDualObjective model W ≤ c
  · exact hZmin ⟨hW, hWc⟩
  · have hcW : c ≤ matrixSdpDualObjective model W := le_of_not_ge hWc
    exact hZS.2.trans hcW

/-- The feasible set of the canonical primal SDP is compact. -/
theorem matrixSdpCanonicalPrimalFeasible_isCompact
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsCompact
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} :=
  Metric.isCompact_of_isClosed_isBounded
    (matrixSdpCanonicalPrimalFeasible_isClosed params model)
    (matrixSdpCanonicalPrimalFeasible_isBounded params model)

/-- The canonical primal objective is continuous. -/
theorem continuous_matrixSdpCanonicalPrimalObjective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Continuous fun X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) =>
      Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X)) := by
  have hmul :
      Continuous fun X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) =>
        matrixSdpCanonicalObjectiveOperator params model * X :=
    continuous_const.mul continuous_id
  exact Complex.continuous_re.comp hmul.matrix_trace

end MIPStarRE.LDT.SelfImprovement

end

end LIDT


