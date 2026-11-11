-- Prove2me | Definitions.Def_OAIQ241TT006
-- name    : OAIQ241TT006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:51:37.545551+00:00
-- url     : https://prove2.me/theorems/d9f13dd0-912d-45d3-97dd-c81f14474c76
-- title:
--   Definitions bundle OAIQ241TT006 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 595 declarations of OpenAI's Lean: 438 definitions, 13 inductive types or structures, 25 instances and 119 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.GreedyTree.Stack.Arc`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.EraseEdge`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.EraseInput`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.ReachState`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.ReachState.bits`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.ReachState.next`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.SEdge`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.Subgraph`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.Subgraph.bits`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.Subgraph.start`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.Vertex`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.Walk`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.arcCode`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.arcEdge`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.arcNumber`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.arcState`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.arcSubedge`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.arcVertex`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.deleteAt`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.erase`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.eraseContext`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.eraseEdgeCode`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.eraseEdgeContext`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.eraseEdgeIndex`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.eraseIndex`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.eraseInputCode`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.eraseSubedge`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.initVertexCode`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.reachBits`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.reachCode`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.reachSubgraph`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.reachView`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.sedgeCode`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.sedgeContext`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.sedgeIndex`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.subgraphBits`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.subgraphCode`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.subgraphGraph`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.subgraphView`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.vertexCode` and 411 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_RationalArithmeticMeter`, `MatrixSigning_Arithmetic_RationalExpressionHeight`, `MatrixSigning_Complexity_ComplexScalarCosts`, `MatrixSigning_Complexity_GlobalCounts`, `MatrixSigning_Complexity_PolynomialCurvature`, `MatrixSigning_Complexity_PolynomialFaceBasics`, `MatrixSigning_Complexity_PolynomialFaceChoice`, `MatrixSigning_Complexity_PolynomialFaceOrbit`, `MatrixSigning_Complexity_PolynomialFaceQuery`, `MatrixSigning_Complexity_PolynomialFamilies`, `MatrixSigning_Complexity_PolynomialLists`, `MatrixSigning_Complexity_PolynomialLoops`, `MatrixSigning_Complexity_PolynomialMatrixFold`, `MatrixSigning_Complexity_PolynomialMatrixSum`, `MatrixSigning_Complexity_PolynomialOptimize`, `MatrixSigning_Complexity_PolynomialOriginalFields`, `MatrixSigning_Complexity_PolynomialPotential`, `MatrixSigning_Complexity_PolynomialRoutine`, `MatrixSigning_Complexity_PolynomialValueQuery`, `MatrixSigning_Complexity_PolynomialVariance`, `MatrixSigning_Complexity_StoredBits`, `MatrixSigning_Encoding_FrameWireCodec`, `MatrixSigning_Encoding_FramedArrayPrefix`, `MatrixSigning_Encoding_WireAppend`, `MatrixSigning_Encoding_ZeroArrayConstructor`, `MatrixSigning_Machines_ExpressionSyntax`, `MatrixSigning_Machines_SchurCellMachine`, `MatrixSigning_Machines_SparseCoefficientStage`, `MatrixSigning_Machines_UnaryLengthMachine`, `MatrixSigning_Matrices_FDerivTightPart`, `MatrixSigning_Matrices_JetBoundInverseSandwich`, `MatrixSigning_Matrices_NormRetractH`, `MatrixSigning_Matrices_Pivot`, `MatrixSigning_Matrices_RetractH`, `MatrixSigning_Matrices_SavedPivotPacketMachine`, `MatrixSigning_Model`, `MatrixSigning_Optimization_Affine`, `MatrixSigning_Optimization_Feasible`, `MatrixSigning_Optimization_FixedPart`, `MatrixSigning_Optimization_PackValue`, `MatrixSigning_Optimization_Pencil`, `MatrixSigning_Optimization_RealVector`, `MatrixSigning_Optimization_ValueDimension`, `MatrixSigning_Optimization_ValueObjectiveCoeffs`, `MatrixSigning_Potential_ChooseCoordinate`, `MatrixSigning_Potential_CoarseBudget`, `MatrixSigning_Potential_FaceState`, `MatrixSigning_Potential_JetBoundProjection`, `MatrixSigning_Potential_NegativeWeight`, `MatrixSigning_Potential_NormPsdScalar`, `MatrixSigning_Potential_NormSq`, `MatrixSigning_Potential_NormTCoord`, `MatrixSigning_Potential_ObjectiveVarsCLM`, `MatrixSigning_Potential_Parameters2`, `MatrixSigning_Potential_PathObjectiveFirst`, `MatrixSigning_Potential_UnpackKkt`, `MatrixSigning_Potential_ValueBranch`, `MatrixSigning_Realization_CoordinateRealization`, `MatrixSigning_Realization_CurvatureRealization`, `MatrixSigning_Realization_DenseInputArrays`, `MatrixSigning_Realization_DenseInputMachine`, `MatrixSigning_Realization_EndpointRealization`, `MatrixSigning_Realization_FaceArrayRealization`, `MatrixSigning_Realization_FaceChoiceRealization`, `MatrixSigning_Realization_FaceQueryRealization`, `MatrixSigning_Realization_FaceRunRealization`, `MatrixSigning_Realization_LevelPencilRealization`, `MatrixSigning_Realization_ListRealization`, `MatrixSigning_Realization_MachineAdapter`, `MatrixSigning_Realization_MatrixStructureRealization`, `MatrixSigning_Realization_OptimizeRealization`, `MatrixSigning_Realization_OriginalFieldsRealization`, `MatrixSigning_Realization_OriginalOutputRoutine`, `MatrixSigning_Realization_OriginalSignRealization`, `MatrixSigning_Realization_PencilCompileRealization`, `MatrixSigning_Realization_PotentialRealization`, `MatrixSigning_Realization_RootRealization`, `MatrixSigning_Realization_ScheduleRealization`, `MatrixSigning_Realization_SelectionRealization`, `MatrixSigning_Realization_StencilRealization`, `MatrixSigning_Realization_StoredPSDRealization`, `MatrixSigning_Realization_ValueDataRealization`, `MatrixSigning_Realization_ValueEvalRealization`, `MatrixSigning_Realization_ValueObjectiveRealization`, `MatrixSigning_Realization_ValueQueryRealization`, `MatrixSigning_Realization_VarianceRealization`, `MatrixSigning_Realization_VectorRealization`, `MatrixSigning_Realization_WitnessRealization`, `ThinTrees_Arithmetic_BoolPrograms`, `ThinTrees_Arithmetic_ScalarRealization`, `ThinTrees_Arithmetic_UnaryArithmetic`, `ThinTrees_Arithmetic_WordHead`, `ThinTrees_BasePacking`, `ThinTrees_Continuation_BitBound`, `ThinTrees_Continuation_CenteredDomain`, `ThinTrees_Continuation_Coordinates`, `ThinTrees_Continuation_Domain`, `ThinTrees_Continuation_Encoding`, `ThinTrees_Continuation_Grid`, `ThinTrees_Continuation_Interior`, `ThinTrees_Continuation_Iteration`, `ThinTrees_Continuation_Ramp`, `ThinTrees_Encoding_GraphRealization`, `ThinTrees_Encoding_GreedyRealization`, `ThinTrees_Encoding_GreedyTree`, `ThinTrees_Encoding_InputArrays`, `ThinTrees_Encoding_InputDispatch`, `ThinTrees_Encoding_OrderedGraph`, `ThinTrees_Encoding_SelectionRealization`, `ThinTrees_Flow_FractionalOrientation`, `ThinTrees_Flow_Interior`, `ThinTrees_Flow_ParallelCopies`, `ThinTrees_Flow_RootedFlow`, `ThinTrees_Flow_RootedOrientation`, `ThinTrees_Flow_RootedRelaxation`, `ThinTrees_GraphMatrix`, `ThinTrees_Metric_CenteredMatrices`, `ThinTrees_Metric_Hierarchy`, `ThinTrees_Metric_MatrixBound`, `ThinTrees_Normalization_Descent`, `ThinTrees_Normalization_Realization`, `ThinTrees_PartitionRank`, `ThinTrees_RationalMatrix_InverseRealization`, `ThinTrees_RationalMatrix_MatrixRealization`, `ThinTrees_RationalMatrix_SchurHistory`, `ThinTrees_Representation`, `ThinTrees_Signing_GramRealization`, `ThinTrees_Signing_RationalSigning`, `ThinTrees_Signing_Realization`, `ThinTrees_Sparsification_IterationPotential`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`; the bundles `OAIQ241TT000`, `OAIQ241TT001` and `OAIQ241TT002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ241TT008` and `OAIQ241TT009`; the statements `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct`, `OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound`, `OAI.AlgorithmicThinTrees.Partitions.finite_chain_response`, `OAI.CurrentKS.RationalFace.activePotential_regular`, `OAI.CurrentKS.RationalFace.faceCandidates_progress`, `OAI.CurrentKS.RationalSDP.valuePencil_ball`, `OAI.CurrentKS.RationalSDP.valueQueryPoint_correct`, `OAI.CurrentKS.Realization.isPoly_face_orbit`, `OAI.CurrentKS.Realization.isPoly_orbitScore`, `OAI.CurrentKS.Realization.isPoly_orbitStencil`, `OAI.CurrentKS.State.kkt_strip_jet`, `OAI.CurrentKS.Variational.contDiffAt_value`, `OAI.CurrentKS.Variational.full_jacobian_inverse_bound`, `OAI.CurrentKS.Variational.jetBound_kktGiven` and `OAI.CurrentKS.Variational.kkt_curve_derivatives`; the proofs of `OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound`, `OAI.AlgorithmicThinTrees.Partitions.finite_chain_response`, `OAI.CurrentKS.RationalFace.activePotential_regular`, `OAI.CurrentKS.RationalFace.faceCandidates_progress`, `OAI.CurrentKS.RationalFace.normalizedRun_spec`, `OAI.CurrentKS.RationalFace.transition_spec`, `OAI.CurrentKS.RationalSDP.valuePencil_ball`, `OAI.CurrentKS.RationalSDP.valueQueryPoint_correct`, `OAI.CurrentKS.State.LightPoint.Psi_driftCurvature`, `OAI.CurrentKS.State.LightPoint.computed_candidates_progress`, `OAI.CurrentKS.State.LightPoint.shifted_hessian_not_psd`, `OAI.CurrentKS.State.face_value_direction_variations`, `OAI.CurrentKS.State.kkt_strip_jet`, `OAI.CurrentKS.State.value_strip_derivatives`, `OAI.CurrentKS.Variational.contDiffAt_value`, `OAI.CurrentKS.Variational.exists_smooth_kkt_branch`, `OAI.CurrentKS.Variational.full_jacobian_inverse_bound`, `OAI.CurrentKS.Variational.jetBound_kktGiven`, `OAI.CurrentKS.Variational.kkt_curve_derivatives` and `OAI.CurrentKS.Variational.value_derivatives_majorant`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT000
import Definitions.Def_OAIQ241TT001
import Definitions.Def_OAIQ241TT002

section
-- module Solutions.OAIQ241_TT.Compat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalArithmeticMeter
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

def RationalExpr.operations : RationalExpr → ℕ
  | .value _ => 0
  | .add x y | .sub x y | .mul x y | .div x y => x.operations + y.operations + 1
  | .neg x => x.operations + 1

@[simp] theorem schurEntryExpr_operations {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (i j : Fin n) :
    (schurEntryExpr M i j).operations = 3 := rfl

def zeroPivotExpr (q r : ℚ) : RationalExpr :=
  .div (.neg (.add (.value q) (.value 1))) (.mul (.value 2) (.value r))

@[simp] theorem zeroPivotExpr_eval (q r : ℚ) :
    (zeroPivotExpr q r).eval = -(q + 1) / (2 * r) := rfl

@[simp] theorem zeroPivotExpr_operations (q r : ℚ) :
    (zeroPivotExpr q r).operations = 4 := rfl

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalExpressionHeight
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17

def RationalExpr.leaves : RationalExpr → ℕ
  | .value _ => 1
  | .add x y | .sub x y | .mul x y | .div x y => x.leaves + y.leaves
  | .neg x => x.leaves

def RationalExpr.inputsBounded (B : ℕ) : RationalExpr → Prop
  | .value q => q.num.natAbs ≤ 2 ^ B ∧ q.den ≤ 2 ^ B
  | .add x y | .sub x y | .mul x y | .div x y => x.inputsBounded B ∧ y.inputsBounded B
  | .neg x => x.inputsBounded B

theorem RationalExpr.eval_parts_le (e : RationalExpr) (B : ℕ)
    (h : e.inputsBounded B) :
    e.eval.num.natAbs ≤ 2 ^ (e.leaves * B + e.operations) ∧
      e.eval.den ≤ 2 ^ (e.leaves * B + e.operations) := by
  induction e with
  | value q => simpa [RationalExpr.eval, RationalExpr.leaves, RationalExpr.operations, RationalExpr.inputsBounded] using h
  | add x y ihx ihy =>
      have hx := ihx h.1
      have hy := ihy h.2
      have ha := KS.W30.add_parts_le_two_pow x.eval y.eval
        (x.leaves * B + x.operations) (y.leaves * B + y.operations)
        hx.1 hx.2 hy.1 hy.2
      have he : (x.leaves * B + x.operations) + (y.leaves * B + y.operations) + 1 =
          (x.leaves + y.leaves) * B + (x.operations + y.operations + 1) := by ring
      refine ⟨?_, ?_⟩
      · simpa [RationalExpr.eval, RationalExpr.leaves, RationalExpr.operations, he] using ha.1
      · apply ha.2.trans
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp only [RationalExpr.leaves, RationalExpr.operations]
        nlinarith
  | sub x y ihx ihy =>
      have hx := ihx h.1
      have hy := ihy h.2
      have hn : (-y.eval).num.natAbs ≤ 2 ^ (y.leaves * B + y.operations) ∧
          (-y.eval).den ≤ 2 ^ (y.leaves * B + y.operations) := by simpa using hy
      have ha := KS.W30.add_parts_le_two_pow x.eval (-y.eval)
        (x.leaves * B + x.operations) (y.leaves * B + y.operations)
        hx.1 hx.2 hn.1 hn.2
      have he : (x.leaves * B + x.operations) + (y.leaves * B + y.operations) + 1 =
          (x.leaves + y.leaves) * B + (x.operations + y.operations + 1) := by ring
      refine ⟨?_, ?_⟩
      · simpa [RationalExpr.eval, RationalExpr.leaves, RationalExpr.operations,
          sub_eq_add_neg, he] using ha.1
      · change (x.eval - y.eval).den ≤ _
        rw [sub_eq_add_neg]
        apply ha.2.trans
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp only [RationalExpr.leaves, RationalExpr.operations]
        nlinarith
  | mul x y ihx ihy =>
      have hx := ihx h.1
      have hy := ihy h.2
      have hm := KS.W30.mul_parts_le_two_pow x.eval y.eval
        (x.leaves * B + x.operations) (y.leaves * B + y.operations)
        hx.1 hx.2 hy.1 hy.2
      have hp : 2 ^ ((x.leaves * B + x.operations) + (y.leaves * B + y.operations)) ≤
          2 ^ ((RationalExpr.mul x y).leaves * B + (RationalExpr.mul x y).operations) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp only [RationalExpr.leaves, RationalExpr.operations]
        nlinarith
      exact ⟨hm.1.trans hp, hm.2.trans hp⟩
  | div x y ihx ihy =>
      have hx := ihx h.1
      have hy := ihy h.2
      have hd := KS.W30.div_parts_le_two_pow x.eval y.eval
        (x.leaves * B + x.operations) (y.leaves * B + y.operations)
        hx.1 hx.2 hy.1 hy.2
      have hp : 2 ^ ((x.leaves * B + x.operations) + (y.leaves * B + y.operations)) ≤
          2 ^ ((RationalExpr.div x y).leaves * B + (RationalExpr.div x y).operations) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp only [RationalExpr.leaves, RationalExpr.operations]
        nlinarith
      exact ⟨hd.1.trans hp, hd.2.trans hp⟩
  | neg x ih =>
      have hx := ih h
      have hp : 2 ^ (x.leaves * B + x.operations) ≤
          2 ^ ((RationalExpr.neg x).leaves * B + (RationalExpr.neg x).operations) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp [RationalExpr.leaves, RationalExpr.operations]
      simpa [RationalExpr.eval] using And.intro (hx.1.trans hp) (hx.2.trans hp)

end KS.W17

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_ComplexScalarCosts
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W15.ComplexMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.WireProgram KS.W01

theorem negativeOneWire_eq : negativeOneWire = encodeRat (-1) := by decide

end KS.W15.ComplexMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RetractH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p6 : NormedSpace ℝ (H d) := inferInstance

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_NormRetractH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance instNormedAddCommGroupMat_p1 : NormedAddCommGroup (Mat d) := inferInstance
local instance instNormedSpaceRealMat_p1 : NormedSpace ℝ (Mat d) := inferInstance
local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p5 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p5 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceMat_p1 : TopologicalSpace (Mat d) :=
  (inferInstance : NormedAddCommGroup (Mat d)).toUniformSpace.toTopologicalSpace
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p5 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FDerivTightPart
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p1 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormSq
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

local instance instNormedAddCommGroupPairHilbert_p1 : NormedAddCommGroup (PairHilbert d) := inferInstance
local instance instNormedSpaceRealPairHilbert_p1 : NormedSpace ℝ (PairHilbert d) := inferInstance
local instance instTopologicalSpacePairHilbert_p1 : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace

local instance instNormedAddCommGroupVars_1_p1 : NormedAddCommGroup (Vars d) := inferInstance
local instance instNormedSpaceRealVars_1_p1 : NormedSpace ℝ (Vars d) := inferInstance
local instance instTopologicalSpaceVars_p2 : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormTCoord
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p1 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace
local instance instNormedAddCommGroupPair : NormedAddCommGroup (Pair d) := inferInstance
local instance instNormedSpaceRealPair : NormedSpace ℝ (Pair d) := inferInstance
local instance instTopologicalSpacePair : TopologicalSpace (Pair d) :=
  (inferInstance : NormedAddCommGroup (Pair d)).toUniformSpace.toTopologicalSpace
local instance instNormedAddCommGroupPairHilbert_p2 : NormedAddCommGroup (PairHilbert d) := inferInstance
local instance instNormedSpaceRealPairHilbert_p2 : NormedSpace ℝ (PairHilbert d) := inferInstance
local instance instTopologicalSpacePairHilbert_p2 : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace
local instance instNormedAddCommGroupVars_1_p2 : NormedAddCommGroup (Vars d) := inferInstance
local instance instNormedSpaceRealVars_1_p2 : NormedSpace ℝ (Vars d) := inferInstance
local instance instTopologicalSpaceVars_p3 : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormPsdScalar
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}
local instance instNormedAddCommGroupVars_1_p0 : NormedAddCommGroup (Vars d) := inferInstance
local instance instNormedSpaceRealVars_1_p0 : NormedSpace ℝ (Vars d) := inferInstance
local instance instTopologicalSpaceVars_p1 : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_JetBoundInverseSandwich
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance instNormedAddCommGroupMat_p0 : NormedAddCommGroup (Mat d) := inferInstance
local instance instNormedSpaceRealMat_p0 : NormedSpace ℝ (Mat d) := inferInstance
local instance instTopologicalSpaceMat_p0 : TopologicalSpace (Mat d) :=
  (inferInstance : NormedAddCommGroup (Mat d)).toUniformSpace.toTopologicalSpace

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p2 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p2 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p2 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace


end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_JetBoundProjection
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdSubtypeMatMemSubmoduleRealH
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_2
local instance instTopologicalSpaceVars_p0 : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace
end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_UnpackKkt
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p6 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ValueBranch
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p7 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p7 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p7 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ObjectiveVarsCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p2
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p2 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
local instance instNormedAddCommGroupVars : NormedAddCommGroup (Vars d) := inferInstance
local instance instNormedSpaceRealVars : NormedSpace ℝ (Vars d) := inferInstance
local instance instTopologicalSpaceVars : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace
end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NegativeWeight
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p4
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
attribute [local instance] OAI.CurrentKS.State.negativeWeightNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.State.negativeWeightNormedSpace
local instance instTopologicalSpaceContinuousLinearMapRealIdSubtypeMatMemSubmoduleH : TopologicalSpace (H d →L[ℝ] H d) :=
  (inferInstance : NormedAddCommGroup (H d →L[ℝ] H d)).toUniformSpace.toTopologicalSpace

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PathObjectiveFirst
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State

section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

variable {d N : ℕ}
local instance instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6 : NormedAddCommGroup (H d) := inferInstance
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_p6 : NormedSpace ℝ (H d) := inferInstance
local instance instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6 : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

end
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Pivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

def pivotBlock (a : K) (b : n → K) (D : Matrix n n K) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) K :=
  Matrix.fromBlocks (scalarPivot a) (fun _ j => b j) (fun i _ => b i) D

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ChooseCoordinate
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference

open Set
open scoped ContDiff

variable {N : ℕ}

def gradientDirection [NeZero N] (g : Fin N → ℚ) : Fin N → ℝ :=
  (if 0 ≤ g (chooseCoordinate g) then (-1:ℝ) else 1) • (Pi.single (chooseCoordinate g) 1 : Fin N → ℝ)

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Pencil
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m : ℕ}

noncomputable def Pencil.realEval (B : Pencil n m) (y : Fin n → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  B.constant.map (fun x => (x : ℝ)) + ∑ i, y i • (B.coeff i).map (fun x => (x : ℝ))

def Pencil.offset (B : Pencil n m) (v : Fin m → ℚ) : ℚ :=
  - KS.W17.psdCutEval v B.constant

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RealVector
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

noncomputable def normalized (a : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  (-(l1 a : ℝ)⁻¹) • realVector a

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Feasible
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

noncomputable def Pencil.feasible (B : Pencil n m) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | (B.realEval z).PosSemidef}

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Affine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m p : ℕ}

lemma Pencil.ofAffine_eval (C : Matrix (Fin m) (Fin m) ℚ)
    (L : (Fin n → ℚ) →ₗ[ℚ] Matrix (Fin m) (Fin m) ℚ)
    (hC : C.IsSymm) (hL : ∀ y,(L y).IsSymm) (y : Fin n → ℚ) :
    (Pencil.ofAffine C L hC hL).eval y=C+L y := by
  change C+∑ i,y i • L (Pi.single i 1)=C+L y
  congr 1
  conv_rhs => rw [vector_eq_sum_single y]
  simp

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueDimension
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {d N n m p : ℕ}

variable {R : Type*} [CommRing R]

lemma schurPencil_eval (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) (v : Fin (valueDimension d) → ℚ) :
    (schurPencil coords x θ second).eval v =
    (Matrix.fromBlocks
      (timeCoordinate d v • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)+
        (if second then rationalSum coords x else -rationalSum coords x)-
        rationalEta coords θ (matrixVariable d (!second) v))
      1 1 (matrixVariable d second v)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  erw [schurPencil,Pencil.ofAffine_eval]
  ext i j
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [diagonalLinear,blockDiagonal,hi,hj,identityLinear,Matrix.add_apply,Matrix.sub_apply]
  abel

lemma lowerMatrixPencil_eval (second : Bool) (v : Fin (valueDimension d) → ℚ) :
    (lowerMatrixPencil d second).eval v = matrixVariable d second v-(1/400:ℚ) • 1 := by
  rw [lowerMatrixPencil,Pencil.ofAffine_eval]
  rw [neg_div,neg_smul]
  abel
lemma upperMatrixPencil_eval (ε : ℚ) (second : Bool) (v : Fin (valueDimension d) → ℚ) :
    (upperMatrixPencil d ε second).eval v = (200/ε:ℚ) • 1-matrixVariable d second v := by
  rw [upperMatrixPencil,Pencil.ofAffine_eval]
  simp only [LinearMap.neg_apply,sub_eq_add_neg]
lemma valueObjective_apply (ε : ℚ) (v : Fin (valueDimension d) → ℚ) :
    valueObjective d ε v = timeCoordinate d v+ε*
      (∑ i : Fin d, (matrixCoordinate d false v (i,i)+matrixCoordinate d true v (i,i))) := by
  simp [valueObjective,LinearMap.sum_apply,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PackValue
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def packValue (z : Point d) : EuclideanSpace ℝ (Fin (valueDimension d)) := WithLp.toLp 2 fun k =>
  match (valueIndex d).symm k with
  | .inl _ => z.1
  | .inr (.inl ij) => encode z.2.1 ij
  | .inr (.inr ij) => encode z.2.2 ij

def unpackValue (v : EuclideanSpace ℝ (Fin (valueDimension d))) : Point d :=
  (timeCoordinate d v,assemble (WithLp.toLp 2 (matrixCoordinate d false v)),
    assemble (WithLp.toLp 2 (matrixCoordinate d true v)))

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueObjectiveCoeffs
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma valueObjectiveCoeffs_dot (ε : ℚ) (v : Fin (valueDimension d) → ℚ) :
    valueObjectiveCoeffs d ε ⬝ᵥ v = valueObjective d ε v := by
  rw [valueObjective_apply]
  simp [valueObjectiveCoeffs,add_dotProduct,smul_dotProduct,sum_dotProduct,
    single_dotProduct,timeCoordinate,matrixCoordinate,smul_eq_mul]

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FixedPart
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N n : ℕ}

def fixedPart (e : Fin n → Fin N) (base : Coordinates N) (A : Fin N → H d) : H d :=
  ∑ i,(lookup e i).elim (base i • A i) (fun _ => 0)

end CurrentKS.RationalFace

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FaceState
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N : ℕ}

def activePotential (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (ν lam : ℚ) : Coordinates (activeIndices base).length → ℝ :=
  facePotential ((ν/(d:ℚ):ℚ):ℝ) (lam:ℝ)
    (fixedPart (activeIndex base) (fun i => (base i:ℝ)) (rationalAtoms coords))
    (fun j => rationalAtoms coords (activeIndex base j))

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters2
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

structure Parameters.Valid (p : Parameters) (n : ℕ) : Prop where
  epsilon_pos : 0 < p.ε
  epsilon_le : p.ε ≤ 1
  strip_pos : 0 < p.σ
  threshold_pos : 0 < p.a
  threshold_le : p.a ≤ 1
  bound_one : 1 ≤ p.M
  step_pos : 0 < p.s
  step_strip : p.s ≤ p.σ/4
  step_le : p.s ≤ 1/4
  step_curvature : p.M*p.s ≤ p.a/4
  stencil_pos : 0 < p.h
  stencil_strip : p.h ≤ p.σ/8
  stencil_le : p.h ≤ 1
  stencil_curvature : p.h ≤ p.a/(64*p.M*n)
  mesh_pos : 0 < p.ρ
  mesh_error : (n:ℚ)*p.ρ/2 ≤ p.s*(p.a/(1024*p.M))/8
  radius : p.s+2*p.h ≤ p.σ/2
  stencilError_pos : 0 < p.stencilError
  stencilError_le : p.stencilError ≤ 1
  selectionError_pos : 0 < p.selectionError
  selectionError_le : p.selectionError ≤ 1

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_GlobalCounts
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Schedule

section
open KS.W23
open scoped BigOperators

def X : NaturalPolynomial := .variable

def coarseP : NaturalPolynomial :=
  200+(X+1)+1+200*X^4*(X+1)+200*(X+1)+((X+1)+X)+
    384*X*(1+800*(40000*X^2)^3)
def jacobianP : NaturalPolynomial := 10^18*(X+1)*(1+X^4)^4
def derivativeP : NaturalPolynomial := 300*coarseP^5
def secondP : NaturalPolynomial := (1+2*(X+1))*(jacobianP*derivativeP*(1+jacobianP*derivativeP)^2)
def thirdP : NaturalPolynomial := (1+2*(X+1))*(jacobianP*derivativeP*
    ((1+jacobianP*derivativeP)^3+3*(1+jacobianP*derivativeP)*(jacobianP*derivativeP*(1+jacobianP*derivativeP)^2)))
def curvatureP : NaturalPolynomial :=
  1+secondP+thirdP+X*(1+800*(40000*X^2)^3)
def movementP : NaturalPolynomial :=
  1+48*(2*(1+(3*X)^2*(40000*X^4))^2*(1+3*X)^2)+4*(1+9*X^2)
def thresholdInvP : NaturalPolynomial := 512*movementP^2*(200*X^4)
def stepInvP : NaturalPolynomial := 4*(40000*X^2)+4*curvatureP*thresholdInvP+4
def dropInvP : NaturalPolynomial := 1+thresholdInvP*stepInvP^2
def iterationP : NaturalPolynomial := 100*dropInvP+1

end

open KS.W23

end CurrentKS.Schedule

namespace CurrentKS.Schedule
open KS.W23

def stencilInvP : NaturalPolynomial :=
  8*(40000*NaturalPolynomial.variable^2)+1+
    64*curvatureP*NaturalPolynomial.variable*thresholdInvP

def queryPrecisionP : NaturalPolynomial :=
  1+NaturalPolynomial.variable+NaturalPolynomial.variable^4+
    512*NaturalPolynomial.variable*thresholdInvP*stencilInvP^2+
    16*thresholdInvP*stepInvP^2

end CurrentKS.Schedule

namespace CurrentKS.RationalSDP
open KS.W23 CurrentKS.Schedule CurrentKS.Hermitian CurrentKS.State
open scoped BigOperators

variable {d N : ℕ}

def valueScanP (p : NaturalPolynomial) : NaturalPolynomial :=
  let dim := 1+2*p^2
  let R := (dim+1)*(100+400*p*(p+1))
  let L := (dim+1)*(1+2*p)
  let rInv := 4000*(p^2+1)
  let nearInv := L*(2*R+1)*p*rInv
  (200*p+4)*(4*R^2*(nearInv*(dim+1))^2+1)

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Model
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS

def toComplex (z : RationalComplex) : ℂ :=
  ⟨(z.1.value : ℝ), (z.2.value : ℝ)⟩

def Input.matrix (x : Input) (i : Fin x.N) : Matrix (Fin x.d) (Fin x.d) ℂ :=
  (x.entries i).map toComplex

def Admissible (x : Input) : Prop :=
  ∀ i, (x.matrix i).IsHermitian ∧ (x.matrix i).rank ≤ 1

noncomputable def signedSum (x : Input) (bits : List Bool) :
    Matrix (Fin x.d) (Fin x.d) ℂ :=
  ∑ i, signValue (bits.getD i.val false) • x.matrix i

noncomputable def variance (x : Input) : Matrix (Fin x.d) (Fin x.d) ℂ :=
  ∑ i, x.matrix i * x.matrix i

def GoodOutput (x : Input) (bits : List Bool) : Prop :=
  bits.length = x.N ∧ opNorm (signedSum x bits) ≤ 40 * Real.sqrt (opNorm (variance x))

end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FrameWireCodec
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FrameWireCodec
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers registers_port registers_other)

theorem frame_rat_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (q : ℚ) :
    RunSpec (frameProgram ports) (registers ports spare [] (KS.W01.encodeRat q) [])
      (registers ports spare [] (KS.W01.frame (KS.W01.encodeRat q)) [])
      (4 * (KS.W01.encodeRat q).length + 3) := frame_spec ports spare _

end KS.W11.FrameWireCodec

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W23.NaturalPolynomial

def comp : NaturalPolynomial → NaturalPolynomial → NaturalPolynomial
  | .constant n,_ => .constant n
  | .variable,q => q
  | .add p r,q => p.comp q+r.comp q
  | .mul p r,q => p.comp q*r.comp q
  | .power p n,q => (p.comp q)^n
@[simp] lemma eval_comp (p q : NaturalPolynomial) (x : ℕ) : (p.comp q).eval x=p.eval (q.eval x) := by
  induction p with
  | constant n => rfl
  | «variable» => rfl
  | add p r hp hr => simp only [comp,eval,eval_add,hp,hr]
  | mul p r hp hr => simp only [comp,eval,eval_mul,hp,hr]
  | power p n hp => simp only [comp,eval,eval_power,hp]
end KS.W23.NaturalPolynomial

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word} {ed : δ → Word}
  {f : α → β} {g : β → γ}

class PolyTime (r : Realizes ea eb f) : Prop where
  bound : ∃ p : NaturalPolynomial,∀ x,r.cost x≤p.eval (ea x).length

instance poly_identity (ea : α → Word) : PolyTime (identity ea) := ⟨⟨1,fun _ => le_rfl⟩⟩
instance poly_constant (ea : α → Word) (eb : β → Word) (y : β) : PolyTime (constant ea eb y) :=
  ⟨⟨X+NaturalPolynomial.constant ((eb y).length+2),by intro x;change (ea x).length+1+((eb y).length+1)≤_;simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_constant];omega⟩⟩
instance poly_congr {g : α → β} (r : Realizes ea eb f) (h : ∀ x,f x=g x) [PolyTime r] :
    PolyTime (r.congr h) := by
  have he : f=g := funext h
  subst g
  exact ‹PolyTime r›
instance poly_changeOutput (r : Realizes ea eb f) (ed : δ → Word) (g : α → δ)
    (h : ∀ x,eb (f x)=ed (g x)) [PolyTime r] : PolyTime (r.changeOutput ed g h) :=
  ⟨PolyTime.bound (r:=r)⟩
instance poly_reindex (r : Realizes ea eb f) (ed : δ → Word) (g : δ → α)
    (h : ∀ x,ed x=ea (g x)) [PolyTime r] : PolyTime (r.reindex ed g h) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  refine ⟨⟨p,?_⟩⟩
  intro x
  simp only [h x]
  exact hp (g x)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ListRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ : Type*}

lemma listCode_append (ea : α → Word) (xs ys : List α) :
    listCode ea (xs++ys)=listCode ea xs++listCode ea ys := by
  simp only [listCode,FramedMapRoutine.tape,List.flatMap_append]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLoops
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {α β γ : Type*} {ea : α → Word} {eb : β → Word}

class FoldSize {f : α×β → α} (r : Realizes (prodCode ea eb) ea f) : Prop where
  bound : ∃ p : NaturalPolynomial,∀ s xs ys zs,xs=ys++zs →
    (ea (ys.foldl (fun a b => f (a,b)) s)).length ≤ p.eval (prodCode ea (listCode eb) (s,xs)).length

class IterateSize {f : α → α} (r : Realizes ea ea f) : Prop where
  bound : ∃ p : NaturalPolynomial,∀ x n,(ea (f^[n] x)).length≤p.eval ((ea x).length+n)
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ExpressionSyntax
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W13.ExpressionMachine
open KS.W17

@[simp] theorem encodeOps_append (ops rest : List Op) :
    encodeOps (ops++rest) = encodeOps ops ++ encodeOps rest := by simp [encodeOps]

end KS.W13.ExpressionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLists
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

instance poly_consList (ea : α → Word) : PolyTime (consList ea) := by
  unfold consList
  apply poly_changeOutput

instance poly_natSucc : PolyTime natSucc := ⟨⟨1,fun _ => le_rfl⟩⟩
instance poly_natPred : PolyTime natPred := ⟨⟨1,fun _ => le_rfl⟩⟩
instance poly_natIsZero : PolyTime natIsZero := by
  refine ⟨⟨X+6,?_⟩⟩
  intro n
  change n+6≤(X+6).eval (natCode n).length
  simp only [natCode,List.length_replicate]
  exact Nat.le_refl _

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VectorRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α β γ : Type*}

def Realizes.findValue {ec : γ → Word} {ea : α → Word} {eb : β → Word}
    {p : γ×α → Bool} {f : γ×α → β}
    (test : Realizes (prodCode ec ea) boolCode p) (value : Realizes (prodCode ec ea) eb f) :
    Realizes (prodCode ec (prodCode eb (listCode ea))) eb
      (fun input => (input.2.2.find? (fun item => p (input.1,item))).elim input.2.1
        (fun item => f (input.1,item))) :=
  let context := first ec (prodCode eb (listCode ea))
  let rest := second ec (prodCode eb (listCode ea))
  let initial := rest.then (first eb (listCode ea))
  let values := rest.then (second eb (listCode ea))
  let previous := first (prodCode ec eb) ea
  let contextValue := (previous.then (first ec eb)).both (second (prodCode ec eb) ea)
  let body := (previous.then (first ec eb)).both
    ((contextValue.then test).ite (contextValue.then value) (previous.then (second ec eb)))
  let loop := ((context.both initial).both (values.then (reverseList ea))).then body.fold
  (loop.then (second ec eb)).congr (by
    intro input
    have foldPair : ∀ (items : List α) (initialValue : β),
        items.foldl (fun state item =>
          (state.1,if p (state.1,item) then f (state.1,item) else state.2))
            (input.1,initialValue) =
        (input.1,items.foldl (fun result item =>
          if p (input.1,item) then f (input.1,item) else result) initialValue) := by
      intro items
      induction items with
      | nil => intro initialValue; rfl
      | cons item items inductionHypothesis =>
        intro initialValue
        simpa only [List.foldl_cons] using inductionHypothesis _
    rw [foldPair,List.foldl_reverse]
    exact chooseFold_find _ _ _ _)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMatrixFold
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

def MatrixParts (H : ℕ) (M : MatrixData) : Prop := ∀row∈M,∀q∈row,QParts H q

def MatrixShape (L : ℕ) (M : MatrixData) : Prop := M.length≤L ∧ ∀row∈M,row.length≤L

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_UnaryLengthMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W28.UnaryLength
open KS.W29

def dispatch (_ : Fin 1) (heads : Fin 27) (_coin : Bool) : Instruction 1 :=
  if heads.val % 3 = 0 then ⟨none, .stay, .stay, .stay⟩
  else ⟨some 0, .pop, .push true, .stay⟩
def machine : BinaryMachine := FiniteDispatch.compile 0 dispatch

def cfg (state : Option (Fin 1)) (xs ys zs : List Bool) : Config 1 := ⟨state, ![xs,ys,zs]⟩

theorem head_zero (state : Option (Fin 1)) (xs ys zs : List Bool) :
    headCode (cfg state xs ys zs) % 3 = topCode xs := by
  have hx := topCode_lt_three xs
  have hy := topCode_lt_three ys
  have hz := topCode_lt_three zs
  change (topCode xs + 3 * topCode ys + 9 * topCode zs) % 3 = topCode xs
  omega

theorem step_cons (a coin : Bool) (xs ys zs : List Bool) :
    machine.step (cfg (some 0) (a::xs) ys zs) coin = cfg (some 0) xs (true::ys) zs := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  have hh := head_zero (some 0) (a::xs) ys zs
  change headCode (Config.mk (some (0 : Fin 1)) ![a::xs,ys,zs]) % 3 = topCode (a::xs) at hh
  simp only [dispatch]
  erw [hh]
  cases a <;> change Config.mk (some (0 : Fin 1)) _ = Config.mk (some (0 : Fin 1)) _
  all_goals
    apply congrArg (Config.mk (some (0 : Fin 1)))
    funext j
    fin_cases j <;> rfl

theorem step_empty (ys zs : List Bool) (coin : Bool) :
    machine.step (cfg (some 0) [] ys zs) coin = cfg none [] ys zs := by
  unfold machine
  erw [FiniteDispatch.step_compile]
  have hh := head_zero (some 0) [] ys zs
  change headCode (Config.mk (some (0 : Fin 1)) ![[],ys,zs]) % 3 = topCode [] at hh
  simp only [dispatch]
  erw [hh]
  change Config.mk none _ = Config.mk none _
  apply congrArg (Config.mk none)
  funext j
  fin_cases j <;> rfl

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers registers_other)

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k := ofMachine (lift3 machine ports)

end KS.W28.UnaryLength

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RootRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev rootStateCode := prodCode ratCode (prodCode ratCode ratCode)

lemma square_iterate (q : ℚ) (k : ℕ) :
    (rootStep 2)^[k] (q,(0,1))=(q,RationalRoot.squareInterval q k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih];rfl
lemma cube_iterate (q : ℚ) (k : ℕ) :
    (rootStep 3)^[k] (q,(0,1))=(q,Scalar.cubeInterval q k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih];rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_MatrixStructureRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

variable {α : Type*}

def fromBlocksData (p : (MatrixData×MatrixData)×(MatrixData×MatrixData)) : MatrixData :=
  zipDefault (fun q : List ℚ×List ℚ => q.1++q.2) [] [] p.1 ++
  zipDefault (fun q : List ℚ×List ℚ => q.1++q.2) [] [] p.2

lemma fromBlocks_data {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin m) ℚ) (C : Matrix (Fin m) (Fin n) ℚ)
    (D : Matrix (Fin m) (Fin m) ℚ) :
    fromBlocksData ((matrixData A,matrixData B),(matrixData C,matrixData D))=
      matrixData ((Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  unfold fromBlocksData matrixData
  rw [zipDefault_ofFn,zipDefault_ofFn,ofFn_sum]
  congr 1 <;> apply congrArg List.ofFn <;> funext i <;> rw [ofFn_sum] <;>
    simp [Matrix.submatrix]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceArrayRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

lemma activeData_data {N : ℕ} (x : Fin N → ℚ) :
    activeData (List.ofFn x)=(RationalFace.activeIndices x).map Fin.val := by
  unfold activeData RationalFace.activeIndices
  rw [List.length_ofFn,range_finRange,List.filter_map]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [Function.comp_apply,getD_ofFn]

abbrev extendDataCode := prodCode indicesCode (prodCode vectorCode vectorCode)

lemma extendEntry_data {N n : ℕ} (e : Fin n → Fin N) (base : Fin N → ℚ) (y : Fin n → ℚ) (i : Fin N) :
    extendEntryData ((List.ofFn (fun j => (e j).val),(List.ofFn base,List.ofFn y)),i.val)=
      RationalFace.extend e base y i := by
  unfold extendEntryData RationalFace.extend RationalFace.lookup
  rw [List.length_ofFn,range_finRange,List.find?_map,getD_ofFn]
  have hp : (fun j : Fin n => (List.ofFn fun j => (e j).val).getD j.val 0==i.val)=
      fun j => e j==i := by
    funext j
    rw [getD_ofFn]
    simp [Fin.ext_iff]
  change (((List.finRange n).find? (fun j : Fin n => (List.ofFn fun j => (e j).val).getD j.val 0==i.val)).map Fin.val).elim (base i) (fun j => (List.ofFn y).getD j 0)=_
  rw [hp]
  cases hh : (List.finRange n).find? (fun j => e j==i) with
  | none => rfl
  | some j => simp

lemma extendData_data {N n : ℕ} (e : Fin n → Fin N) (base : Fin N → ℚ) (y : Fin n → ℚ) :
    extendData (List.ofFn (fun j => (e j).val),(List.ofFn base,List.ofFn y))=
      List.ofFn (RationalFace.extend e base y) := by
  unfold extendData
  rw [List.length_ofFn,range_map_fin]
  apply congrArg List.ofFn
  funext i
  exact extendEntry_data e base y i

lemma activeIndex_data {N : ℕ} (x : Fin N → ℚ) :
    activeData (List.ofFn x)=List.ofFn (fun j => (RationalFace.activeIndex x j).val) := by
  rw [activeData_data]
  symm
  change List.ofFn (Fin.val ∘ (RationalFace.activeIndices x).get)=_
  rw [←List.map_ofFn,List.ofFn_get]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SparseCoefficientStage
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SparseCoefficientStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.ComplexMachine

def put (s : Fin 35 → List Bool) (p : Fin 35) (q : ℚ) : Fin 35 → List Bool :=
  Function.update s p (KS.W01.encodeRat q)
def after (s : Fin 35 → List Bool) (a b : ℚ) : Fin 35 → List Bool :=
  put (put (put (put (put (put s 24 1) 25 2) 21 (a+1)) 22 (2*b)) 27 (-(a+1)))
    28 (SparseScalarNodes.coefficient a b)

def result (s : Fin 35 → List Bool) (a b : ℚ) : Fin 35 → List Bool :=
  Function.update (KS.W04.CleanRationalCompare.clearListState cleanupPorts s) 28
    (KS.W01.encodeRat (SparseScalarNodes.coefficient a b))

end KS.W19.SparseCoefficientStage

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireAppend
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.WireAppend

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem move_spec {k : ℕ} (source target : Fin k) (hst : source ≠ target)
    (before : Fin k → List Bool) :
    RunSpec (KS.W04.BinaryStackMoves.moveProgram source target) before
      (moveAfter source target before) ((before source).length+1) := by
  intro bits hbits
  exact KS.W04.BinaryStackMoves.run_move_stacks source target hst before bits hbits

end KS.W07.WireAppend

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayPrefix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack
open KS.W29 (StackAction)
open KS.W29.FixedSequential

def config {q : ℕ} (state : Option (Fin q))
    (src replacement «prefix» scratch index : List Bool) : Config 5 q :=
  ⟨state, «stacks» src replacement «prefix» scratch index⟩

theorem config_ext {q : ℕ} {c d : Config 5 q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ZeroArrayConstructor
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.ZeroArrayConstructor
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem config_ext {q : ℕ} {c d : Config 3 q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

end KS.W11.ZeroArrayConstructor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SavedPivotPacketMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08.SavedPivotPacket
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers)

theorem frame_at {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (payload : List Bool) (h0 : before (ports 0) = []) (h1 : before (ports 1) = payload)
    (h2 : before (ports 2) = []) :
    RunSpec (KS.W11.FrameWireCodec.frameProgram ports) before
      (Function.update before (ports 1) (KS.W01.frame payload)) (4 * payload.length + 3) := by
  have h := KS.W11.FrameWireCodec.frame_spec ports before payload
  have hi : registers ports before [] payload [] = before := by
    funext j
    by_cases hj0 : j = ports 0
    · subst j; simp [registers, h0]
    · by_cases hj1 : j = ports 1
      · subst j; simp [registers, hj0, h1]
      · by_cases hj2 : j = ports 2
        · subst j; simp [registers, hj0, hj1, h2]
        · simp [registers, hj0, hj1, hj2]
  have ho : registers ports before [] (KS.W01.frame payload) [] =
      Function.update before (ports 1) (KS.W01.frame payload) := by
    funext j
    by_cases hj0 : j = ports 0
    · subst j; simp [registers, Function.update, h0, ports.injective.eq_iff]
    · by_cases hj1 : j = ports 1
      · subst j; simp [registers, hj0, Function.update]
      · by_cases hj2 : j = ports 2
        · subst j; simp [registers, hj0, hj1, h2, Function.update]
        · simp [registers, hj0, hj1, hj2, Function.update]
  rw [hi, ho] at h
  exact h

end KS.W08.SavedPivotPacket

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurCellMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurCellMachine

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem first_spec {n : ℕ} (hn : n ≤ 23) (P : Program n)
    (before after : Fin n → List Bool) (spare : Fin 23 → List Bool) (ticks : ℕ)
    (h : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P (firstPorts n hn))
      (extend before spare) (extend after spare) ticks := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec P (firstPorts n hn) _ _ _ _ _ h
  · intro i; simp [extend, firstPorts, i.isLt]
  · intro i; simp [extend, firstPorts, i.isLt]
  · intro j hj
    by_cases hb : j.val < n
    · exact (hj ⟨j.val, hb⟩ (Fin.ext rfl)).elim
    · simp [extend, hb]

end KS.W07.SchurCellMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_StoredPSDRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

lemma matrixData_flatten {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    (matrixData M).flatten=List.ofFn (fun k : Fin (n*n) => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*n+j.val,KS.W08.matrixEntryIndex_lt i j⟩ : Fin (n*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [he,Equiv.symm_apply_apply]

def witnessData (a : MatrixObject) : List ℚ :=
  (KS.W17.rationalNegativeWitness a.1 a.2).elim [] List.ofFn

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScheduleRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*} {ea : α → Word} {f g : α → ℚ}

abbrev scheduleArgsCode := prodCode natCode (prodCode natCode (prodCode ratCode ratCode))
def saD := first natCode (prodCode natCode (prodCode ratCode ratCode))
def saRest := second natCode (prodCode natCode (prodCode ratCode ratCode))
def saN := saRest.then (first natCode (prodCode ratCode ratCode))
def saScalars := saRest.then (second natCode (prodCode ratCode ratCode))
def saNu := saScalars.then (first ratCode ratCode)
def saLam := saScalars.then (second ratCode ratCode)
def parametersData (p : Schedule.Parameters) := [p.ε,p.σ,p.a,p.M,p.s,p.h,p.ρ,p.stencilError,p.selectionError]
def parametersCode (p : Schedule.Parameters) : Word := vectorCode (parametersData p)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CoordinateRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def reEntryData (p : (MatrixData×ℕ)×ℕ) : ℚ :=
  if p.1.2 ≤ p.2 then (p.1.1.getD p.1.2 []).getD p.2 0 else (p.1.1.getD p.2 []).getD p.1.2 0

def imEntryData (p : (MatrixData×ℕ)×ℕ) : ℚ :=
  if p.1.2 < p.2 then (p.1.1.getD p.2 []).getD p.1.2 0 else
    if p.2 < p.1.2 then -(p.1.1.getD p.1.2 []).getD p.2 0 else 0

def squareTabData (f : (MatrixData×ℕ)×ℕ → ℚ) (p : ℕ×MatrixData) : MatrixData :=
  (List.range p.1).map (fun i => (List.range p.1).map (fun j => f ((p.2,i),j)))

def realDecodeData (p : ℕ×MatrixData) : MatrixData :=
  let re := squareTabData reEntryData p
  let im := squareTabData imEntryData p
  fromBlocksData ((re,im.map (fun row => row.map (fun x => -x))),(im,re))

lemma reEntry_data {d : ℕ} (x : Fin d×Fin d → ℚ) (i j : Fin d) :
    reEntryData ((matrixData (fun i j => x (i,j)),i.val),j.val)=x (min i j,max i j) := by
  unfold reEntryData matrixData
  rw [getD_ofFn,getD_ofFn,getD_ofFn,getD_ofFn]
  by_cases h : i ≤ j
  · simp [h,show i.val ≤ j.val from h]
  · have h' : j ≤ i := le_of_not_ge h
    simp [min_eq_right h',max_eq_left h',show ¬i.val ≤ j.val from h]

lemma imEntry_data {d : ℕ} (x : Fin d×Fin d → ℚ) (i j : Fin d) :
    imEntryData ((matrixData (fun i j => x (i,j)),i.val),j.val)=
      (if i < j then x (j,i) else if j < i then -x (i,j) else 0) := by
  unfold imEntryData matrixData
  rw [getD_ofFn,getD_ofFn,getD_ofFn,getD_ofFn]
  rfl

lemma squareTab_data {d : ℕ} (f : (MatrixData×ℕ)×ℕ → ℚ) (x : Fin d×Fin d → ℚ) :
    squareTabData f (d,matrixData (fun i j => x (i,j)))=
      matrixData (fun i j : Fin d => f ((matrixData (fun i j => x (i,j)),i.val),j.val)) := by
  simp only [squareTabData,range_map_fin,matrixData]

lemma realDecode_data {d : ℕ} (x : Fin d×Fin d → ℚ) :
    realDecodeData (d,matrixData (fun i j => x (i,j)))=matrixData (RationalSDP.realFinDecode d x) := by
  simp only [realDecodeData,squareTab_data,reEntry_data,imEntry_data]
  have hn (M : Matrix (Fin d) (Fin d) ℚ) :
      (matrixData M).map (fun row => row.map (fun x => -x))=matrixData (-M) := by
    simp only [matrixData,List.map_ofFn,Function.comp_def];rfl
  erw [hn,fromBlocks_data]
  rfl

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_LevelPencilRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α : Type*}
def singletonList (ea : α → Word) : Realizes ea (listCode ea) (fun x => [x]) :=
  ((identity ea).both (constant ea (listCode ea) [])).then (consList ea)

def blockScalarData (p : MatrixData×ℚ) : MatrixData :=
  p.1.map (fun row => row++[0]) ++ [List.replicate p.1.length 0++[p.2]]

lemma blockScalar_data {m : ℕ} (M : Matrix (Fin m) (Fin m) ℚ) (q : ℚ) :
    blockScalarData (matrixData M,q)=matrixData (RationalSDP.blockScalar M q) := by
  unfold blockScalarData matrixData
  simp only [List.map_ofFn,Function.comp_def,List.length_ofFn]
  rw [List.ofFn_succ_last]
  congr 1
  · apply congrArg List.ofFn
    funext i
    rw [List.ofFn_succ_last]
    simp [RationalSDP.blockScalar,Matrix.submatrix,finSumFinEquiv_symm_apply_castSucc]
  · congr 1
    rw [List.ofFn_succ_last]
    simp only [RationalSDP.blockScalar,Matrix.submatrix,Matrix.of_apply,finSumFinEquiv_symm_last,
      finSumFinEquiv_symm_apply_castSucc,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply,List.ofFn_const]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PencilCompileRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def zeroRect : Realizes (prodCode natCode natCode) matrixCode
    (fun p => List.replicate p.1 (List.replicate p.2 (0:ℚ))) :=
  let n := first natCode natCode
  let m := second natCode natCode
  let row := ((constant _ ratCode 0).both m).then (replicateList ratCode)
  (row.both n).then (replicateList vectorCode)

lemma zeroRect_data (n m : ℕ) :
    List.replicate n (List.replicate m (0:ℚ))=matrixData (0 : Matrix (Fin n) (Fin m) ℚ) := by
  change _=List.ofFn (fun _ : Fin n => List.ofFn (fun _ : Fin m => (0:ℚ)))
  simp

def blockDiagonalData (p : MatrixData×MatrixData) : MatrixData :=
  fromBlocksData ((p.1,List.replicate p.1.length (List.replicate p.2.length 0)),
    (List.replicate p.2.length (List.replicate p.1.length 0),p.2))
lemma blockDiagonal_data {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin m) (Fin m) ℚ) :
    blockDiagonalData (matrixData A,matrixData B)=matrixData (RationalSDP.blockDiagonal A B) := by
  unfold blockDiagonalData
  simp only [matrixData,List.length_ofFn]
  change fromBlocksData ((matrixData A,_),(_,matrixData B))=_
  rw [zeroRect_data,zeroRect_data,fromBlocks_data]
  rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_SelectionRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*}

abbrev scoredCode (ea : α → Word) := prodCode ea ratCode
lemma selectScored_data (score : α → ℚ) (e : α → β) (xs : List α) (a : α) :
    (xs.map (fun x => (e x,score x))).foldl (fun s x => betterData (s,x)) (e a,score a)=
      (e (Descent.select score a xs),score (Descent.select score a xs)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,Descent.select,betterData]
    split_ifs <;> exact ih _

lemma select_map (f : α → β) (score : β → ℚ) (xs : List α) (a : α) :
    Descent.select score (f a) (xs.map f)=f (Descent.select (score ∘ f) a xs) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,Descent.select,Function.comp_apply]
    split_ifs <;> exact ih _

def chooseCoordinateData (xs : List ℚ) : ℕ :=
  Descent.select (fun i => -|xs.getD i 0|) 0 (List.range xs.length)
lemma chooseCoordinate_data {n : ℕ} [NeZero n] (g : Fin n → ℚ) :
    chooseCoordinateData (List.ofFn g)=(Difference.chooseCoordinate g).val := by
  unfold chooseCoordinateData Difference.chooseCoordinate
  rw [List.length_ofFn,range_finRange]
  change Descent.select (fun i => -|(List.ofFn g).getD i 0|) (0 : Fin n).val
    ((List.finRange n).map Fin.val)=_
  rw [select_map]
  have hs : ((fun i => -|(List.ofFn g).getD i 0|) ∘ Fin.val)=(fun i : Fin n => -|g i|) := by
    funext i
    exact congrArg (fun q : ℚ => -|q|) (getD_ofFn g i 0)
  rw [hs]

def gradientDirectionData (xs : List ℚ) : List ℚ :=
  (basisData (xs.length,chooseCoordinateData xs)).map
    (fun q => (if 0≤xs.getD (chooseCoordinateData xs) 0 then (-1:ℚ) else 1)*q)
lemma gradientDirection_data {n : ℕ} [NeZero n] (g : Fin n → ℚ) :
    gradientDirectionData (List.ofFn g)=List.ofFn (Difference.rationalGradientDirection g) := by
  unfold gradientDirectionData
  rw [List.length_ofFn,chooseCoordinate_data,basis_data,getD_ofFn]
  simp only [List.map_ofFn,Function.comp_def,Difference.rationalGradientDirection]
  rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_WitnessRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

structure WitnessState where
  n : ℕ
  m : ℕ
  B : RationalSDP.Pencil n m
  y : Fin n → ℚ

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OptimizeRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

structure OptParams where
  n : ℕ
  m : ℕ
  B : RationalSDP.Pencil n m
  f : Fin n → ℚ
  delta : ℚ
  r : ℚ
  R : ℚ
  U : ℚ
abbrev optScalarsCode := prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode))

structure OptState where
  p : OptParams
  k : ℕ
  y : Fin p.n → ℚ

def optStateData (s : OptState) := (s.p,(s.k,List.ofFn s.y))
def OptState.feasibility (s : OptState) : WitnessState :=
  ⟨s.p.n,s.p.m+1,s.p.B.withLevel s.p.f (RationalSDP.level s.p.delta s.p.U s.k),s.y⟩

def OptState.next (s : OptState) : OptState :=
  ⟨s.p,s.k+1,if (s.p.B.withLevel s.p.f (RationalSDP.level s.p.delta s.p.U s.k)).witness s.y=none
    then s.y else s.p.B.levelCandidate s.p.f s.p.delta s.p.r s.p.R s.p.U (s.k+1)⟩

def OptParams.init (p : OptParams) : OptState :=
  ⟨p,0,p.B.levelCandidate p.f p.delta p.r p.R p.U 0⟩

lemma opt_iterate (p : OptParams) (k : ℕ) :
    OptState.next^[k] p.init=⟨p,k,p.B.optimize p.f p.delta p.r p.R p.U k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih];rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueDataRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

abbrev ValueData := ℕ×(List MatrixData×(List ℚ×(List ℚ×ℚ)))
abbrev valueDataCode := prodCode natCode (prodCode (listCode matrixCode)
  (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdD := first natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdRest := Realization.second natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdAtoms := vdRest.then (first (listCode matrixCode) (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdParams := vdRest.then (second (listCode matrixCode) (prodCode vectorCode (prodCode vectorCode ratCode)))
def vdX := vdParams.then (first vectorCode (prodCode vectorCode ratCode))
def vdTheta := vdParams.then ((second vectorCode (prodCode vectorCode ratCode)).then (first vectorCode ratCode))
def vdEps := vdParams.then ((second vectorCode (prodCode vectorCode ratCode)).then (second vectorCode ratCode))

def valueData {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) : ValueData :=
  (d,(List.ofFn (fun i => matrixData (RationalSDP.realFinDecode d (coords i))),
    (List.ofFn x,(List.ofFn θ,ε))))

abbrev matrixVarCode := prodCode natCode vectorCode

lemma coordinateIndex_value {d : ℕ} (second : Bool) (i j : Fin d) :
    coordinateIndex second ((d,i.val),j.val)=
      (RationalSDP.valueIndex d (.inr (if second then .inr (i,j) else .inl (i,j)))).val := by
  cases second
  · change 1+0+(j.val+d*i.val)=1+(j.val+d*i.val)
    omega
  · change 1+d*d+(j.val+d*i.val)=1+(d*d+(j.val+d*i.val))
    omega

def coordinateData (second : Bool) (p : ℕ×List ℚ) : MatrixData :=
  (List.range p.1).map (fun i => (List.range p.1).map
    (fun j => p.2.getD (coordinateIndex second ((p.1,i),j)) 0))

def matrixVariableData (second : Bool) (p : ℕ×List ℚ) :=
  realDecodeData (p.1,coordinateData second p)

lemma coordinates_data {d : ℕ} (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    coordinateData second (d,List.ofFn y)=
      matrixData (fun i j => RationalSDP.matrixCoordinate d second y (i,j)) := by
  unfold coordinateData
  simp only [range_map_fin,matrixData]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [coordinateIndex_value,getD_ofFn]
  rfl
lemma matrixVariable_data {d : ℕ} (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    matrixVariableData second (d,List.ofFn y)=matrixData (RationalSDP.matrixVariable d second y) := by
  rw [matrixVariableData,coordinates_data,realDecode_data]
  rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueEvalRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

abbrev ValueEvalData := ValueData×List ℚ
abbrev valueEvalCode := prodCode valueDataCode vectorCode
def veP := first valueDataCode vectorCode
def veY := second valueDataCode vectorCode
def veD := veP.then vdD
def veEps := veP.then vdEps

lemma time_getD {d : ℕ} (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    (List.ofFn y).getD 0 0=RationalSDP.timeCoordinate d y := by
  have h : (RationalSDP.valueIndex d (.inl 0)).val=0 := rfl
  rw [← h,getD_ofFn]
  rfl

def tinyMatrix : Realizes ratCode matrixCode (fun q => [[q]]) :=
  (singletonList ratCode).then (singletonList vectorCode)
lemma tinyMatrix_data (q : ℚ) : [[q]]=matrixData (q • (1 : Matrix (Fin 1) (Fin 1) ℚ)) := by
  simp [matrixData,List.ofFn_succ]

lemma pencil_blockDiagonal_eval {n m p : ℕ} (A : RationalSDP.Pencil n m) (B : RationalSDP.Pencil n p)
    (z : Fin n → ℚ) : (A.blockDiagonal B).eval z=RationalSDP.blockDiagonal (A.eval z) (B.eval z) := by
  ext i j
  simp only [RationalSDP.Pencil.eval,RationalSDP.Pencil.blockDiagonal,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [RationalSDP.blockDiagonal,hi,hj,Matrix.sum_apply]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueObjectiveRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def traceData (M : MatrixData) : ℚ :=
  ((List.range M.length).map (fun i => (M.getD i []).getD i 0)).sum

lemma trace_data {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : traceData (matrixData A)=Matrix.trace A := by
  unfold traceData matrixData
  simp only [List.length_ofFn,range_map_fin]
  have h : (fun i : Fin n => ((List.ofFn fun i => List.ofFn (A i)).getD i.val []).getD i.val 0)=
      fun i => A i i := by
    funext i
    rw [getD_ofFn,getD_ofFn]
  rw [h,List.sum_ofFn]
  rfl

def valueObjectiveData (p : ValueEvalData) : ℚ :=
  p.2.getD 0 0 + p.1.2.2.2.2*(traceData (coordinateData false (p.1.1,p.2))+
    traceData (coordinateData true (p.1.1,p.2)))
lemma valueObjective_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    valueObjectiveData (valueData coords x θ ε,List.ofFn y)=RationalSDP.valueObjective d ε y := by
  unfold valueObjectiveData
  change (List.ofFn y).getD 0 0+ε*(traceData (coordinateData false (d,List.ofFn y))+
    traceData (coordinateData true (d,List.ofFn y)))=_
  erw [time_getD,coordinates_data,coordinates_data,trace_data,trace_data,RationalSDP.valueObjective_apply]
  simp only [Matrix.trace,Matrix.diag,Finset.sum_add_distrib]

def valueCoeffsData (p : ValueData) : List ℚ :=
  (List.range (RationalSDP.valueDimension p.1)).map
    (fun i => valueObjectiveData (p,basisData (RationalSDP.valueDimension p.1,i)))
lemma valueCoeffs_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) :
    valueCoeffsData (valueData coords x θ ε)=List.ofFn (RationalSDP.valueObjectiveCoeffs d ε) := by
  unfold valueCoeffsData
  change (List.range (RationalSDP.valueDimension d)).map _=_
  rw [range_map_fin]
  apply congrArg List.ofFn
  funext i
  erw [basis_data]
  exact (valueObjective_data coords x θ ε (Pi.single i (1:ℚ))).trans (by
    simpa using (RationalSDP.valueObjectiveCoeffs_dot ε (Pi.single i (1:ℚ))).symm)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueQueryRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev valueQueryDataCode := prodCode valueDataCode ratCode

def ValueQueryParams.data (p : ValueQueryParams) :=
  (valueData p.coords p.x p.theta (p.nu/p.d),p.delta)
def valueQueryCode (p : ValueQueryParams) : Word := valueQueryDataCode p.data
def vqView : Realizes valueQueryCode valueQueryDataCode ValueQueryParams.data :=
  (identity valueQueryDataCode).reindex valueQueryCode ValueQueryParams.data (fun _ => rfl)
def vqData : Realizes valueQueryCode valueDataCode
    (fun p => valueData p.coords p.x p.theta (p.nu/p.d)) :=
  vqView.then (first valueDataCode ratCode)
def vqDelta : Realizes valueQueryCode ratCode ValueQueryParams.delta :=
  vqView.then (second valueDataCode ratCode)

def ValueQueryParams.opt (p : ValueQueryParams) : OptParams :=
  let ε := p.nu/p.d
  let L := RationalSDP.valueLipschitz p.d ε
  let R := RationalSDP.valueOuterRadius p.d ε
  let r := RationalSDP.valueInnerRadius p.d
  ⟨RationalSDP.valueDimension p.d,_,
    RationalSDP.valuePencil p.coords p.x p.theta ε,
    RationalSDP.valueObjectiveCoeffs p.d ε,p.delta,
    RationalSDP.nearRadius p.delta L R r,R,100⟩

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PotentialRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

abbrev potentialScalarsCode := prodCode ratCode (prodCode ratCode ratCode)
abbrev potentialDataCode := prodCode natCode (prodCode (listCode matrixCode) (prodCode vectorCode potentialScalarsCode))
def PotentialParams.data (p : PotentialParams) :=
  (p.d,(List.ofFn (fun i => matrixData (RationalSDP.realFinDecode p.d (p.coords i))),
    (List.ofFn p.x,(p.nu,(p.lam,p.error)))))
def potentialCode (p : PotentialParams) : Word := potentialDataCode p.data
def potentialView : Realizes potentialCode potentialDataCode PotentialParams.data :=
  (identity potentialDataCode).reindex potentialCode PotentialParams.data (fun _ => rfl)
def ppD : Realizes potentialCode natCode PotentialParams.d :=
  potentialView.then (first natCode (prodCode (listCode matrixCode) (prodCode vectorCode potentialScalarsCode)))
def ppRest := potentialView.then (second natCode (prodCode (listCode matrixCode) (prodCode vectorCode potentialScalarsCode)))
def ppAtoms := ppRest.then (first (listCode matrixCode) (prodCode vectorCode potentialScalarsCode))
def ppArgs := ppRest.then (second (listCode matrixCode) (prodCode vectorCode potentialScalarsCode))
def ppX : Realizes potentialCode vectorCode (fun p => List.ofFn p.x) :=
  ppArgs.then (first vectorCode potentialScalarsCode)
def ppScalars : Realizes potentialCode potentialScalarsCode (fun p => (p.nu,(p.lam,p.error))) :=
  ppArgs.then (second vectorCode potentialScalarsCode)
def ppNu : Realizes potentialCode ratCode PotentialParams.nu :=
  ppScalars.then (first ratCode (prodCode ratCode ratCode))
def ppLam : Realizes potentialCode ratCode PotentialParams.lam :=
  ppScalars.then ((second ratCode (prodCode ratCode ratCode)).then (first ratCode ratCode))
def ppError : Realizes potentialCode ratCode PotentialParams.error :=
  ppScalars.then ((second ratCode (prodCode ratCode ratCode)).then (second ratCode ratCode))
def PotentialParams.theta (p : PotentialParams) : Fin p.N → ℚ :=
  fun i => Scalar.approxPsi (p.x i) (RationalSDP.rootTolerance p.d p.N p.lam p.error)
def PotentialParams.query (p : PotentialParams) : ValueQueryParams :=
  ⟨p.d,p.N,p.coords,p.x,p.theta,p.nu,p.error/4⟩

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceQueryRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev faceDataCode := prodCode natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode)))
def FaceParams.data (p : FaceParams) :=
  (p.d,(List.ofFn (fun i => matrixData (RationalSDP.realFinDecode p.d (p.coords i))),
    (List.ofFn p.base,(p.nu,p.lam))))
def faceCode (p : FaceParams) : Word := faceDataCode p.data
def faceView : Realizes faceCode faceDataCode FaceParams.data :=
  (identity faceDataCode).reindex faceCode FaceParams.data (fun _ => rfl)
def fD := faceView.then (first natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode))))
def fRest := faceView.then (second natCode (prodCode (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode))))
def fAtoms := fRest.then (first (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode)))
def fArgs := fRest.then (second (listCode matrixCode) (prodCode vectorCode (prodCode ratCode ratCode)))
def fBase : Realizes faceCode vectorCode (fun p => List.ofFn p.base) :=
  fArgs.then (first vectorCode (prodCode ratCode ratCode))
def fScalars := fArgs.then (second vectorCode (prodCode ratCode ratCode))
def fNu := fScalars.then (first ratCode ratCode)
def fLam := fScalars.then (second ratCode ratCode)
abbrev FaceParams.n (p : FaceParams) : ℕ := (RationalFace.activeIndices p.base).length
def FaceParams.schedule (p : FaceParams) : Schedule.Parameters := Schedule.parameters p.d p.n p.nu p.lam
lemma gather_data {N n : ℕ} (x : Fin N → ℚ) (e : Fin n → Fin N) :
    gatherData (List.ofFn x,List.ofFn (fun j => (e j).val))=List.ofFn (fun j => x (e j)) := by
  simp only [gatherData,List.map_ofFn,Function.comp_def,getD_ofFn]

structure FacePoint where
  p : FaceParams
  y : Fin p.n → ℚ
def facePointData (s : FacePoint) := (s.p,List.ofFn s.y)
def facePointCode (s : FacePoint) : Word := prodCode faceCode vectorCode (facePointData s)
def facePointView : Realizes facePointCode (prodCode faceCode vectorCode) facePointData :=
  (identity (prodCode faceCode vectorCode)).reindex facePointCode facePointData (fun _ => rfl)
def fpP : Realizes facePointCode faceCode FacePoint.p := facePointView.then (first faceCode vectorCode)
def fpY : Realizes facePointCode vectorCode (fun s => List.ofFn s.y) := facePointView.then (second faceCode vectorCode)
def FacePoint.potential (q : FacePoint×ℚ) : PotentialParams :=
  ⟨q.1.p.d,q.1.p.N,q.1.p.coords,
    RationalFace.extend (RationalFace.activeIndex q.1.p.base) q.1.p.base q.1.y,
    q.1.p.nu,q.1.p.lam,q.2⟩

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_StencilRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*}

abbrev FaceIndex := Σ p : FaceParams,Fin p.n
abbrev faceIndexCode := finFamilyCode faceCode FaceParams.n
def fiP : Realizes faceIndexCode faceCode (fun s : FaceIndex => s.1) := familyFirst
def fiI : Realizes faceIndexCode natCode (fun s : FaceIndex => s.2.val) := familyIndex

abbrev FaceDouble := Σ s : FaceIndex,Fin s.1.n
abbrev faceDoubleCode := finFamilyCode faceIndexCode (fun s : FaceIndex => s.1.n)
def fdS : Realizes faceDoubleCode faceIndexCode (fun s : FaceDouble => s.1) := familyFirst
def fdP := fdS.then fiP
def fdI := fdS.then fiI
def fdJ : Realizes faceDoubleCode natCode (fun s : FaceDouble => s.2.val) := familyIndex

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CurvatureRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

lemma squareSum_data {n : ℕ} (v : Fin n → ℚ) : squareSumData (List.ofFn v)=RationalRoot.sqSum v := by
  simp [squareSumData,RationalRoot.sqSum,List.sum_ofFn,Function.comp_def]

lemma initialScale_data {n : ℕ} (v : Fin n → ℚ) :
    initialScaleData (List.ofFn v)=List.ofFn (RationalRoot.initialScale v) := by
  simp only [initialScaleData,squareSum_data,List.map_ofFn,Function.comp_def]
  rfl

def normalizeData (p : ℚ×List ℚ) : List ℚ :=
  let u := initialScaleData p.2
  u.map (fun t => t/RationalRoot.upperSqrt (squareSumData u) (p.1*squareSumData u))
lemma normalize_data {n : ℕ} (beta : ℚ) (v : Fin n → ℚ) :
    normalizeData (beta,List.ofFn v)=List.ofFn (fun i => RationalRoot.normalize v beta i) := by
  simp only [normalizeData,initialScale_data,squareSum_data,List.map_ofFn,Function.comp_def,RationalRoot.normalize]

lemma roundMesh_data {n : ℕ} (rho : ℚ) (v : Fin n → ℚ) :
    (List.ofFn v).map (fun x => rho*(RationalRoot.nearest (x/rho):ℚ))=
      List.ofFn (RationalRoot.roundMesh rho v) := by
    rw [List.map_ofFn]
    rfl

abbrev curvatureDataCode := prodCode natCode (prodCode matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode))))
def CurvatureParams.data (p : CurvatureParams) := (p.n,(matrixData p.H,(p.a,(p.M,(p.s,p.rho)))))
def curvatureCode (p : CurvatureParams) : Word := curvatureDataCode p.data
def curvatureView : Realizes curvatureCode curvatureDataCode CurvatureParams.data :=
  (identity curvatureDataCode).reindex curvatureCode CurvatureParams.data (fun _ => rfl)
def cuN := curvatureView.then (first natCode (prodCode matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode)))))
def cuRest := curvatureView.then (second natCode (prodCode matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode)))))
def cuH := cuRest.then (first matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode))))
def cuScalars := cuRest.then (second matrixCode (prodCode ratCode (prodCode ratCode (prodCode ratCode ratCode))))
def cuA := cuScalars.then (first ratCode (prodCode ratCode (prodCode ratCode ratCode)))
def cuMore := cuScalars.then (second ratCode (prodCode ratCode (prodCode ratCode ratCode)))
def cuM := cuMore.then (first ratCode (prodCode ratCode ratCode))
def cuLast := cuMore.then (second ratCode (prodCode ratCode ratCode))
def cuS := cuLast.then (first ratCode ratCode)
def cuRho := cuLast.then (second ratCode ratCode)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_EndpointRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev vectorUpdateCode := prodCode vectorCode (prodCode natCode ratCode)
def endpointData (xs : List ℚ) : List (List ℚ) :=
  (List.range xs.length).flatMap (fun i => [updateData (xs,(i,-1)),updateData (xs,(i,1))])
lemma endpoint_data {n : ℕ} (x : Fin n → ℚ) :
    endpointData (List.ofFn x)=(Difference.endpointCandidates x).map List.ofFn := by
  unfold endpointData Difference.endpointCandidates
  rw [List.length_ofFn,range_finRange,List.flatMap_map,List.map_flatMap]
  apply congrArg (List.flatMap · (List.finRange n))
  funext i
  simp only [update_data,List.map_cons,List.map_nil]

def freezeScalarData (sigma t : ℚ) : ℚ :=
  if 1 - |t| ≤ sigma then RationalFace.nearestEndpoint t else t
lemma nearestEndpoint_idem (t : ℚ) : RationalFace.nearestEndpoint (RationalFace.nearestEndpoint t)=RationalFace.nearestEndpoint t := by
  unfold RationalFace.nearestEndpoint
  split_ifs <;> norm_num at *
lemma freezeScalar_idem (sigma t : ℚ) : freezeScalarData sigma (freezeScalarData sigma t)=freezeScalarData sigma t := by
  unfold freezeScalarData
  split_ifs <;> simp_all only [nearestEndpoint_idem]

lemma freezeOne_at {n : ℕ} (sigma : ℚ) (x : Fin n → ℚ) (i j : Fin n) :
    RationalFace.freezeOne sigma x j i=if i=j then freezeScalarData sigma (x i) else x i := by
  by_cases hij : i=j
  · subst i
    unfold RationalFace.freezeOne freezeScalarData
    split_ifs <;> simp_all
  · unfold RationalFace.freezeOne
    split_ifs <;> simp [hij]
lemma freezeList_at {n : ℕ} (sigma : ℚ) (xs : List (Fin n)) (x : Fin n → ℚ) (i : Fin n) :
    RationalFace.freezeList sigma x xs i=if i∈xs then freezeScalarData sigma (x i) else x i := by
  induction xs generalizing x with
  | nil => simp [RationalFace.freezeList]
  | cons j js ih =>
    rw [RationalFace.freezeList,ih,freezeOne_at]
    by_cases hij : i=j
    · subst j
      simp [freezeScalar_idem]
    · simp only [hij,ite_false, if_false,List.mem_cons,false_or]
lemma freezeVector_data {n : ℕ} (sigma : ℚ) (x : Fin n → ℚ) :
    (List.ofFn x).map (freezeScalarData sigma)=List.ofFn (RationalFace.freezeAll sigma x) := by
  rw [List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,RationalFace.freezeAll,freezeList_at,List.mem_finRange,ite_true, if_true]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCurvature
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_curvatureView : PolyTime curvatureView := by unfold curvatureView;apply poly_reindex
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceBasics
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_faceView : PolyTime faceView := by unfold faceView;apply poly_reindex
instance poly_facePointView : PolyTime facePointView := by unfold facePointView;apply poly_reindex
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_consList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β γ : Type*} {L f g : ι → ℕ}

def IsPoly (L f : ι → ℕ) : Prop := ∃ p : NaturalPolynomial,∀i,f i≤p.eval (L i)

variable {ea : α → Word} {eb : β → Word} {ec : γ → Word} {F : α → β} {G : β → γ}

structure RunsPoly (L : ι → ℕ) (r : Realizes ea eb F) (a : ι → α) : Prop where
  input : IsPoly L (fun i => (ea (a i)).length)
  cost : IsPoly L (fun i => r.cost (a i))
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOptimize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

def OptParams.searchCount (p : OptParams) : ℕ := RationalSDP.searchFuel p.n p.r p.R
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialValueQuery
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_vqView : PolyTime vqView := by unfold vqView;apply poly_reindex

variable {ι : Type*} {L : ι → ℕ}

def ValueQueryParams.scanCount (p : ValueQueryParams) : ℕ :=
  (RationalSDP.optimizeFuel p.delta 100+1)*p.opt.searchCount
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialPotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_potentialView : PolyTime potentialView := by unfold potentialView;apply poly_reindex

def PotentialParams.scanCount (p : PotentialParams) : ℕ := p.query.scanCount
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceQuery
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def queryScanCount (d : ℕ) (nu err : ℚ) : ℕ :=
  (RationalSDP.optimizeFuel (err/4) 100+1)*RationalSDP.searchFuel (RationalSDP.valueDimension d)
    (RationalSDP.nearRadius (err/4) (RationalSDP.valueLipschitz d (nu/d))
      (RationalSDP.valueOuterRadius d (nu/d)) (RationalSDP.valueInnerRadius d))
    (RationalSDP.valueOuterRadius d (nu/d))
def FaceParams.queryCount (p : FaceParams) (err : ℚ) : ℕ := queryScanCount p.d p.nu err
def FaceParams.stencilCount (p : FaceParams) := p.queryCount p.schedule.stencilError
def FaceParams.scoreCount (p : FaceParams) := p.queryCount p.schedule.selectionError

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceChoiceRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev FaceActive := {p : FaceParams // p.n ≠ 0}
def activeFaceCode (p : FaceActive) : Word := faceCode p.val
def faP : Realizes activeFaceCode faceCode Subtype.val :=
  (identity faceCode).reindex activeFaceCode Subtype.val (fun _ => rfl)
def FaceParams.gradient (p : FaceParams) := Difference.stencilGradient
  (RationalFace.faceStencil p.coords p.base p.nu p.lam) (RationalFace.faceState p.base) p.schedule.h
def FaceParams.hessian (p : FaceParams) := Difference.stencilHessian
  (RationalFace.faceStencil p.coords p.base p.nu p.lam) (RationalFace.faceState p.base) p.schedule.h
def FaceParams.curvatureParams (p : FaceParams) : CurvatureParams :=
  ⟨p.n,p.hessian,p.schedule.a,p.schedule.M,p.schedule.s,p.schedule.ρ⟩
def FaceParams.curvature (p : FaceParams) :=
  RationalRoot.computedCurvature p.hessian p.schedule.a p.schedule.M p.schedule.s p.schedule.ρ

def FaceActive.gradientPoint (p : FaceActive) : Fin p.val.n → ℚ :=
  letI : NeZero p.val.n := ⟨p.property⟩
  RationalFace.faceState p.val.base+p.val.schedule.s • Difference.rationalGradientDirection p.val.gradient

def curvatureCandidatesData (p : List ℚ×List ℚ) : List (List ℚ) :=
  if p.2.length=0 then [] else
    [zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0 p,zipDefault (fun z : ℚ×ℚ => z.1-z.2) 0 0 p]
lemma curvatureCandidates_data {n : ℕ} [NeZero n] (x : Fin n → ℚ) (q : Option (Fin n → ℚ)) :
    curvatureCandidatesData (List.ofFn x,q.elim [] List.ofFn)=
      ((match q with | none => [] | some q => [x+q,x-q]).map List.ofFn) := by
  cases q with
  | none => simp [curvatureCandidatesData]
  | some q => simp only [Option.elim_some,curvatureCandidatesData,List.length_ofFn,NeZero.ne,ite_false, if_false,
      vectorAdd_ofFn,vectorSub_data,List.map_cons,List.map_nil]

def FaceActive.candidates (p : FaceActive) : List (Fin p.val.n → ℚ) :=
  letI : NeZero p.val.n := ⟨p.property⟩
  RationalFace.faceCandidates p.val.coords p.val.base p.val.nu p.val.lam

def FaceActive.choice (p : FaceActive) : Fin p.val.n → ℚ :=
  letI : NeZero p.val.n := ⟨p.property⟩
  RationalFace.faceChoice p.val.coords p.val.base p.val.nu p.val.lam

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceChoice
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι : Type*} {L : ι → ℕ}
instance poly_faP : PolyTime faP := by unfold faP;apply poly_reindex
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMatrixSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

abbrev addMatrices (A B : MatrixData) := zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] [] (A,B)
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceRunRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def packFace {α : Type*} {ea : α → Word} {f : α → FaceParams}
    {g : (a : α) → Fin (f a).N → ℚ}
    (p : Realizes ea faceCode f) (y : Realizes ea vectorCode (fun a => List.ofFn (g a))) :
    Realizes ea faceCode (fun a => {f a with base := g a}) :=
  ((p.then fD).both ((p.then fAtoms).both (y.both (p.then fScalars)))).changeOutput
    faceCode (fun a => {f a with base := g a}) (fun _ => rfl)

def FaceActive.nextBase (p : FaceActive) : Fin p.val.N → ℚ :=
  RationalFace.freezeAll (p.val.lam^2/p.val.nu)
    (RationalFace.extend (RationalFace.activeIndex p.val.base) p.val.base p.choice)

def FaceParams.next (p : FaceParams) : FaceParams :=
  {p with base := (RationalFace.transition p.coords p.nu p.lam p.base).getD p.base}

lemma minList_reverse (xs : List ℚ) : xs.reverse.foldl min 1=Descent.minList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,ih,Descent.minList]
    exact min_comm _ _

def FaceParams.start (p : FaceParams) : FaceParams :=
  {p with base := RationalFace.freezeAll (p.lam^2/p.nu) 0}

lemma run_eq_iterate {α : Type*} (step : α → Option α) (k : ℕ) (x : α) :
    Descent.run step k x=(fun a => (step a).getD a)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Descent.run,Function.iterate_succ_apply]
    cases he : step x with
    | none =>
      simp only [Option.getD_none]
      exact (Function.iterate_fixed (by simp [he]) k).symm
    | some y => simpa only [Option.getD_some] using ih y

lemma next_iterate (p : FaceParams) (k : ℕ) :
    FaceParams.next^[k] p={p with base := Descent.run (RationalFace.transition p.coords p.nu p.lam) k p.base} := by
  rcases p with ⟨d,N,coords,x,nu,lam⟩
  rw [run_eq_iterate]
  let g (x : Fin N → ℚ) : FaceParams := ⟨d,N,coords,x,nu,lam⟩
  have h : Function.Semiconj g (fun x => (RationalFace.transition coords nu lam x).getD x) FaceParams.next :=
    fun x => rfl
  exact (h.iterate_right k x).symm

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VarianceRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

abbrev matrixGridDataCode := prodCode natCode (prodCode matrixCode natCode)
def MatrixGrid.data (p : MatrixGrid) := (p.n,(matrixData p.M,p.den))
def matrixGridCode (p : MatrixGrid) : Word := matrixGridDataCode p.data
def mgView : Realizes matrixGridCode matrixGridDataCode MatrixGrid.data :=
  (identity matrixGridDataCode).reindex matrixGridCode MatrixGrid.data (fun _ => rfl)
def mgN := mgView.then (first natCode (prodCode matrixCode natCode))
def mgRest := mgView.then (second natCode (prodCode matrixCode natCode))
def mgM := mgRest.then (first matrixCode natCode)
def mgDen := mgRest.then (second matrixCode natCode)
def MatrixGrid.test (p : MatrixGrid) (q : ℚ) : Bool :=
  (KS.W17.rationalNegativeWitness p.n (q • 1-p.M)).isNone

abbrev gridStateCode := prodCode matrixGridCode (prodCode natCode natCode)
def gridStepData (s : MatrixGrid×(ℕ×ℕ)) :=
  (s.1,(s.2.1+1,if s.1.test ((s.2.1:ℚ)/s.1.den) then s.2.2 else s.2.1+1))
lemma grid_iterate (p : MatrixGrid) (k : ℕ) :
    gridStepData^[k] (p,(0,0))=(p,(k,RationalGrid.upperIndex p.den p.test k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih]
    rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialVariance
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_vqView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_mgView : PolyTime mgView := by unfold mgView;apply poly_reindex
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_StoredBits
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalFace

section
open CurrentKS.RationalGridSize CurrentKS.Schedule CurrentKS.Descent CurrentKS.Difference
open scoped BigOperators

variable {d N n : ℕ}

def meshDenominator (d N : ℕ) (ν lam : ℚ) : ℕ :=
  ∏ n ∈ Finset.range (N+1), (parameters d n ν lam).s.den*(parameters d n ν lam).ρ.den

end
open CurrentKS.RationalBits CurrentKS.RationalGridSize CurrentKS.ScheduleBits
open CurrentKS.Schedule CurrentKS.RationalSDP CurrentKS.Descent
open KS.W23
open scoped BigOperators

variable {d N : ℕ}

def baseBitsP : NaturalPolynomial :=
  NaturalPolynomial.variable+NaturalPolynomial.variable+
    2*(1000*NaturalPolynomial.variable*NaturalPolynomial.variable^2)+1+200*NaturalPolynomial.variable
def meshBitsP (C : ℕ) : NaturalPolynomial :=
  1+(NaturalPolynomial.variable+1)*(2*(NaturalPolynomial.constant C*(baseBitsP+1)+1))

def storedBitsP (C : ℕ) : NaturalPolynomial := 2*meshBitsP C

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceOrbit
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalSDP Hermitian
open scoped BigOperators MatrixOrder

structure FaceParams.GoodAtoms (p : FaceParams) : Prop where
  d_ne : p.d≠0
  N_ne : p.N≠0
  positive : ∀i,rationalAtoms p.coords i∈psdCone p.d
  nonzero : ∀i,rationalAtoms p.coords i≠0
  rank : ∀i,(rationalAtoms p.coords i : Mat p.d).rank≤1
  trace : ∑i,Hermitian.realTrace (rationalAtoms p.coords i)=1

def FaceParams.normal (p : FaceParams) : FaceParams :=
  {p with nu := RationalSDP.varianceQuery p.coords,lam := Schedule.penaltyParameter p.N (RationalSDP.varianceQuery p.coords)}
def FaceParams.orbit (p : FaceParams) (k : ℕ) : FaceParams :=
  FaceParams.next^[k] p.normal.start
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_DenseInputMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.DenseInputMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

lemma frame_eq (bs : List Bool) : CurrentKS.frame bs = KS.W01.frame bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [CurrentKS.frame, KS.W01.frame, ih]

lemma encodeNat_eq (n : ℕ) : CurrentKS.encodeNat n = KS.W01.encodeNat n :=
  frame_eq _

end CurrentKS.DenseInputMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_DenseInputArrays
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.DenseInputArrays
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def fields (x : Input) (i : Fin x.N) : List RationalEntry :=
  (List.ofFn fun j : Fin x.d =>
    (List.ofFn fun k : Fin x.d => x.entries i j k).flatMap
      (fun z => [z.1,z.2])).flatten

end CurrentKS.DenseInputArrays

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalFieldsRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def fieldValues (x : Input) (i : Fin x.N) : List ℚ :=
  (DenseInputArrays.fields x i).map RationalEntry.value
lemma fieldValues_eq (x : Input) (i : Fin x.N) :
    fieldValues x i=(List.ofFn fun j : Fin x.d =>
      (List.ofFn fun k : Fin x.d => [(x.entries i j k).1.value,(x.entries i j k).2.value]).flatten).flatten := by
  simp [fieldValues,DenseInputArrays.fields,List.flatMap_def,List.map_flatten,List.map_ofFn,Function.comp_def]

lemma fieldValues_get (x : Input) (i : Fin x.N) (j k : Fin x.d) (b : Fin 2) :
    (fieldValues x i).getD (2*(j.val*x.d+k.val)+b.val) 0=
      (if b.val=0 then (x.entries i j k).1.value else (x.entries i j k).2.value) := by
  rw [fieldValues_eq]
  have hl (j : Fin x.d) :
      ((List.ofFn fun k : Fin x.d => [(x.entries i j k).1.value,(x.entries i j k).2.value]).flatten).length=2*x.d := by
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,List.length_cons,List.length_nil]
    simp
    omega
  have he : 2*(j.val*x.d+k.val)+b.val=j.val*(2*x.d)+(k.val*2+b.val) := by ring
  rw [he,getD_flatten_ofFn _ hl j _ (by have hk := k.isLt;have hb := b.isLt;omega)]
  rw [getD_flatten_ofFn (fun k : Fin x.d => [(x.entries i j k).1.value,(x.entries i j k).2.value]) (m := 2) (fun _ => rfl) k b.val b.isLt]
  fin_cases b <;> simp

abbrev originalDataCode := prodCode natCode (listCode vectorCode)
def originalData (x : Input) := (x.d,List.ofFn (fieldValues x))
def originalCode (x : Input) : Word := originalDataCode (originalData x)
def originalView : Realizes originalCode originalDataCode originalData :=
  (identity originalDataCode).reindex originalCode originalData (fun _ => rfl)
def originalD : Realizes originalCode natCode Input.d := originalView.then (first natCode (listCode vectorCode))
def originalRecords : Realizes originalCode (listCode vectorCode) (fun x => List.ofFn (fieldValues x)) :=
  originalView.then (second natCode (listCode vectorCode))

abbrev recordCode := prodCode natCode vectorCode
abbrev recordPointCode := prodCode (prodCode recordCode natCode) natCode

def recordCoordinateData (p : ((ℕ×List ℚ)×ℕ)×ℕ) : ℚ :=
  if p.1.2≤p.2 then recordEntryData false p else recordEntryData true ((p.1.1,p.2),p.1.2)

def recordCoordinatesData (p : ℕ×List ℚ) : MatrixData :=
  (List.range p.1).map (fun i => (List.range p.1).map (fun j => recordCoordinateData ((p,i),j)))
lemma recordCoordinate_data (x : Input) (i : Fin x.N) (j k : Fin x.d) :
    recordCoordinateData (((x.d,fieldValues x i),j.val),k.val)=RationalInput.coordinates x i (j,k) := by
  unfold recordCoordinateData RationalInput.coordinates
  change (if j.val≤k.val then _ else _)=
    (if j.val≤k.val then (x.entries i j k).1.value else (x.entries i k j).2.value)
  by_cases hle : j.val≤k.val
  · simp only [hle,ite_true, if_true,recordEntryData,Bool.false_eq_true,ite_false, if_false,Nat.add_zero]
    have hh := fieldValues_get x i j k (0 : Fin 2)
    simpa using hh
  · simp only [hle,ite_false, if_false,recordEntryData,ite_true, if_true]
    have hh := fieldValues_get x i k j (1 : Fin 2)
    simpa using hh
lemma recordCoordinates_data (x : Input) (i : Fin x.N) :
    recordCoordinatesData (x.d,fieldValues x i)=matrixData (fun j k => RationalInput.coordinates x i (j,k)) := by
  simp only [recordCoordinatesData,range_map_fin,matrixData,recordCoordinate_data]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalSignRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

lemma recordTrace_data (x : Input) (i : Fin x.N) :
    recordTraceData (x.d,fieldValues x i)=RationalInput.trace x i := by
  unfold recordTraceData
  rw [range_map_fin,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  have h := fieldValues_get x i j j (0 : Fin 2)
  simpa [recordEntryData] using h

lemma nonzeroIndices_data (x : Input) :
    nonzeroIndicesData (List.ofFn (RationalInput.trace x))=List.ofFn (fun j => (RationalInput.index x j).val) := by
  have h : nonzeroIndicesData (List.ofFn (RationalInput.trace x))=(RationalInput.indices x).map Fin.val := by
    unfold nonzeroIndicesData RationalInput.indices
    rw [List.length_ofFn,range_finRange,List.filter_map]
    congr 1
    apply List.filter_congr
    intro i hi
    rw [Function.comp_apply,getD_ofFn]
  rw [h]
  change _=List.ofFn (Fin.val ∘ (RationalInput.indices x).get)
  rw [←List.map_ofFn,List.ofFn_get]

abbrev originalCount (x : Input) := (RationalInput.indices x).length

def originalFace (x : Input) : FaceParams :=
  ⟨x.d,originalCount x,RationalInput.normalizedCoordinates x,fun _ => 0,0,0⟩

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOriginalFields
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_vqView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_originalView : PolyTime originalView := by unfold originalView;apply poly_reindex
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_MachineAdapter
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.ArchivedMachine
open KS.W01.FixedStack

def action : KS.W29.StackAction → CurrentKS.StackAction
  | .stay => .stay
  | .pop => .pop
  | .push b => .push b

def instruction {k q : ℕ} (a : KS.W01.FixedStack.Instruction k q) :
    CurrentKS.Instruction k q := ⟨a.next,fun j => action (a.action j)⟩

def machine (M : KS.W01.FixedStack.Machine) : CurrentKS.Machine where
  stackCount := M.stackCount
  states := M.states
  initial := M.initial
  inputStack := M.inputStack
  outputStack := M.outputStack
  table := List.ofFn fun i : Fin (M.states*3^M.stackCount) =>
    instruction (M.table.getD (2*i.val) (KS.W01.FixedStack.Instruction.halt _ _))

def config {k q : ℕ} (c : KS.W01.FixedStack.Config k q) : CurrentKS.Config k q :=
  ⟨c.state,c.«stacks»⟩

end CurrentKS.ArchivedMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalOutputRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

abbrev wordCode : Word → Word := id

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_GraphMatrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
def resistance (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) : ℝ := qform X⁻¹ (G.incidence e)

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_BasePacking
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uI2

section

noncomputable section
open Finset Submodule

namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

abbrev edgeSpan (T : Finset (Fin m)) := Packing.span G.incidence T

def Same (T : Finset (Fin m)) (u v : Fin n) : Prop :=
  point u - point v ∈ G.edgeSpan T

lemma same_refl (T : Finset (Fin m)) (u : Fin n) : G.Same T u u := by
  simp [Same]

lemma same_symm {T : Finset (Fin m)} {u v : Fin n} (h : G.Same T u v) : G.Same T v u := by
  change point v - point u ∈ G.edgeSpan T
  simpa only [neg_sub] using (G.edgeSpan T).neg_mem h

lemma same_trans {T : Finset (Fin m)} {u v w : Fin n}
    (huv : G.Same T u v) (hvw : G.Same T v w) : G.Same T u w := by
  change point u - point w ∈ G.edgeSpan T
  simpa only [sub_add_sub_cancel] using (G.edgeSpan T).add_mem huv hvw

def components (T : Finset (Fin m)) : Setoid (Fin n) where
  r := G.Same T
  iseqv := ⟨G.same_refl T, G.same_symm, G.same_trans⟩

def rep (T : Finset (Fin m)) (u : Fin n) : Fin n := (Quotient.mk (G.components T) u).out

lemma same_endpoints {T : Finset (Fin m)} {e : Fin m} (he : e ∈ T) :
    G.Same T (G.left e) (G.right e) := Packing.mem_span_self G.incidence he

abbrev repDifference (T : Finset (Fin m)) (u : Fin n) : Fin n → ℝ :=
  point u - point (G.rep T u)

def componentCount (T : Finset (Fin m)) : ℕ := (Finset.univ.image (G.rep T)).card

lemma sumOn_point (S : Finset (Fin n)) (v : Fin n) :
    (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) =
      if v ∈ S then 1 else 0 := by
  simp [LinearMap.sum_apply, point, Pi.single_apply, Finset.sum_ite_eq']

theorem connected_iff_same (T : Finset (Fin m)) :
    G.Connected T ↔ ∀ u v, G.Same T u v := by
  classical
  constructor
  · intro hconn u v
    by_contra huv
    let S := Finset.univ.filter (fun w => G.Same T w v)
    have hS : S.Nonempty := ⟨v, by simp [S, G.same_refl]⟩
    have hSne : S ≠ Finset.univ := by
      intro heq
      have hu : u ∈ S := heq ▸ Finset.mem_univ u
      exact huv (by simpa [S] using hu)
    obtain ⟨e, he⟩ := hconn S hS hSne
    obtain ⟨heT, hecut⟩ := Finset.mem_filter.mp he
    rcases hecut with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have hl' : G.Same T (G.left e) v := by simpa [S] using hl
      have hr' := G.same_trans (G.same_symm (G.same_endpoints heT)) hl'
      exact hr (by simpa [S] using hr')
    · have hr' : G.Same T (G.right e) v := by simpa [S] using hr
      have hl' := G.same_trans (G.same_endpoints heT) hr'
      exact hl (by simpa [S] using hl')
  · intro hsame S hS hSne
    by_contra hcut
    have hempty : G.cut T S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcut
    let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ u ∈ S, LinearMap.proj u
    have hker : G.edgeSpan T ≤ LinearMap.ker f := by
      apply (Packing.span_le_iff G.incidence).mpr
      intro e he
      have hiff : G.left e ∈ S ↔ G.right e ∈ S := by
        have h : ¬ ((G.left e ∈ S ∧ G.right e ∉ S) ∨
            (G.right e ∈ S ∧ G.left e ∉ S)) := by
          intro hc
          have : e ∈ G.cut T S := Finset.mem_filter.mpr ⟨he, hc⟩
          simp [hempty] at this
        tauto
      change f (G.incidence e) = 0
      rw [incidence, map_sub]
      change (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
        (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e)) = 0
      simp only [sumOn_point]
      simp only [hiff, sub_self]
    obtain ⟨u, hu⟩ := hS
    have hv : ∃ v, v ∉ S := by
      by_contra h
      push Not at h
      exact hSne (Finset.eq_univ_of_forall h)
    obtain ⟨v, hv⟩ := hv
    have hz := hker (hsame u v)
    change f (point u - point v) = 0 at hz
    rw [map_sub] at hz
    change (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
      (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) = 0 at hz
    simp [sumOn_point, hu, hv] at hz

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

instance size_natPred : IterateSize natPred := by
  refine ⟨⟨X,?_⟩⟩
  intro n k
  change (natCode (Nat.pred^[k] n)).length ≤ (natCode n).length+k
  simp only [natCode,List.length_replicate,pred_iterate]
  omega

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_PartitionRank
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uE2 uV2

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

def ConnectedOn (A : Finset (Fin n)) (F : Finset (Fin m)) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, G.Same F u v

def TreeOn (A : Finset (Fin n)) (F : Finset (Fin m)) : Prop :=
  F ⊆ G.internal univ A ∧ G.ConnectedOn A F ∧ LinearIndepOn ℝ G.incidence (F : Set (Fin m))

def PackableOn (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) : Prop :=
  ∃ T : Fin q → Finset (Fin m),
    (∀ i, T i ⊆ G.internal F A ∧ G.ConnectedOn A (T i)) ∧
    ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j)

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Representation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uE uT uI uE2 uE3 uV uE4 uV2 uW

section

open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {n m : ℕ} (G : MultiGraph n m)

lemma incidence_zeroSum (e : Fin m) : G.incidence e ∈ zeroSumSpace n := by
  rw [mem_zeroSumSpace]
  simp [incidence, point, Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply,
    Finset.sum_ite_eq']

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Descent
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization descent. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder

section Covariance
variable {E I : Type*} [normalizationFintypeE : Fintype E]
  [normalizationDecidableEqE : DecidableEq E] [normalizationFintypeI : Fintype I]
  [normalizationDecidableEqI : DecidableEq I]

noncomputable def leverage (v : E → I → ℝ) (a : E → ℝ) (e : E) : ℝ :=
  a e * (v e ⬝ᵥ ((covariance v a)⁻¹ *ᵥ v e))

noncomputable def objective (q : ℕ) (v : E → I → ℝ) (a : E → ℝ) : ℝ :=
  Real.log (covariance v a).det-(∑e, Real.log (a e))/q

end Covariance

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.size_natPred
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {β : Type*}

def selectFlagged (eb : β → Word) :
    Realizes (prodCode eb (listCode (prodCode boolCode eb))) eb
      (fun p => (p.2.find? Prod.fst).elim p.1 Prod.snd) :=
  let ec := prodCode boolCode eb
  let ctx := first eb (listCode ec)
  let test := (second eb ec).then (first boolCode eb)
  let value := (second eb ec).then (second boolCode eb)
  ((ctx.both (identity (prodCode eb (listCode ec)))).then
    (test.findValue value)).congr (fun _ => rfl)

end CurrentKS.Realization

namespace AlgorithmicThinTrees.Normalization.Stack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open Matrix

abbrev paramsDataCode :=
  prodCode natCode (prodCode natCode (prodCode ratCode matrixCode))
def Params.data (p : Params) := (p.d,(p.q,(p.t,matrixData p.v)))
def paramsCode (p : Params) : Word := paramsDataCode p.data
abbrev view : Realizes paramsCode paramsDataCode Params.data :=
  (identity paramsDataCode).reindex paramsCode Params.data (fun _ => rfl)
instance poly_view : PolyTime view := by
  unfold view
  apply poly_reindex

abbrev dim := view.then (first natCode (prodCode natCode (prodCode ratCode matrixCode)))
abbrev rest := view.then (second natCode (prodCode natCode (prodCode ratCode matrixCode)))
abbrev count := rest.then (first natCode (prodCode ratCode matrixCode))
abbrev tail := rest.then (second natCode (prodCode ratCode matrixCode))
abbrev factor := tail.then (first ratCode matrixCode)
abbrev columns := tail.then (second ratCode matrixCode)

def stateCode (s : State) : Word :=
  prodCode paramsCode vectorCode (s.params,List.ofFn s.scales)
abbrev stateView : Realizes stateCode (prodCode paramsCode vectorCode)
    (fun s => (s.params,List.ofFn s.scales)) :=
  (identity (prodCode paramsCode vectorCode)).reindex stateCode
    (fun s => (s.params,List.ofFn s.scales)) (fun _ => rfl)
instance poly_stateView : PolyTime stateView := by
  unfold stateView
  apply poly_reindex

abbrev params := stateView.then (first paramsCode vectorCode)
abbrev scales := stateView.then (second paramsCode vectorCode)

abbrev columnCode := finFamilyCode stateCode (fun s : State => s.params.m)
abbrev colState : Realizes columnCode stateCode (fun x : Column => x.1) := familyFirst
abbrev colIndex : Realizes columnCode natCode (fun x : Column => x.2.val) := familyIndex
abbrev colParams := colState.then params

abbrev fixedCode := prodCode paramsCode natCode
abbrev fixedParams := first paramsCode natCode
abbrev fixedR := second paramsCode natCode

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_MatrixRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}

lemma matrix_entry_data {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) (i : Fin n) (j : Fin m) :
    ((matrixData A).getD i.val []).getD j.val 0=A i j := by
  rw [show matrixData A=List.ofFn (fun i => List.ofFn (A i)) from rfl,
    getD_ofFn,getD_ofFn]

def schurData (a : MatrixObject) : MatrixObject :=
  match a with
  | ⟨0,A⟩ => ⟨0,A⟩
  | ⟨n+1,A⟩ => ⟨n,KS.W17.schurTail A⟩

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_SchurHistory
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schur history. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

abbrev SchurStack := MatrixObject×List MatrixObject

def schurNextData (s : SchurStack) : SchurStack :=
  if s.1.1=0 then s else (schurData s.1,s.1::s.2)

def schurHistoryData : MatrixObject → List MatrixObject
  | ⟨0,_⟩ => []
  | ⟨d+1,A⟩ => schurHistoryData ⟨d,KS.W17.schurTail A⟩ ++ [⟨d+1,A⟩]
termination_by a => a.1

lemma schurHistory_iterate (a : MatrixObject) (xs : List MatrixObject) :
    ((schurNextData^[a.1]) (a,xs)).2=schurHistoryData a++xs := by
  rcases a with ⟨d,A⟩
  induction d generalizing xs with
  | zero => simp [schurHistoryData]
  | succ d ih =>
    rw [Function.iterate_succ_apply]
    change ((schurNextData^[d]) (⟨d,KS.W17.schurTail A⟩,⟨d+1,A⟩::xs)).2=_
    rw [ih]
    simp only [schurHistoryData,List.append_assoc,List.singleton_append]

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_MatrixBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric matrix bound. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

def Test (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Z.PosSemidef ∧ ∀u v w, qform Z (difference u w) ≤
    qform Z (difference u v)+qform Z (difference v w)

def CenteredTest (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Test Z ∧ Z *ᵥ (fun _ => 1)=0

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CenteredMatrices
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered matrices. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

def CenteredPositive (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  D.IsHermitian ∧ D *ᵥ ones n=0 ∧ ∀x : Fin n → ℝ, (∑i, x i)=0 → x ≠ 0 → 0 < qform D x

def regularize (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  D+constantProjection n

def inverseOnZeroSum (D : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (regularize D)⁻¹

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_Hierarchy
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric hierarchy. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

def resistance (G : MultiGraph n m) (D : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) : ℝ :=
  qform (inverseOnZeroSum D) (G.incidence e)

def boundaryResistance (G : MultiGraph n m) (H : Hierarchy n)
    (D : Matrix (Fin n) (Fin n) ℝ) (A : Finset (Fin n)) : ℝ :=
  ((H.parentBoundary G A).card : ℝ)⁻¹ * ∑e ∈ H.parentBoundary G A, resistance G D e

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_CenteredDomain
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

def metricDomain (G : MultiGraph n m) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.IsHermitian ∧ X *ᵥ ones n=0 ∧ G.laplacian univ ≤ X ∧
     ∀Z, CenteredTest Z → (X*Z).trace ≤ 3*(G.laplacian univ*Z).trace}

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Ramp
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation ramp. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

def cappedParameter (G : MultiGraph n m) (s : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) : ℝ :=
  min 2 (s*resistance G X e)⁻¹

def ramp (G : MultiGraph n m) (s : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) : ℝ :=
  max 0 (cappedParameter G s X e-1)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Domain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

def admissible (H : MultiGraph n m) (s : ℝ) (u : Fin m → ℝ) : Set (ResponseSpace n m) :=
  {x | x.1 ∈ metricDomain H ∧ (∀e, 0 ≤ x.2 e ∧ x.2 e ≤ 1) ∧
    ∀e, 0 < u e → (6*s*x.2 e) • vecMulVec (H.incidence e) (H.incidence e) ≤ x.1}

def responseSlack (H : MultiGraph n m) (κ t Q : ℝ) (u : Fin m → ℝ)
    (p : Setoid (Fin n)) (x : ResponseSpace n m) : ℝ :=
  Partitions.slack H.left H.right (fun e => lowerCapacity κ t (u e) (x.2 e)) Q p

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation encoding. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

namespace StepFree

def capacities (κ : ℝ) (u : Fin m → ℝ) (x : StepFree n m) : Fin m → ℝ :=
  fun e => if 0 < u e then x.z e else κ

end StepFree

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Interior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation interior. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

namespace StepFree

def Close (x w : StepFree n m) (η : ℝ) : Prop :=
  (∀i j, |x.1 i j-w.1 i j| ≤ η) ∧
  (∀ijk, |x.multiplier ijk-w.multiplier ijk| ≤ η) ∧
  (∀e, |x.y e-w.y e| ≤ η) ∧ (∀e, |x.z e-w.z e| ≤ η)

end StepFree

def auxiliaryPoint (H : MultiGraph n m) (κ : ℝ) : StepFree n m :=
  ((2 : ℝ) • H.laplacian univ,fun _ => (graphSize n m)^(-8 : ℤ),
    fun _ => (graphSize n m)^(-8 : ℤ),fun _ => κ/2)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation grid. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise
variable {n m : ℕ}

namespace StepFree

def canonical (x : StepFree n m) : StepFree n m := (x.matrix,x.2)

def Bounded (x : StepFree n m) (R : ℝ) : Prop :=
  (∀i j, |x.1 i j| ≤ R) ∧ (∀ijk, |x.multiplier ijk| ≤ R) ∧
    (∀e, |x.y e| ≤ R) ∧ (∀e, |x.z e| ≤ R)

end StepFree

abbrev StepRational (n m : ℕ) :=
  Matrix (Fin n) (Fin n) ℚ × (DistinctTriple n → ℚ) × (Fin m → ℚ) × (Fin m → ℚ)

namespace StepRational

def real (x : StepRational n m) : StepFree n m :=
  (fun i j => (x.1 i j:ℝ),fun ijk => (x.2.1 ijk:ℝ),
    fun e => (x.2.2.1 e:ℝ),fun e => (x.2.2.2 e:ℝ))

end StepRational

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_RootedOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rooted orientation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical
variable {n m : ℕ}

def adjacency (G : MultiGraph n m) (T : Finset (Fin m)) : SimpleGraph (Fin n) where
  Adj a b := ∃e ∈ T, (G.left e=a ∧ G.right e=b) ∨ (G.right e=a ∧ G.left e=b)
  symm := ⟨by rintro a b ⟨e,he,h|h⟩ <;> exact ⟨e,he,by tauto⟩⟩
  loopless := ⟨by
    intro a
    rintro ⟨e,he,h|h⟩
    · exact G.loopless e (h.1.trans h.2.symm)
    · exact G.loopless e (h.2.trans h.1.symm)⟩

structure Rooted (G : MultiGraph n m) (T : Finset (Fin m)) (root : Fin n) where
  tail : T ≃ {v : Fin n // v ≠ root}
  endpoint : ∀e : T, (tail e).val=G.left e ∨ (tail e).val=G.right e

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_RootedFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rooted flow. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical
variable {n m : ℕ}

def Rooted.leftFlow {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) : ℝ :=
  if he : e ∈ T then if (R.tail ⟨e,he⟩).val=G.left e then 1 else 0 else 0

def Rooted.rightFlow {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) : ℝ :=
  if he : e ∈ T then if (R.tail ⟨e,he⟩).val=G.right e then 1 else 0 else 0

def out (G : MultiGraph n m) (a b : Fin m → ℝ) (v : Fin n) : ℝ :=
  ∑e, ((if G.left e=v then a e else 0)+(if G.right e=v then b e else 0))

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_RootedRelaxation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rooted relaxation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

def FlowPoint.Feasible (G : MultiGraph n m) (c : Fin m → ℝ) (qbar ε : ℝ)
    (F : FlowPoint n m) : Prop :=
  (∀e, 0 ≤ F.x e ∧ F.x e ≤ c e) ∧
  (∀r e, 0 ≤ F.a r e ∧ 0 ≤ F.b r e ∧ F.x e ≤ F.a r e+F.b r e) ∧
  (∀r v, out G (F.a r) (F.b r) v ≤ if v=r then ε else qbar) ∧
  qbar*((n:ℝ)-1)-ε ≤ ∑e, F.x e

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_FractionalOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional orientation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

def FlowPoint.Exact (G : MultiGraph n m) (c : Fin m → ℝ) (q : ℝ)
    (F : FlowPoint n m) : Prop :=
  (∀e, 0 ≤ F.x e ∧ F.x e ≤ c e) ∧
  (∀r e, 0 ≤ F.a r e ∧ 0 ≤ F.b r e ∧ F.x e = F.a r e+F.b r e) ∧
  (∀r v, out G (F.a r) (F.b r) v = if v=r then 0 else q) ∧
  (∑e, F.x e)=q*((n:ℝ)-1)

def FlowPoint.push {M : ℕ} (π : Fin M → Fin m) (F : FlowPoint n M) : FlowPoint n m :=
  ⟨fun e => ∑f ∈ univ.filter (fun f => π f=e), F.x f,
    fun r e => ∑f ∈ univ.filter (fun f => π f=e), F.a r f,
    fun r e => ∑f ∈ univ.filter (fun f => π f=e), F.b r f⟩

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_ParallelCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parallel copies. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

def copies (G : MultiGraph n m) (a : Fin m → ℕ) : MultiGraph n (Fintype.card (Copy a)) where
  left f := G.left (copyProjection a f)
  right f := G.right (copyProjection a f)
  loopless f := G.loopless (copyProjection a f)

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_Interior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flow interior. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

namespace FlowPoint

def bump (F : FlowPoint n m) (γ : ℝ) : FlowPoint n m :=
  ⟨fun e => F.x e+γ,fun r e => F.a r e+γ,fun r e => F.b r e+γ⟩

def Close (F H : FlowPoint n m) (ρ : ℝ) : Prop :=
  (∀e, |F.x e-H.x e| ≤ ρ) ∧
  (∀r e, |F.a r e-H.a r e| ≤ ρ) ∧ (∀r e, |F.b r e-H.b r e| ≤ ρ)

def Bounded (F : FlowPoint n m) (R : ℝ) : Prop :=
  (∀e, |F.x e| ≤ R) ∧ (∀r e, |F.a r e| ≤ R) ∧ (∀r e, |F.b r e| ≤ R)

end FlowPoint

end
end AlgorithmicThinTrees.Orientations

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Coordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation coordinates. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations

variable {n m : ℕ}

def rational (v : Fin (dimension n m) → ℚ) : StepRational n m :=
  (rawMatrix v,multiplier v,y v,z v)

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Iteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation iteration. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

noncomputable def State.realMatrix (a : State n m) : Matrix (Fin n) (Fin n) ℝ :=
  a.matrix.map (fun q => (q:ℝ))

def Invariant (H : MultiGraph n m) (a : State n m) : Prop :=
  0 < (a.scale:ℝ) ∧ a.realMatrix ∈ metricDomain H ∧
    (∀e, 0 ≤ (a.capacity e:ℝ) ∧ (a.capacity e:ℝ) ≤ 1 ∧
      (a.capacity e:ℝ) ≤ ramp H (a.scale:ℝ) a.realMatrix e) ∧
    ∀p, 0 ≤ slack H.left H.right (fun e => (a.capacity e:ℝ)+continuationBaseline m)
      (a.quality:ℝ) p

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GraphRealization
attribute [-instance] _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graph realization. -/

section

namespace AlgorithmicThinTrees.GraphStack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.MetricTests.RationalStep
open scoped BigOperators

instance poly_view : PolyTime view := by
  unfold view
  apply poly_reindex

end AlgorithmicThinTrees.GraphStack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_BoolPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bool programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
variable {α : Type*} {ea : α → Word}

def Realizes.or {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) :
    Realizes ea boolCode (fun a => decide (P a ∨ Q a)) :=
  (r.ite (constant ea boolCode true) s).congr (by intro a;simp)

abbrev boolsCode := listCode boolCode

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ScalarRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 AlgorithmicThinTrees.RationalGram

lemma squareScan_correct (k n : ℕ) (a : ℚ) (xs : List ℚ) :
    (squareScanStep^[k] (n,(a,xs))).2.2=
      xs++(base4Squares k n).map (fun v : ℕ => a*(v:ℚ)) := by
  induction k generalizing n a xs with
  | zero => simp [base4Squares]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    change (squareScanStep^[k] (n/4,(2*a,xs++List.replicate (n%4) a))).2.2=_
    rw [ih]
    simp only [base4Squares,List.map_append,List.map_replicate,Nat.cast_one,mul_one,
      List.map_map,Function.comp_def,List.append_assoc]
    congr 2
    apply List.map_congr_left
    intro x hx
    push_cast
    ring

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_BitBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation bit bound. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open CurrentKS.Realization
open CurrentKS.CleanRoutine KS.W23
open Stack GraphStack

variable {n m : ℕ}
def State.Parts (b : ℕ) (a : State n m) : Prop :=
  QParts b a.scale ∧ QParts b a.quality ∧ (∀i j,QParts b (a.matrix i j)) ∧
    ∀e,QParts b (a.capacity e)

end AlgorithmicThinTrees.MetricTests.RationalStep

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_RationalSigning
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational signing. -/

section

namespace AlgorithmicThinTrees.RationalSigning
open Matrix Finset CurrentKS
open RealMatrixBridge
open scoped MatrixOrder ComplexOrder
variable {d m : ℕ}

lemma entry_value (q : ℚ) : (entry q).value=q := by
  exact q.num_div_den

end AlgorithmicThinTrees.RationalSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_InverseRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

abbrev BackSolve := MatrixData×MatrixObject

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix AlgorithmicThinTrees

abbrev GramLift := MatrixData × MatrixObject

lemma firstColumn_data {n m : ℕ} (A : Matrix (Fin n) (Fin (m+1)) ℚ) :
    (matrixData A).map (fun row => row.getD 0 0)=List.ofFn (fun i => A i 0) := by
  simp only [matrixData,List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  exact getD_ofFn (A i) 0 0

def gramLiftData (p : GramLift) : MatrixData :=
  (RationalGram.scalarFactors (((matrixData p.2.2).getD 0 []).getD 0 0)⁻¹).map
    (fun a => ((matrixData p.2.2).map (fun row => row.getD 0 0)).map (fun q => a*q)) ++
    p.1.map (fun row => 0::row)

lemma gramLift_data {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (xs : List (Fin n → ℚ)) :
    gramLiftData (xs.map List.ofFn,⟨n+1,A⟩)=
      ((RationalGram.scalarFactors (A 0 0)⁻¹).map (fun a i => a*A i 0) ++
        xs.map (Fin.cons 0)).map List.ofFn := by
  unfold gramLiftData
  have hp : ((matrixData A).getD 0 []).getD 0 0=A 0 0 := matrix_entry_data A 0 0
  rw [hp,firstColumn_data]
  simp only [List.map_append,List.map_map,List.map_ofFn,Function.comp_def,List.ofFn_succ,
    Fin.cons_zero,Fin.cons_succ,List.map_cons, List.map_ofFn]

lemma gram_fold_correct (a : MatrixObject) :
    (schurHistoryData a).foldl (fun B A => gramLiftData (B,A)) []=
      (RationalGram.factorColumns a.1 a.2).map List.ofFn := by
  rcases a with ⟨n,A⟩
  induction n with
  | zero => simp [schurHistoryData,RationalGram.factorColumns]
  | succ n ih =>
    simp only [schurHistoryData,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih,gramLift_data]
    rfl

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

abbrev frameDataCode := prodCode natCode matrixCode
def Frame.data (a : Frame) := (a.d,matrixData a.v)
def frameCode (a : Frame) : Word := frameDataCode a.data
abbrev frameView : Realizes frameCode frameDataCode Frame.data :=
  (identity frameDataCode).reindex frameCode Frame.data (fun _ => rfl)
instance poly_frameView : PolyTime frameView := by
  unfold frameView
  apply poly_reindex

abbrev frameDim := frameView.then (first natCode matrixCode)
abbrev frameRows := frameView.then (second natCode matrixCode)

def complexField : Realizes ratCode vectorCode (fun q => [q,0]) :=
  ((identity ratCode).both (constant ratCode vectorCode [0])).then (consList ratCode)

lemma outerFields_data {d m : ℕ} (v : Fin m → Fin d → ℚ) (e : Fin m) :
    ((List.ofFn (v e)).map (fun q =>
      ((List.ofFn (v e)).map (fun r => [q*r,0])).flatten)).flatten=
      fieldValues (RationalSigning.input v) e := by
  refine Eq.trans ?_ (fieldValues_eq (RationalSigning.input v) e).symm
  simp only [List.map_ofFn,Function.comp_def,RationalSigning.input,RationalSigning.entry_value]

def FormFrame.data (a : FormFrame) := (a.form,matrixData a.v)

lemma factorColumns_data (a : MatrixObject) :
    (RationalGram.factorColumns a.1 a.2).map List.ofFn=
      matrixData (RationalGram.factorMatrix a.2)ᵀ := by
  change (RationalGram.factorColumns a.1 a.2).map List.ofFn=
      List.ofFn (fun i => List.ofFn ((RationalGram.factorColumns a.1 a.2).get i))
  have he : List.map List.ofFn (List.ofFn (RationalGram.factorColumns a.1 a.2).get)=
      List.ofFn (List.ofFn ∘ (RationalGram.factorColumns a.1 a.2).get) := List.map_ofFn
  simpa only [List.ofFn_get,Function.comp_def] using he

def FormFrame.whiten (a : FormFrame) : Frame :=
  ⟨(RationalGram.factorColumns a.form.1 (RationalInverse.inverse a.form.1 a.form.2)).length,
    a.m,FormSigning.whiten a.form.2 a.v⟩

def FramePair.stack (a : FramePair) : Frame :=
  ⟨a.a+a.b,a.m,fun e => StackedSigning.stack (a.u e) (a.v e)⟩
def pairCode (a : FramePair) : Word := prodCode frameCode frameCode (a.left,a.right)
abbrev pairView : Realizes pairCode (prodCode frameCode frameCode)
    (fun a => (a.left,a.right)) :=
  (identity (prodCode frameCode frameCode)).reindex pairCode
    (fun a => (a.left,a.right)) (fun _ => rfl)
instance poly_pairView : PolyTime pairView := by
  unfold pairView
  apply poly_reindex

abbrev pairLeft := pairView.then (first frameCode frameCode)
abbrev pairRight := pairView.then (second frameCode frameCode)

lemma stack_data {a b : ℕ} (u : Fin a → ℚ) (v : Fin b → ℚ) :
    List.ofFn u++List.ofFn v=List.ofFn (StackedSigning.stack u v) := by
  rw [List.ofFn_add]
  change List.ofFn u++List.ofFn v=
    (List.ofFn (fun i => StackedSigning.stack u v (Fin.castAdd b i)))++
      (List.ofFn (fun i => StackedSigning.stack u v (Fin.natAdd a i)))
  simp only [StackedSigning.stack_left,StackedSigning.stack_right]

def FormPair.whiten (p : FormPair) : FramePair :=
  ⟨p.left.whiten.d,p.right.whiten.d,p.m,p.left.whiten.v,p.right.whiten.v⟩

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GreedyTree
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greedy tree. -/

section

namespace AlgorithmicThinTrees.GreedyTree
open Finset StrongThinTree StrongThinTree.MultiGraph
variable {n m : ℕ}

def expand (G : MultiGraph n m) (A : Finset (Fin m)) (U : Finset (Fin n)) :
    Finset (Fin n) :=
  U ∪ (A.filter (fun e => G.right e ∈ U)).image G.left ∪
    (A.filter (fun e => G.left e ∈ U)).image G.right

def reach (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) (t : ℕ) : Finset (Fin n) :=
  (expand G A)^[t] {root}

lemma subset_expand (G : MultiGraph n m) (A : Finset (Fin m)) (U : Finset (Fin n)) :
    U ⊆ expand G A U := (subset_union_left).trans subset_union_left

lemma reach_succ (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) (t : ℕ) :
    reach G A root (t+1)=expand G A (reach G A root t) := Function.iterate_succ_apply' _ _ _

lemma reach_mono (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) :
    Monotone (reach G A root) :=
  monotone_nat_of_le_succ (fun t => (reach_succ G A root t).symm ▸ subset_expand G A _)

lemma reach_root (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) (t : ℕ) :
    root ∈ reach G A root t := reach_mono G A root (Nat.zero_le t) (mem_singleton_self root)

lemma expand_strict (G : MultiGraph n m) (A : Finset (Fin m)) (hc : G.Connected A)
    (U : Finset (Fin n)) (hu : U.Nonempty) (hu' : U ≠ univ) : U ⊂ expand G A U := by
  obtain ⟨e,he⟩ := hc U hu hu'
  obtain ⟨hea,hcut⟩ := mem_filter.mp he
  apply ssubset_iff_subset_ne.mpr
  refine ⟨subset_expand G A U,?_⟩
  intro heq
  rcases hcut with ⟨hl,hr⟩ | ⟨hr,hl⟩
  · apply hr
    rw [heq]
    exact mem_union_right _ (mem_image.mpr ⟨e,mem_filter.mpr ⟨hea,hl⟩,rfl⟩)
  · apply hl
    rw [heq]
    exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨e,mem_filter.mpr ⟨hea,hr⟩,rfl⟩))

lemma reach_full (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n)
    (hc : G.Connected A) : reach G A root n=univ := by
  by_contra hne
  have hstrict (i : ℕ) (hi : i ≤ n) : reach G A root i ≠ univ := by
    intro he
    apply hne
    exact eq_univ_iff_forall.mpr (fun v => reach_mono G A root hi (he ▸ mem_univ v))
  have hcard : ∀i, i ≤ n → i+1 ≤ (reach G A root i).card := by
    intro i hi
    induction i with
    | zero => simp [reach]
    | succ i ih =>
      have hj := ih (by omega)
      have hs := card_lt_card (expand_strict G A hc (reach G A root i)
        ⟨root,reach_root G A root i⟩ (hstrict i (by omega)))
      rw [reach_succ]
      omega
  have hh := (hcard n le_rfl).trans (card_le_univ _)
  simp only [Fintype.card_fin] at hh
  omega

lemma reach_same (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) (t : ℕ) :
    ∀v ∈ reach G A root t, G.Same A v root := by
  induction t with
  | zero =>
    intro v hv
    have he : v=root := mem_singleton.mp hv
    subst v
    exact G.same_refl A root
  | succ t ih =>
    intro v hv
    rw [reach_succ] at hv
    rcases mem_union.mp hv with hv|hv
    · rcases mem_union.mp hv with hv|hv
      · exact ih v hv
      · obtain ⟨e,he,rfl⟩ := mem_image.mp hv
        obtain ⟨he,hu⟩ := mem_filter.mp he
        exact G.same_trans (G.same_endpoints he) (ih _ hu)
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hv
      obtain ⟨he,hu⟩ := mem_filter.mp he
      exact G.same_trans (G.same_symm (G.same_endpoints he)) (ih _ hu)

lemma connected_iff_reach (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) :
    G.Connected A ↔ reach G A root n=univ := by
  refine ⟨reach_full G A root,fun h => ?_⟩
  rw [G.connected_iff_same]
  intro u v
  exact G.same_trans (reach_same G A root n u (h ▸ mem_univ _))
    (G.same_symm (reach_same G A root n v (h ▸ mem_univ _)))

def connected (G : MultiGraph n m) (A : Finset (Fin m)) : Bool :=
  if hn : 0 < n then decide (reach G A ⟨0,hn⟩ n=univ) else true

lemma connected_correct (G : MultiGraph n m) (A : Finset (Fin m)) :
    connected G A=true ↔ G.Connected A := by
  unfold connected
  split_ifs with hn
  · simpa only [decide_eq_true_eq] using (connected_iff_reach G A ⟨0,hn⟩).symm
  · have hzero : n=0 := by omega
    subst n
    simp only [true_iff]
    intro S hS _
    obtain ⟨v,_⟩ := hS
    exact Fin.elim0 v

def eraseIf (G : MultiGraph n m) (A : Finset (Fin m)) (e : Fin m) : Finset (Fin m) :=
  if connected G (A.erase e) then A.erase e else A

def deletePass (G : MultiGraph n m) (A : Finset (Fin m)) (es : List (Fin m)) : Finset (Fin m) :=
  es.foldl (eraseIf G) A

def tree (G : MultiGraph n m) : Finset (Fin m) := deletePass G univ (List.finRange m)

end AlgorithmicThinTrees.GreedyTree
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GreedyRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greedy realization. -/

section

namespace AlgorithmicThinTrees.GreedyTree.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Finset StrongThinTree
open GraphStack

structure Subgraph where
  graph : Graph
  A : Finset (Fin graph.m)

def Subgraph.bits (s : Subgraph) := List.ofFn (fun e => decide (e ∈ s.A))
def subgraphCode (s : Subgraph) : Word := prodCode graphCode boolsCode (s.graph,s.bits)
abbrev subgraphView : Realizes subgraphCode (prodCode graphCode boolsCode) (fun s => (s.graph,s.bits)) :=
  (identity (prodCode graphCode boolsCode)).reindex subgraphCode (fun s => (s.graph,s.bits)) (fun _ => rfl)
instance poly_subgraphView : PolyTime subgraphView := by
  unfold subgraphView
  apply poly_reindex

abbrev subgraphGraph := subgraphView.then (first graphCode boolsCode)
abbrev subgraphBits := subgraphView.then (second graphCode boolsCode)

abbrev SEdge := Σ s : Subgraph, Fin s.graph.m
abbrev sedgeCode := finFamilyCode subgraphCode (fun s : Subgraph => s.graph.m)
abbrev sedgeContext : Realizes sedgeCode subgraphCode (fun s : SEdge => s.1) := familyFirst
abbrev sedgeIndex : Realizes sedgeCode natCode (fun s : SEdge => s.2.val) := familyIndex

structure ReachState where
  subgraph : Subgraph
  U : Finset (Fin subgraph.graph.n)

def ReachState.bits (s : ReachState) := List.ofFn (fun v => decide (v ∈ s.U))
def reachCode (s : ReachState) : Word := prodCode subgraphCode boolsCode (s.subgraph,s.bits)
abbrev reachView : Realizes reachCode (prodCode subgraphCode boolsCode) (fun s => (s.subgraph,s.bits)) :=
  (identity (prodCode subgraphCode boolsCode)).reindex reachCode (fun s => (s.subgraph,s.bits)) (fun _ => rfl)
instance poly_reachView : PolyTime reachView := by
  unfold reachView
  apply poly_reindex

abbrev reachSubgraph := reachView.then (first subgraphCode boolsCode)
abbrev reachBits := reachView.then (second subgraphCode boolsCode)
abbrev Vertex := Σ s : ReachState, Fin s.subgraph.graph.n
abbrev vertexCode := finFamilyCode reachCode (fun s : ReachState => s.subgraph.graph.n)
abbrev vertexContext : Realizes vertexCode reachCode (fun v : Vertex => v.1) := familyFirst
abbrev vertexIndex : Realizes vertexCode natCode (fun v : Vertex => v.2.val) := familyIndex

abbrev Arc := Σ v : Vertex, Fin v.1.subgraph.graph.m
abbrev arcCode := finFamilyCode vertexCode (fun v : Vertex => v.1.subgraph.graph.m)
abbrev arcVertex : Realizes arcCode vertexCode (fun a : Arc => a.1) := familyFirst
abbrev arcNumber : Realizes arcCode natCode (fun a : Arc => a.2.val) := familyIndex
abbrev arcState := arcVertex.then vertexContext

def arcSubedge : Realizes arcCode sedgeCode (fun a => ⟨a.1.1.subgraph,a.2⟩) :=
  ((arcState.then reachSubgraph).both arcNumber).changeOutput sedgeCode
    (fun a => ⟨a.1.1.subgraph,a.2⟩) (fun _ => rfl)

def arcEdge : Realizes arcCode GraphStack.edgeCode (fun a => ⟨a.1.1.subgraph.graph,a.2⟩) :=
  ((arcState.then reachSubgraph |>.then subgraphGraph).both arcNumber).changeOutput
    GraphStack.edgeCode (fun a => ⟨a.1.1.subgraph.graph,a.2⟩) (fun _ => rfl)

def ReachState.next (s : ReachState) : ReachState :=
  ⟨s.subgraph,expand s.subgraph.graph.G s.subgraph.A s.U⟩
abbrev initVertexCode := finFamilyCode subgraphCode (fun s : Subgraph => s.graph.n)

def Subgraph.start (s : Subgraph) : ReachState := ⟨s,univ.filter (fun v => v.val=0)⟩

def Walk (s : Subgraph) : ReachState := ReachState.next^[s.graph.n] s.start

lemma walk_eq (s : Subgraph) : Walk s =
    ⟨s,(expand s.graph.G s.A)^[s.graph.n] (univ.filter (fun v => v.val=0))⟩ := by
  have he (k : ℕ) : ReachState.next^[k] s.start =
      ⟨s,(expand s.graph.G s.A)^[k] (univ.filter (fun v => v.val=0))⟩ := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply'];rfl
  exact he _

lemma walk_connected (s : Subgraph) : ((Walk s).U=univ) ↔ s.graph.G.Connected s.A := by
  rw [walk_eq]
  dsimp only
  by_cases hn : 0 < s.graph.n
  · let root : Fin s.graph.n := ⟨0,hn⟩
    have he : (univ.filter (fun v : Fin s.graph.n => v.val=0))={root} := by
      ext v;simp [Fin.ext_iff,root]
    rw [he]
    exact (connected_iff_reach s.graph.G s.A root).symm
  · have hn0 : s.graph.n=0 := by omega
    constructor
    · intro _ S hS hS'
      obtain ⟨v,_⟩ := hS
      exact (Nat.not_lt_zero v.val (hn0 ▸ v.isLt)).elim
    · intro _
      apply eq_univ_iff_forall.mpr
      intro v
      exact (Nat.not_lt_zero v.val (hn0 ▸ v.isLt)).elim

abbrev EraseInput := Subgraph × ℕ
abbrev eraseInputCode := prodCode subgraphCode natCode
abbrev eraseContext := first subgraphCode natCode
abbrev eraseIndex := second subgraphCode natCode
abbrev EraseEdge := Σ p : EraseInput, Fin p.1.graph.m
abbrev eraseEdgeCode := finFamilyCode eraseInputCode (fun p : EraseInput => p.1.graph.m)
abbrev eraseEdgeContext : Realizes eraseEdgeCode eraseInputCode (fun p : EraseEdge => p.1) := familyFirst
abbrev eraseEdgeIndex : Realizes eraseEdgeCode natCode (fun p : EraseEdge => p.2.val) := familyIndex

def eraseSubedge : Realizes eraseEdgeCode sedgeCode (fun p => ⟨p.1.1,p.2⟩) :=
  ((eraseEdgeContext.then eraseContext).both eraseEdgeIndex).changeOutput sedgeCode
    (fun p => ⟨p.1.1,p.2⟩) (fun _ => rfl)

def erase (p : EraseInput) : Subgraph := ⟨p.1.graph,p.1.A.filter (fun e => e.val ≠ p.2)⟩

def deleteAt (p : EraseInput) : Subgraph :=
  if connected (erase p).graph.G (erase p).A then erase p else p.1

lemma deleteAt_fin (g : Graph) (A : Finset (Fin g.m)) (e : Fin g.m) :
    deleteAt (⟨g,A⟩,e.val)=⟨g,eraseIf g.G A e⟩ := by
  have he : erase (⟨g,A⟩,e.val)=⟨g,A.erase e⟩ := by
    change (Subgraph.mk g (A.filter (fun i => i.val ≠ e.val)))=Subgraph.mk g (A.erase e)
    congr 1
    ext i
    simp [mem_erase,Fin.ext_iff,and_comm]
  unfold deleteAt
  rw [he]
  change (if connected g.G (A.erase e) then Subgraph.mk g (A.erase e) else Subgraph.mk g A)=_
  unfold eraseIf
  split_ifs <;> rfl

lemma fold_deletes (g : Graph) (A : Finset (Fin g.m)) (es : List (Fin g.m)) :
    (es.map Fin.val).foldl (fun s i => deleteAt (s,i)) ⟨g,A⟩=⟨g,deletePass g.G A es⟩ := by
  induction es generalizing A with
  | nil => rfl
  | cons e es ih =>
    rw [List.map_cons,List.foldl_cons,deleteAt_fin,ih]
    rfl

end AlgorithmicThinTrees.GreedyTree.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_WordHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word head. -/

section

namespace CurrentKS.WordHead
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine

def dispatch (_ : Fin 1) (heads : Fin 3 → Fin 3) (_ : Bool) : KS.W01.FixedStack.Instruction 3 1 :=
  ⟨none,Vector.ofFn (fun j => if j=1 then .push (decide (heads 0=2)) else .stay)⟩
end CurrentKS.WordHead

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input arrays. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
abbrev eCode (x : E) : Word := x.val.encode
abbrev bCode (x : B) : Word := x.val.encode

def eFields (x : ExplicitInput) : List ℕ :=
  [x.n,x.m,x.k] ++ (List.ofFn fun i => [(x.graph.left i).val,(x.graph.right i).val]).flatten

abbrev eEdgeCode := finFamilyCode eCode (fun x : E => x.val.m)
abbrev eeInput : Realizes eEdgeCode eCode (fun x => x.1) := familyFirst
abbrev eeIndex : Realizes eEdgeCode natCode (fun x => x.2.val) := familyIndex
abbrev bRecCode := finFamilyCode bCode (fun x : B => x.val.p)
abbrev brInput : Realizes bRecCode bCode (fun x => x.1) := familyFirst
abbrev brIndex : Realizes bRecCode natCode (fun x => x.2.val) := familyIndex

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_OrderedGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered graph. -/

section

namespace AlgorithmicThinTrees.OrderedGraph
open Finset StrongThinTree StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

def restrict (F : Finset (Fin m)) : MultiGraph n F.card where
  left e := G.left (edgeEmbedding F e)
  right e := G.right (edgeEmbedding F e)
  loopless e := G.loopless (edgeEmbedding F e)
end AlgorithmicThinTrees.OrderedGraph
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_SelectionRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Finset
open AlgorithmicThinTrees.OrderedGraph

variable {α : Type*}

lemma maskArray_data {m : ℕ} (A : Finset (Fin m)) (f : Fin m → α) (z : α) :
    (zipDefault (fun q : Bool×α => if q.1 then [q.2] else []) false z
      (List.ofFn (fun e => decide (e ∈ A)),List.ofFn f)).flatten=
        List.ofFn (fun i => f (edgeEmbedding A i)) := by
  rw [zipDefault_ofFn]
  have hh : ∀es : List (Fin m),
      (es.map (fun e => if decide (e ∈ A) then [f e] else [])).flatten=
        (es.filter (fun e => decide (e ∈ A))).map f := by
    intro es
    induction es with
    | nil => rfl
    | cons e es ih => by_cases he : e ∈ A <;> simp_all
  dsimp only
  rw [List.ofFn_eq_map,hh,sorted_selected,List.map_ofFn]
  rfl

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_IterationPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration potential. -/

section

noncomputable section
namespace AlgorithmicThinTrees.Iteration
open StrongThinTree

def potential (r : ℕ) : ℝ := Real.exp (lossB*(1-errorU r))

end AlgorithmicThinTrees.Iteration
end

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input dispatch. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
abbrev goodCode (x : Good) : Word := x.val.encode
abbrev largeCode (x : Large) : Word := x.val.encode
lemma valid_n {x : AlgorithmicThinTrees.Input} (hv : Valid x) : 1≤x.n := by
  cases x <;> exact hv.1

def isBinary : AlgorithmicThinTrees.Input → Bool
  | .explicit _ => false
  | .binary _ => true

def asBinary (x : {x : Large // isBinary x.val = true}) : B := by
  rcases x with ⟨⟨x|x,hvalid,hn⟩,hb⟩
  · cases hb
  · exact ⟨x,hn,hvalid.2⟩
def asExplicit (x : {x : Large // ¬isBinary x.val = true}) : E := by
  rcases x with ⟨⟨x|x,hvalid,hn⟩,hb⟩
  · exact ⟨x,hn,hvalid.2⟩
  · exact (hb rfl).elim

def makeLarge (x : {x : Good // x.val.n ≠ 1}) : Large := by
  refine ⟨x.val.val,x.val.property,?_⟩
  have hv : 1 ≤ x.val.val.n := valid_n x.val.property
  have hn := x.property
  omega

def inputFields : AlgorithmicThinTrees.Input → List ℕ
  | .explicit x => eFields x
  | .binary x => bFields x

end AlgorithmicThinTrees.InputStack
end

end OAI
end


