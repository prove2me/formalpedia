-- Prove2me | Definitions.Def_OAIQ241TT005
-- name    : OAIQ241TT005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:51:08.789185+00:00
-- url     : https://prove2.me/theorems/44be282d-57fd-47b9-b47f-e9cfb1fa40fa
-- title:
--   Definitions bundle OAIQ241TT005 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 678 declarations of OpenAI's Lean: 432 definitions, 9 inductive types or structures and 237 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.GraphStack.numEdges`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Coordinate`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Edge`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.MaskEdge`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.MaskInput`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem.active`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem.forms`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem.graph`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem.normalization`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem.q`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem.scales`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.Problem.state`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.context`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.coordCode`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.coordEdge`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.coordIndex`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.edgeCode`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.problemCode`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.problemView`, `OAI.AlgorithmicThinTrees.GraphicHalf.fullColumns`, `OAI.AlgorithmicThinTrees.GraphicHalf.scaledColumns`, `OAI.AlgorithmicThinTrees.GraphicHalf.scaledForm`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Loop`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Loop.data`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Loop.next`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Loop.params`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Loop.updated`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Loop.vector`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.LoopEdge`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Params`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Params.data`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Params.pencil`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Params.searchState`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Point`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.Point.data`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.beBudget`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.beE`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.beGraphEdge`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.bePoint` and 401 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Arithmetic_ArithmeticEncodingSize`, `MatrixSigning_Arithmetic_BinaryAddressLookup`, `MatrixSigning_Arithmetic_BinaryDivision`, `MatrixSigning_Arithmetic_BorrowSubtractor`, `MatrixSigning_Arithmetic_DivisionInput`, `MatrixSigning_Arithmetic_DivisionMachine`, `MatrixSigning_Arithmetic_FloorRationalMachine`, `MatrixSigning_Arithmetic_MultiplicationInitialize`, `MatrixSigning_Arithmetic_NegativeDivision`, `MatrixSigning_Arithmetic_RationalDivisionStages`, `MatrixSigning_Arithmetic_RationalMagnitudeSetup`, `MatrixSigning_Arithmetic_RationalMagnitudeSign`, `MatrixSigning_Arithmetic_RationalMultiplicationMachine`, `MatrixSigning_Arithmetic_RationalSignAction`, `MatrixSigning_Arithmetic_RationalSignClassifier`, `MatrixSigning_Arithmetic_RationalSubtractProgram`, `MatrixSigning_Arithmetic_SparseScalarNodes`, `MatrixSigning_Arithmetic_ZeroPaddedRow`, `MatrixSigning_Encoding_FrameDecoder`, `MatrixSigning_Encoding_FramedArrayPorts`, `MatrixSigning_Encoding_FramedArrayPrefix`, `MatrixSigning_Encoding_FramedArrayReplacement`, `MatrixSigning_Encoding_FramedArrayReplacementPorts`, `MatrixSigning_Encoding_FramedArrayRetrieval`, `MatrixSigning_Encoding_FramedArraySkip`, `MatrixSigning_Encoding_ReusableArrayLookup`, `MatrixSigning_Encoding_SignedQuotientSerializer`, `MatrixSigning_Encoding_UnsignedPairSerializer`, `MatrixSigning_Encoding_WireAppend`, `MatrixSigning_Encoding_WireProgramPrimitives`, `MatrixSigning_Encoding_WordOperations`, `MatrixSigning_Encoding_ZeroArrayConstructor`, `MatrixSigning_Machines_BinaryMachine`, `MatrixSigning_Machines_BinaryStackMoves`, `MatrixSigning_Machines_BinaryToUnary`, `MatrixSigning_Machines_BinaryToUnaryDeterministic`, `MatrixSigning_Machines_BinaryToUnaryMachine`, `MatrixSigning_Machines_BinaryToUnaryRun`, `MatrixSigning_Machines_ControllerReachable`, `MatrixSigning_Machines_FixedCanonicalize`, `MatrixSigning_Machines_FixedDotBounds`, `MatrixSigning_Machines_FixedDotControl`, `MatrixSigning_Machines_FixedDotMachine`, `MatrixSigning_Machines_FixedDotModel`, `MatrixSigning_Machines_FixedDotPrimitives`, `MatrixSigning_Machines_FixedLoop`, `MatrixSigning_Machines_FixedSequential`, `MatrixSigning_Machines_MachineTransport`, `MatrixSigning_Machines_SchurCellMachine`, `MatrixSigning_Machines_SchurCounters`, `MatrixSigning_Machines_SchurDimension`, `MatrixSigning_Machines_SchurEntryMachine`, `MatrixSigning_Machines_SchurReadStage`, `MatrixSigning_Machines_SchurTableMachine`, `MatrixSigning_Machines_SignedFloorMachine`, `MatrixSigning_Machines_SignedFloorModel`, `MatrixSigning_Machines_TerminalSparseAssembly`, `MatrixSigning_Machines_TerminalVectorReplace`, `MatrixSigning_Machines_TerminalZeroVector`, `MatrixSigning_Matrices_DenseElimination`, `MatrixSigning_Matrices_DenseMatrixSerialization`, `MatrixSigning_Matrices_EliminationCallBounds`, `MatrixSigning_Matrices_MatrixAddressArithmetic`, `MatrixSigning_Matrices_MatrixReadProgram`, `MatrixSigning_Matrices_PivotControllerBody`, `MatrixSigning_Matrices_PivotControllerCorrectness`, `MatrixSigning_Matrices_PivotControllerLoop`, `MatrixSigning_Matrices_PivotDecisionMachine`, `MatrixSigning_Matrices_PivotDecisionPorts`, `MatrixSigning_Matrices_PivotHistory`, `MatrixSigning_Matrices_PivotHistoryBounds`, `MatrixSigning_Matrices_PivotHistoryMachine`, `MatrixSigning_Matrices_PivotReplayLoop`, `MatrixSigning_Matrices_PivotRowBody`, `MatrixSigning_Matrices_PivotRowFinish`, `MatrixSigning_Matrices_PivotRowInitialize`, `MatrixSigning_Matrices_PivotRowLoop`, `MatrixSigning_Matrices_PivotTerminalMachine`, `MatrixSigning_Matrices_RowDotBody`, `MatrixSigning_Matrices_RowDotBounds`, `MatrixSigning_Matrices_RowDotControl`, `MatrixSigning_Matrices_RowDotCounter`, `MatrixSigning_Matrices_RowDotMachine`, `MatrixSigning_Matrices_RowDotModel`, `MatrixSigning_Matrices_RowDotPrimitives`, `MatrixSigning_Matrices_SavedPivotPacketMachine`, `MatrixSigning_Matrices_UniformElimination`, `MatrixSigning_Matrices_UniformEliminationHeight`, `MatrixSigning_Optimization_EliminationWitnessHeight`, `MatrixSigning_Optimization_PivotDescentMachine`, `MatrixSigning_Optimization_PivotWitnessMachine`, `MatrixSigning_Optimization_SchurWitnessHead`, `MatrixSigning_Optimization_SignedFloorInterface`, `MatrixSigning_Optimization_StoredWitnessLift`, `MatrixSigning_Potential_SchurLoopState`, `MatrixSigning_Realization_ArrayRealization`, `MatrixSigning_Realization_DependentBranchRealization`, `MatrixSigning_Realization_DependentRealization`, `MatrixSigning_Realization_FixedSubroutineBridge`, `MatrixSigning_Realization_FloorCleanRoutine`, `MatrixSigning_Realization_FramedMapRoutine`, `MatrixSigning_Realization_MatrixStructureRealization`, `MatrixSigning_Realization_NaturalRealization`, `MatrixSigning_Realization_PSDCleanRoutine`, `MatrixSigning_Realization_PencilArrayRealization`, `MatrixSigning_Realization_PencilCompileRealization`, `MatrixSigning_Realization_Realization`, `MatrixSigning_Realization_RoundedStepRealization`, `MatrixSigning_Realization_SearchRealization`, `MatrixSigning_Realization_StoredPSDRealization`, `MatrixSigning_Realization_ValueDataRealization`, `MatrixSigning_Realization_ValueEvalRealization`, `MatrixSigning_Realization_VectorRealization`, `ThinTrees_Arithmetic_ArraySums`, `ThinTrees_Arithmetic_BinaryArithmetic`, `ThinTrees_Arithmetic_UnaryArithmetic`, `ThinTrees_Arithmetic_UnaryRoot`, `ThinTrees_Continuation_Coordinates`, `ThinTrees_Continuation_Encoding`, `ThinTrees_Continuation_Interior`, `ThinTrees_Continuation_Iteration`, `ThinTrees_Continuation_Loop`, `ThinTrees_Continuation_Pencil`, `ThinTrees_Continuation_PencilCorrectness`, `ThinTrees_Continuation_Realization`, `ThinTrees_Continuation_Search`, `ThinTrees_Continuation_Start`, `ThinTrees_Encoding_GraphRealization`, `ThinTrees_Normalization_Algorithm`, `ThinTrees_Normalization_Realization`, `ThinTrees_Pencil_AffinePencil`, `ThinTrees_Pencil_BlockAssembly`, `ThinTrees_Pencil_FiniteFamilies`, `ThinTrees_Pencil_MatrixConstraintRealization`, `ThinTrees_Pencil_Parameters`, `ThinTrees_Pencil_PointPrograms`, `ThinTrees_Pencil_RationalAffineEval`, `ThinTrees_Pencil_Realization`, `ThinTrees_Pencil_ScalarConstraintRealization`, `ThinTrees_Pencil_SearchRealization`, `ThinTrees_RationalMatrix_MatrixRealization`, `ThinTrees_Sparsification_GraphicHalf`, `ThinTrees_Sparsification_GraphicNormalization`, `ThinTrees_Sparsification_Realization`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`; the bundles `OAIQ241TT000` and `OAIQ241TT001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ241TT007`, `OAIQ241TT008` and `OAIQ241TT009`; the statement `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT000
import Definitions.Def_OAIQ241TT001

section
-- module Solutions.OAIQ241_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ArithmeticEncodingSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W01

theorem intPayload_le_natAbs (n : ℤ) : intPayload n ≤ n.natAbs := by
  cases n <;> simp [intPayload]

theorem natAbs_le_intPayload_add_one (n : ℤ) : n.natAbs ≤ intPayload n + 1 := by
  cases n <;> simp [intPayload]

theorem natAbs_size_le_payload_size_add_one (n : ℤ) :
    Nat.size n.natAbs ≤ Nat.size (intPayload n) + 1 := by
  apply Nat.size_le.mpr
  have hn := natAbs_le_intPayload_add_one n
  have hp := Nat.lt_size_self (intPayload n)
  have hpos : 0 < 2 ^ Nat.size (intPayload n) := pow_pos (by decide) _
  rw [pow_succ]
  omega

end KS.W01

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryMachine
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29

theorem BinaryMachine.run_halted (M : BinaryMachine) (c : Config M.states)
    (h : c.state = none) (bits : List Bool) : M.run c bits = c := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simpa [BinaryMachine.run, M.step_halted c h b] using ih

end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedSequential
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedLoop.dispatch_body _root_.OAI.KS.W29.FixedLoop.dispatch_guard _root_.OAI.KS.W29.FixedLoop.loop_initial _root_.OAI.KS.W29.FixedLoop.loop_input _root_.OAI.KS.W29.FixedLoop.loop_output _root_.OAI.KS.W29.FixedLoop.loop_states _root_.OAI.KS.W29.FixedLoop.loop_toMachine _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29.FixedSequential

theorem activeFor_append {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (first rest : List Bool) :
    ActiveFor P c (first ++ rest) ↔
      ActiveFor P c first ∧ ActiveFor P (P.toMachine.run c first) rest := by
  induction first generalizing c with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons b bs ih =>
      simp only [List.cons_append, ActiveFor, KS.W01.FixedStack.Machine.run, ih (P.toMachine.step c b), and_assoc]

theorem activeFor_liftLeft {k : Nat} (P Q : Program k)
    (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool) (h : ActiveFor P c bits) :
    ActiveFor (compose P Q) (liftLeft P Q c) bits := by
  induction bits generalizing c with
  | nil => trivial
  | cons b bs ih =>
      refine ⟨Option.some_ne_none _, ?_⟩
      rw [step_liftLeft P Q c b h.1]
      exact ih _ h.2

theorem activeFor_liftRight {k : Nat} (P Q : Program k)
    (c : KS.W01.FixedStack.Config k Q.states) (bits : List Bool) (h : ActiveFor Q c bits) :
    ActiveFor (compose P Q) (liftRight P Q c) bits := by
  induction bits generalizing c with
  | nil => trivial
  | cons b bs ih =>
      refine ⟨?_, ?_⟩
      · have hc := h.1
        cases hs : c.state with
        | none => exact (hc hs).elim
        | some state =>
            change c.state.map (rightState P Q) ≠ none
            rw [hs]
            exact Option.some_ne_none _
      · rw [step_liftRight]
        exact ih _ h.2

theorem compose_haltsAfter {k : Nat} (P Q : Program k)
    (c : KS.W01.FixedStack.Config k P.states) (first second : List Bool)
    (hfirst : HaltsAfter P c first)
    (hsecond : HaltsAfter Q ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ second) :
    HaltsAfter (compose P Q) (liftLeft P Q c) (first ++ second) := by
  constructor
  · apply (activeFor_append _ _ _ _).2
    refine ⟨activeFor_liftLeft P Q c first hfirst.1, ?_⟩
    rw [run_liftLeft P Q c first hfirst.1]
    have he : liftLeft P Q (P.toMachine.run c first) =
        liftRight P Q ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ := by
      simp [liftLeft, liftRight, hfirst.2]
    rw [he]
    exact activeFor_liftRight P Q _ second hsecond.1
  · rw [run_compose P Q c first second hfirst]
    change (Q.toMachine.run ⟨some Q.initial, (P.toMachine.run c first).«stacks»⟩ second).state.map
      (rightState P Q) = none
    exact congrArg (Option.map (rightState P Q)) hsecond.2

def HaltsFromWithin {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (fuel : Nat) : Prop :=
  ∀ bits : List Bool, bits.length = fuel → (P.toMachine.run c bits).state = none

theorem haltsFromWithin_mono {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states)
    {small large : Nat} (h : HaltsFromWithin P c small) (hle : small ≤ large) :
    HaltsFromWithin P c large := by
  intro bits hbits
  have htake : (bits.take small).length = small := by
    simp [List.length_take, hbits, Nat.min_eq_left hle]
  have hh := h (bits.take small) htake
  conv_lhs => rw [← List.take_append_drop small bits]
  erw [KS.W01.FixedStack.Machine.run_append,
    KS.W01.FixedStack.Machine.run_halted P.toMachine _ hh]
  exact hh

end KS.W29.FixedSequential

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedLoop
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29.FixedLoop
open KS.W29.FixedSequential (Program ofMachine ActiveFor HaltsAfter fetch)
open KS.W01.FixedStack (Config Instruction observedHeads)

theorem run_body_within {k : Nat} (P : Program k) (guard) (c : KS.W01.FixedStack.Config k P.states)
    (fuel : Nat) (h : KS.W29.FixedSequential.HaltsFromWithin P c fuel)
    (bits : List Bool) (hlen : fuel ≤ bits.length) :
    ∃ first rest : List Bool, bits = first ++ rest ∧ first.length ≤ fuel ∧
      HaltsAfter P c first ∧
      (loop P guard).toMachine.run (liftBody P c) bits =
        (loop P guard).toMachine.run
          ⟨some (guardState P), (P.toMachine.run c (bits.take fuel)).«stacks»⟩ rest := by
  have ht : (bits.take fuel).length = fuel := by
    simp [List.length_take, Nat.min_eq_left hlen]
  obtain ⟨first, leftover, heq, hf⟩ :=
    KS.W29.FixedSequential.exists_halting_prefix P c (bits.take fuel) (h _ ht)
  have hfl : first.length ≤ fuel := by
    have hh := congrArg List.length heq
    simp only [List.length_append, ht] at hh
    omega
  have hwhole : bits = first ++ (leftover ++ bits.drop fuel) := by
    calc
      bits = bits.take fuel ++ bits.drop fuel := (List.take_append_drop fuel bits).symm
      _ = first ++ (leftover ++ bits.drop fuel) := by rw [heq, List.append_assoc]
  have hout : P.toMachine.run c (bits.take fuel) = P.toMachine.run c first := by
    erw [heq, KS.W01.FixedStack.Machine.run_append]
    exact P.toMachine.run_halted _ hf.2 leftover
  refine ⟨first, leftover ++ bits.drop fuel, hwhole, hfl, hf, ?_⟩
  rw [hout]
  conv_lhs => rw [hwhole]
  exact run_body_then P guard c first _ hf

end KS.W29.FixedLoop

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryDivision
attribute [-simp] _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19

theorem signedBitsValue_intPayload (z : ℤ) :
    signedBitsValue (negativeOfInt z) (Computability.encodeNat (KS.W01.intPayload z)) = z := by
  cases z <;> simp [negativeOfInt, signedBitsValue, KS.W01.intPayload, bitsValue_encodeNat]

theorem divideSignedBits_intPayload_quotient (z : ℤ) (d : ℕ) (hd : 0 < d) :
    signedBitsValue (negativeOfInt z)
      (divideSignedBits (negativeOfInt z) (Computability.encodeNat d)
        (Computability.encodeNat (KS.W01.intPayload z))).1 = z / (d : ℤ) := by
  simpa only [bitsValue_encodeNat, signedBitsValue_intPayload] using
    divideSignedBits_quotient (negativeOfInt z) (Computability.encodeNat d)
      (Computability.encodeNat (KS.W01.intPayload z)) (by simpa only [bitsValue_encodeNat] using hd)

end KS.W19

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryToUnaryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.BinaryToUnary
open KS.W01.FixedStack KS.W29

def instruction (next : Option (Fin 8)) (a b c : StackAction) :
    KS.W01.FixedStack.Instruction 3 8 :=
  ⟨next, Vector.ofFn ![a, b, c]⟩

def dispatch (s : Fin 8) (heads : Fin 3 → Fin 3) (_coin : Bool) :
    KS.W01.FixedStack.Instruction 3 8 :=
  if s = 0 then
    if heads 0 = 0 then instruction (some 1) .stay .stay .stay
    else instruction (some 0) .pop .stay (.push (heads 0 == 2))
  else if s = 1 then
    if heads 2 = 0 then instruction none .stay .stay .stay
    else instruction (some (doubleState (heads 2 == 2))) .stay .stay .pop
  else if s = 2 ∨ s = 5 then
    let b := s == 5
    if heads 1 = 0 then instruction (some (restoreState b)) .stay .stay .stay
    else instruction (some (secondState b)) (.push true) .pop .stay
  else if s = 3 ∨ s = 6 then
    instruction (some (doubleState (s == 6))) (.push true) .stay .stay
  else
    let b := s == 7
    if heads 0 = 0 then
      instruction (some 1) .stay (if b then .push true else .stay) .stay
    else instruction (some (restoreState b)) .pop (.push true) .stay

def machine : Machine := compile (0 : Fin 8) (0 : Fin 3) (1 : Fin 3) dispatch

def cfg (s : Option (Fin 8)) (scratch counter unread : List Bool) :
    KS.W01.FixedStack.Config 3 8 := ⟨s, ![scratch, counter, unread]⟩

theorem init_eq (xs : List Bool) : machine.init xs = cfg (some 0) xs [] [] := by
  change KS.W01.FixedStack.Config.mk (some (0 : Fin 8)) _ =
    KS.W01.FixedStack.Config.mk (some (0 : Fin 8)) _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem reverse_step (b coin : Bool) (xs ys zs : List Bool) :
    machine.step (cfg (some 0) (b :: xs) ys zs) coin =
      cfg (some 0) xs ys (b :: zs) := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem reverse_done (coin : Bool) (ys zs : List Bool) :
    machine.step (cfg (some 0) [] ys zs) coin = cfg (some 1) [] ys zs := by
  unfold machine
  erw [step_compile]
  change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem guard_done (coin : Bool) (counter : List Bool) :
    machine.step (cfg (some 1) [] counter []) coin = cfg none [] counter [] := by
  unfold machine
  erw [step_compile]
  change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem guard_step (b coin : Bool) (counter unread : List Bool) :
    machine.step (cfg (some 1) [] counter (b :: unread)) coin =
      cfg (some (doubleState b)) [] counter unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem double_step (b coin : Bool) (scratch counter unread : List Bool) :
    machine.step (cfg (some (doubleState b)) scratch (true :: counter) unread) coin =
      cfg (some (secondState b)) (true :: scratch) counter unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem second_step (b coin : Bool) (scratch counter unread : List Bool) :
    machine.step (cfg (some (secondState b)) scratch counter unread) coin =
      cfg (some (doubleState b)) (true :: scratch) counter unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem double_done (b coin : Bool) (scratch unread : List Bool) :
    machine.step (cfg (some (doubleState b)) scratch [] unread) coin =
      cfg (some (restoreState b)) scratch [] unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem restore_step (b coin : Bool) (scratch counter unread : List Bool) :
    machine.step (cfg (some (restoreState b)) (true :: scratch) counter unread) coin =
      cfg (some (restoreState b)) scratch (true :: counter) unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem restore_done (b coin : Bool) (counter unread : List Bool) :
    machine.step (cfg (some (restoreState b)) [] counter unread) coin =
      cfg (some 1) [] (if b then true :: counter else counter) unread := by
  unfold machine
  erw [step_compile]
  cases b <;> change KS.W01.FixedStack.Config.mk _ _ = KS.W01.FixedStack.Config.mk _ _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

end KS.W03.BinaryToUnary

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryToUnaryRun
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.BinaryMultiply.shift_value _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W08.denseMatrixBinaryCursor_value _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedLoop.loop_toMachine _root_.OAI.KS.W29.FixedSequential.compose_toMachine _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine _root_.OAI.KS.W29.FixedSequential.ofMachine_toMachine _root_.OAI.KS.W29.FixedSequential.toMachine_ofMachine _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_quotient _root_.OAI.KS.W30.BinaryRational.divisionLoop_trim_remainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W03.BinaryToUnary
open KS.W01.FixedStack KS.W03.UnaryArithmetic KS.W19

theorem run_budget_append (a b c : Config 3 8) (t u : ℕ)
    (hab : ∀ coins, coins.length = t → machine.run a coins = b)
    (hbc : ∀ coins, coins.length = u → machine.run b coins = c)
    (coins : List Bool) (hlen : coins.length = t + u) : machine.run a coins = c := by
  have ht : (coins.take t).length = t := by simp only [List.length_take, hlen]; omega
  have hu : (coins.drop t).length = u := by simp only [List.length_drop, hlen]; omega
  conv_lhs => rw [← List.take_append_drop t coins]
  erw [Machine.run_append, hab _ ht, hbc _ hu]

theorem run_reverse (xs ys zs coins : List Bool) (hlen : coins.length = xs.length) :
    machine.run (cfg (some 0) xs ys zs) coins =
      cfg (some 0) [] ys (xs.reverse ++ zs) := by
  induction xs generalizing zs coins with
  | nil =>
    have hc : coins = [] := List.length_eq_zero_iff.mp hlen
    subst coins
    rfl
  | cons b bs ih =>
    cases coins with
    | nil => simp at hlen
    | cons c cs =>
      erw [Machine.run.eq_2, reverse_step, ih _ _ (by simpa using hlen)]
      simp [List.reverse_cons, List.append_assoc]
      rfl

theorem run_double (b : Bool) (n k : ℕ) (unread coins : List Bool)
    (hlen : coins.length = 2 * n) :
    machine.run (cfg (some (doubleState b)) (List.replicate k true)
      (List.replicate n true) unread) coins =
      cfg (some (doubleState b)) (List.replicate (2 * n + k) true) [] unread := by
  induction n generalizing k coins with
  | zero =>
    have hc : coins = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst coins
    simp [Machine.run]
    rfl
  | succ n ih =>
    cases coins with
    | nil => simp at hlen
    | cons c cs =>
      cases cs with
      | nil => simp at hlen; omega
      | cons d ds =>
        erw [List.replicate_succ, Machine.run.eq_2, double_step, Machine.run.eq_2, second_step]
        change machine.run (cfg (some (doubleState b)) (List.replicate (k + 2) true)
          (List.replicate n true) unread) ds = _
        rw [ih (k + 2) ds (by simp only [List.length_cons] at hlen; omega)]
        congr 2
        omega

theorem run_restore (b : Bool) (n k : ℕ) (unread coins : List Bool)
    (hlen : coins.length = n) :
    machine.run (cfg (some (restoreState b)) (List.replicate n true)
      (List.replicate k true) unread) coins =
      cfg (some (restoreState b)) [] (List.replicate (n + k) true) unread := by
  induction n generalizing k coins with
  | zero =>
    have hc : coins = [] := List.length_eq_zero_iff.mp hlen
    subst coins
    simp [Machine.run]
    rfl
  | succ n ih =>
    cases coins with
    | nil => simp at hlen
    | cons c cs =>
      erw [List.replicate_succ, Machine.run.eq_2, restore_step]
      change machine.run (cfg (some (restoreState b)) (List.replicate n true)
        (List.replicate (k + 1) true) unread) cs = _
      rw [ih (k + 1) cs (by simpa using hlen)]
      congr 2
      omega

theorem run_round (b : Bool) (n : ℕ) (unread coins : List Bool)
    (hlen : coins.length = 4 * n + 2) :
    machine.run (cfg (some (doubleState b)) [] (List.replicate n true) unread) coins =
      cfg (some 1) [] (List.replicate (2 * n + digit b) true) unread := by
  apply run_budget_append _
    (cfg (some (doubleState b)) (List.replicate (2 * n) true) [] unread) _
    (2 * n) (2 * n + 2) ?_ ?_ coins (by omega)
  · intro cs hcs
    simpa using run_double b n 0 unread cs hcs
  · intro cs hcs
    cases cs with
    | nil => simp at hcs
    | cons c rest =>
      erw [Machine.run.eq_2, double_done]
      apply run_budget_append _
        (cfg (some (restoreState b)) [] (List.replicate (2 * n) true) unread) _
        (2 * n) 1 ?_ ?_ rest (by
        simp only [List.length_cons] at hcs; omega)
      · intro ds hds
        simpa using run_restore b (2 * n) 0 unread ds hds
      · intro ds hds
        cases ds with
        | nil => simp at hds
        | cons d tail =>
          have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hds)
          subst tail
          erw [Machine.run.eq_2, restore_done]
          cases b <;> simp [Machine.run, digit, List.replicate_succ] <;> rfl

theorem run_loop (xs : List Bool) (n : ℕ) (coins : List Bool)
    (hlen : coins.length = ticks xs n) :
    machine.run (cfg (some 1) [] (List.replicate n true) xs) coins =
      cfg none [] (List.replicate (accumulate xs n) true) [] := by
  induction xs generalizing n coins with
  | nil =>
    cases coins with
    | nil => simp [ticks] at hlen
    | cons c cs =>
      have ht : cs = [] := List.length_eq_zero_iff.mp (by simpa [ticks] using hlen)
      subst cs
      erw [Machine.run.eq_2, guard_done]
      rfl
  | cons b bs ih =>
    cases coins with
    | nil => simp [ticks] at hlen; omega
    | cons c cs =>
      erw [Machine.run.eq_2, guard_step]
      apply run_budget_append _
        (cfg (some 1) [] (List.replicate (2 * n + digit b) true) bs) _
        (4 * n + 2) (ticks bs (2 * n + digit b))
        (run_round b n bs) (ih (2 * n + digit b)) cs
      simp only [List.length_cons, ticks] at hlen
      omega

theorem run_input_exact (xs coins : List Bool) (hlen : coins.length = totalTicks xs) :
    machine.run (machine.init xs) coins =
      cfg none [] (List.replicate (bitsValue xs) true) [] := by
  rw [init_eq]
  apply run_budget_append _ (cfg (some 0) [] [] xs.reverse) _
    xs.length (1 + ticks xs.reverse 0) ?_ ?_ coins (by
    unfold totalTicks at hlen; omega)
  · intro cs hcs
    simpa using run_reverse xs [] [] cs hcs
  · intro cs hcs
    cases cs with
    | nil => simp at hcs; omega
    | cons c rest =>
      erw [Machine.run.eq_2, reverse_done]
      have hr := run_loop xs.reverse 0 rest (by simp only [List.length_cons] at hcs; omega)
      simpa only [accumulate_reverse, List.replicate_zero] using hr

end KS.W03.BinaryToUnary

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryToUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W03.BinaryToUnary
open KS.W01.FixedStack KS.W03.UnaryArithmetic KS.W19

theorem run_input (xs coins : List Bool) (hlen : totalTicks xs ≤ coins.length) :
    machine.run (machine.init xs) coins =
      cfg none [] (List.replicate (bitsValue xs) true) [] := by
  have ht : (coins.take (totalTicks xs)).length = totalTicks xs := by
    simp only [List.length_take, Nat.min_eq_left hlen]
  conv_lhs => rw [← List.take_append_drop (totalTicks xs) coins]
  rw [Machine.run_append, run_input_exact xs _ ht]
  exact Machine.run_halted machine (cfg none [] (List.replicate (bitsValue xs) true) []) rfl
    (coins.drop (totalTicks xs))

theorem run_input_linear (xs coins : List Bool)
    (hlen : 4 * bitsValue xs + 4 * xs.length + 2 ≤ coins.length) :
    machine.run (machine.init xs) coins =
      cfg none [] (List.replicate (bitsValue xs) true) [] :=
  run_input xs coins ((totalTicks_le_linear xs).trans hlen)

end KS.W03.BinaryToUnary

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DenseMatrixSerialization
attribute [-simp] _root_.OAI.KS.W08.AccessCounted.readMatrix_ops _root_.OAI.KS.W08.AccessCounted.readMatrix_value _root_.OAI.KS.W08.AccessCounted.readMatrix_work _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open KS.W07
open scoped BigOperators

def denseMatrixPayloads {n : ℕ} (M : DenseRatMatrix n) : List (List Bool) :=
  List.ofFn (fun k : Fin (n * n) =>
    KS.W01.encodeRat (DenseRatMatrix.decode M (finProdFinEquiv.symm k).1
      (finProdFinEquiv.symm k).2))

@[simp] theorem denseMatrixPayloads_length {n : ℕ} (M : DenseRatMatrix n) :
    (denseMatrixPayloads M).length = n * n := by simp [denseMatrixPayloads]

theorem denseMatrixPayloads_get {n : ℕ} (M : DenseRatMatrix n) (i j : Fin n) :
    (denseMatrixPayloads M)[i.val * n + j.val]'(by
      rw [denseMatrixPayloads_length]
      exact matrixEntryIndex_lt i j) = KS.W01.encodeRat (DenseRatMatrix.decode M i j) := by
  have h : (denseMatrixPayloads M)[(matrixEntryIndex i j).val]'(by
      rw [denseMatrixPayloads_length]
      exact (matrixEntryIndex i j).isLt) =
      KS.W01.encodeRat (DenseRatMatrix.decode M i j) := by
    unfold denseMatrixPayloads
    rw [List.getElem_ofFn]
    change KS.W01.encodeRat (DenseRatMatrix.decode M
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = _
    simp only [Equiv.symm_apply_apply]
  simpa only [matrixEntryIndex_val] using h

def denseMatrixTape {n : ℕ} (M : DenseRatMatrix n) : List Bool :=
  (denseMatrixPayloads M).flatMap KS.W01.frame

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FrameDecoder
attribute [-simp] _root_.OAI.KS.W01.FixedStack.lift3_project_init _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.BinaryMachine.withEntry_init_stacks _root_.OAI.KS.W29.BinaryMachine.withEntry_init_state _root_.OAI.KS.W29.BinaryMachine.withEntry_initial _root_.OAI.KS.W29.BinaryMachine.withEntry_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29
namespace FrameDecoder

theorem run_frame_of_length_ge (payload tail bits : List Bool)
    (h : 3 * payload.length + 2 ≤ bits.length) :
    machine.run (machine.init (W01.frame payload ++ tail)) bits =
      config none tail payload [] := by
  have htake : (bits.take (3 * payload.length + 2)).length = 3 * payload.length + 2 := by
    simp [List.length_take, Nat.min_eq_left h]
  have hr := run_frame payload tail (bits.take (3 * payload.length + 2)) htake
  conv_lhs => rw [← List.take_append_drop (3 * payload.length + 2) bits]
  erw [machine.run_append, hr]
  exact machine.run_halted _ rfl _

end FrameDecoder
end KS.W29

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArraySkip
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArray
open KS.W01.FixedStack
open KS.W29 (StackAction)
open KS.W29.FixedSequential

def config {q : ℕ} (state : Option (Fin q)) (input output scratch index : List Bool) :
    Config 4 q := ⟨state, «stacks» input output scratch index⟩

theorem config_ext {q : ℕ} {c d : Config 4 q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

def skipDispatch (s : Fin 2) (heads : Fin 4 → Fin 3) (_coin : Bool) : Instruction 4 2 :=
  if (heads 0).val = 0 then Instruction.halt 4 2 else
    ⟨if s = 0 then (if (heads 0).val = 2 then none else some 1) else some 0,
      Vector.ofFn (fun j => if j = 0 then .pop else .stay)⟩

def skipMachine : Machine := compile 0 0 1 skipDispatch
def skipProgram : Program 4 := ofMachine skipMachine

@[simp] theorem skipProgram_toMachine : skipProgram.toMachine = skipMachine :=
  toMachine_ofMachine skipMachine

theorem roundtrip_step (M : Machine) (c : Config M.stackCount M.states) (coin : Bool) :
    (ofMachine M).toMachine.step c coin = M.step c coin := by
  cases M
  rfl

theorem roundtrip_run (M : Machine) (c : Config M.stackCount M.states) (bits : List Bool) :
    (ofMachine M).toMachine.run c bits = M.run c bits := by
  cases M
  rfl

theorem skipProgram_step (c : Config 4 2) (coin : Bool) :
    skipProgram.toMachine.step c coin = skipMachine.step c coin :=
  roundtrip_step skipMachine c coin

theorem skipProgram_run (c : Config 4 2) (bits : List Bool) :
    skipProgram.toMachine.run c bits = skipMachine.run c bits :=
  roundtrip_run skipMachine c bits

theorem skip_tag_false (xs out tmp ix : List Bool) (coin : Bool) :
    skipMachine.step (config (some (0 : Fin 2)) (false :: xs) out tmp ix) coin =
      config (some (1 : Fin 2)) xs out tmp ix := by
  unfold skipMachine config
  erw [step_compile]
  apply config_ext
  · simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode]
  · intro j
    fin_cases j <;> simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode,
      Instruction.action, StackAction.apply]

theorem skip_tag_true (xs out tmp ix : List Bool) (coin : Bool) :
    skipMachine.step (config (some (0 : Fin 2)) (true :: xs) out tmp ix) coin =
      config none xs out tmp ix := by
  unfold skipMachine config
  erw [step_compile]
  apply config_ext
  · simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode]
    rfl
  · intro j
    fin_cases j <;> simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode,
      Instruction.action, StackAction.apply]

theorem skip_data (bit : Bool) (xs out tmp ix : List Bool) (coin : Bool) :
    skipMachine.step (config (some (1 : Fin 2)) (bit :: xs) out tmp ix) coin =
      config (some (0 : Fin 2)) xs out tmp ix := by
  unfold skipMachine config
  erw [step_compile]
  cases bit <;> apply config_ext
  all_goals
    first | (solve | simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode]) |
      (intro j; fin_cases j <;> simp [skipDispatch, observedHeads, «stacks», KS.W29.topCode,
        Instruction.action, StackAction.apply])

theorem skip_frame (payload tail out tmp ix bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    skipMachine.run (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) out tmp ix) bits =
      config none tail out tmp ix ∧
    ActiveFor skipProgram (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) out tmp ix) bits := by
  induction payload generalizing bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons, List.length_nil] at hlen
            omega
          subst rest
          constructor
          · simpa [KS.W01.frame, Machine.run] using skip_tag_true tail out tmp ix coin
          · exact ⟨Option.some_ne_none _, trivial⟩
  | cons bit payload ih =>
      cases bits with
      | nil => simp at hlen
      | cons c₀ rest =>
          cases rest with
          | nil => simp at hlen
          | cons c₁ rest =>
              have hr : rest.length = 2 * payload.length + 1 := by
                simp only [List.length_cons] at hlen
                omega
              obtain ⟨he, ha⟩ := ih rest hr
              constructor
              · simp only [KS.W01.frame, List.cons_append, Machine.run]
                erw [skip_tag_false, skip_data]
                exact he
              · erw [ActiveFor.eq_2]
                refine ⟨Option.some_ne_none _, ?_⟩
                erw [skipProgram_step]
                simp only [KS.W01.frame, List.cons_append]
                erw [skip_tag_false]
                erw [ActiveFor.eq_2]
                refine ⟨Option.some_ne_none _, ?_⟩
                erw [skipProgram_step]
                erw [skip_data]
                exact ha

theorem skip_frame_haltsAfter (payload tail out tmp ix bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    HaltsAfter skipProgram (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) out tmp ix) bits := by
  have h := skip_frame payload tail out tmp ix bits hlen
  refine ⟨h.2, ?_⟩
  erw [skipProgram_run]
  exact congrArg (fun c : Config 4 2 => c.state) h.1

def indexGuard (heads : Fin 4 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 4 :=
  if (heads 3).val = 0 then ⟨.halt, Vector.replicate 4 .stay⟩
  else ⟨.call, Vector.ofFn (fun j => if j = 3 then .pop else .stay)⟩

def scanProgram : Program 4 := KS.W29.FixedLoop.loop skipProgram indexGuard

theorem scan_guard_nil (input out tmp : List Bool) (coin : Bool) :
    scanProgram.toMachine.step (config (some scanProgram.initial) input out tmp []) coin =
      config none input out tmp [] := by
  change (KS.W29.FixedLoop.loop skipProgram indexGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState skipProgram), «stacks» input out tmp []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, config]
    rfl
  · intro j
    fin_cases j <;> simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, Instruction.action, StackAction.apply, config]

theorem scan_guard_cons (input out tmp ix : List Bool) (coin : Bool) :
    scanProgram.toMachine.step
      (config (some scanProgram.initial) input out tmp (true :: ix)) coin =
      KS.W29.FixedLoop.liftBody skipProgram (config (some (0 : Fin 2)) input out tmp ix) := by
  change (KS.W29.FixedLoop.loop skipProgram indexGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState skipProgram), «stacks» input out tmp (true :: ix)⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody, config]; rfl
  · intro j
    fin_cases j <;> simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody,
      Instruction.action, StackAction.apply, config]

def scanFuel («prefix» : List (List Bool)) : ℕ :=
  («prefix».flatMap KS.W01.frame).length + «prefix».length + 1

theorem scanFuel_cons (p : List Bool) (ps : List (List Bool)) :
    scanFuel (p :: ps) = 1 + (2 * p.length + 1) + scanFuel ps := by
  simp only [scanFuel, List.flatMap_cons, List.length_append, KS.W01.length_frame,
    List.length_cons]
  omega

theorem scan_prefix («prefix» : List (List Bool)) (tail out tmp bits : List Bool)
    (hlen : bits.length = scanFuel «prefix») :
    scanProgram.toMachine.run
      (config (some scanProgram.initial) («prefix».flatMap KS.W01.frame ++ tail)
        out tmp (List.replicate «prefix».length true)) bits =
      config none tail out tmp [] := by
  induction «prefix» generalizing bits with
  | nil =>
      cases bits with
      | nil => simp [scanFuel] at hlen
      | cons coin rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [scanFuel, List.flatMap_nil, List.length_nil, List.length_cons] at hlen
            omega
          subst rest
          simpa [Machine.run] using scan_guard_nil tail out tmp coin
  | cons p ps ih =>
      cases bits with
      | nil => simp [scanFuel] at hlen
      | cons coin rest =>
          have hr : rest.length = (2 * p.length + 1) + scanFuel ps := by
            rw [scanFuel_cons] at hlen
            simp only [List.length_cons] at hlen
            omega
          have ht : (rest.take (2 * p.length + 1)).length = 2 * p.length + 1 := by
            simp only [List.length_take, hr]
            omega
          have hd : (rest.drop (2 * p.length + 1)).length = scanFuel ps := by
            simp only [List.length_drop, hr]
            omega
          simp only [List.flatMap_cons, List.append_assoc, List.length_cons,
            List.replicate_succ, Machine.run]
          rw [scan_guard_cons]
          conv_lhs => rw [← List.take_append_drop (2 * p.length + 1) rest]
          erw [KS.W29.FixedLoop.run_body_then skipProgram indexGuard _ _ _
            (skip_frame_haltsAfter p (ps.flatMap KS.W01.frame ++ tail) out tmp
              (List.replicate ps.length true) _ ht)]
          erw [skipProgram_run]
          erw [(skip_frame p (ps.flatMap KS.W01.frame ++ tail) out tmp
            (List.replicate ps.length true) _ ht).1]
          exact ih _ hd

end KS.W11.FramedArray

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayRetrieval
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArray
open KS.W01.FixedStack
open KS.W29.FixedSequential

def decoderProgram : Program 4 := ofMachine (lift3 KS.W29.FrameDecoder.machine decoderPorts)

theorem run_decoder (payload tail ix bits : List Bool)
    (hlen : 3 * payload.length + 2 ≤ bits.length) :
    decoderProgram.toMachine.run
      (config (some decoderProgram.initial) (KS.W01.frame payload ++ tail) [] [] ix) bits =
      config none tail payload [] ix := by
  have hr (a b c : List Bool) :
      KS.W28.FixedPositiveSerializer.registers decoderPorts (fun _ => ix) a b c =
        «stacks» a b c ix := by
    funext j
    fin_cases j <;> simp [KS.W28.FixedPositiveSerializer.registers, decoderPorts, «stacks»]
  have h := KS.W11.FrameWireCodec.unframe_spec decoderPorts (fun _ => ix) payload tail
  rw [hr, hr] at h
  exact h.run_of_le bits hlen

def lookupProgram : Program 4 := compose scanProgram decoderProgram

def lookupFuel («prefix» : List (List Bool)) (payload : List Bool) : ℕ :=
  scanFuel «prefix» + 3 * payload.length + 2

theorem run_lookup_prefix («prefix» : List (List Bool)) (payload tail bits : List Bool)
    (hlen : lookupFuel «prefix» payload ≤ bits.length) :
    lookupProgram.toMachine.run
      (config (some lookupProgram.initial)
        («prefix».flatMap KS.W01.frame ++ KS.W01.frame payload ++ tail)
        [] [] (List.replicate «prefix».length true)) bits =
      config none tail payload [] [] := by
  have hs : KS.W03.MachineCombinators.RunSpec scanProgram
      («stacks» («prefix».flatMap KS.W01.frame ++ KS.W01.frame payload ++ tail)
        [] [] (List.replicate «prefix».length true))
      («stacks» (KS.W01.frame payload ++ tail) [] [] []) (scanFuel «prefix») := by
    intro coins hc
    have h := scan_prefix «prefix» (KS.W01.frame payload ++ tail) [] [] coins hc
    simp only [List.append_assoc] at h ⊢
    exact h
  have hd : KS.W03.MachineCombinators.RunSpec decoderProgram
      («stacks» (KS.W01.frame payload ++ tail) [] [] []) («stacks» tail payload [] [])
      (3*payload.length+2) := by
    intro coins hc
    exact run_decoder payload tail [] coins hc.ge
  have h := hs.compose hd
  exact h.run_of_le bits (by unfold lookupFuel at hlen;omega)

theorem lookupFuel_linear («prefix» : List (List Bool)) (payload tail : List Bool) :
    lookupFuel «prefix» payload ≤
      2 * («prefix».flatMap KS.W01.frame ++ KS.W01.frame payload ++ tail).length +
        «prefix».length + 1 := by
  simp only [lookupFuel, scanFuel, List.length_append, KS.W01.length_frame]
  omega

theorem run_lookup (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length)
    (tail bits : List Bool)
    (hlen : 2 * (xs.flatMap KS.W01.frame ++ tail).length + i + 1 ≤ bits.length) :
    lookupProgram.toMachine.run
      (config (some lookupProgram.initial) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true)) bits =
      config none ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) xs[i] [] [] := by
  have hx : xs = xs.take i ++ xs[i] :: xs.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have ht : (xs.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hflat : xs.flatMap KS.W01.frame ++ tail =
      (xs.take i).flatMap KS.W01.frame ++ KS.W01.frame xs[i] ++
        ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) := by
    conv_lhs => rw [hx]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hb := lookupFuel_linear (xs.take i) xs[i]
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail)
  rw [← hflat, ht] at hb
  have h := run_lookup_prefix (xs.take i) xs[i]
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) bits (hb.trans hlen)
  simpa only [← hflat, ht] using h

end KS.W11.FramedArray

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArray
open KS.W01.FixedStack
open KS.W29.FixedSequential

def liftedLookup {k : ℕ} (ports : Fin 4 ↪ Fin k) : Program k :=
  KS.W29.FixedSequential.liftPorts lookupProgram ports

theorem run_lookup_ports {k : ℕ} (ports : Fin 4 ↪ Fin k)
    (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length) (tail bits : List Bool)
    (c : Config k lookupProgram.states)
    (hc : projectPorts ports c =
      config (some lookupProgram.initial) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true))
    (hlen : 2 * (xs.flatMap KS.W01.frame ++ tail).length + i + 1 ≤ bits.length) :
    let result := (liftedLookup ports).toMachine.run c bits
    result.state = none ∧
      result.«stacks» (ports 0) = (xs.drop (i + 1)).flatMap KS.W01.frame ++ tail ∧
      result.«stacks» (ports 1) = xs[i] ∧
      result.«stacks» (ports 2) = [] ∧
      result.«stacks» (ports 3) = [] ∧
      ∀ j, (∀ r, j ≠ ports r) → result.«stacks» j = c.«stacks» j := by
  have hp := KS.W01.FixedStack.liftPorts_project_run lookupProgram.toMachine ports c bits
  erw [hc, run_lookup xs i hi tail bits hlen] at hp
  refine ⟨congrArg (fun d : Config 4 lookupProgram.states => d.state) hp,
    congrArg (fun d : Config 4 lookupProgram.states => d.«stacks» 0) hp,
    congrArg (fun d : Config 4 lookupProgram.states => d.«stacks» 1) hp,
    congrArg (fun d : Config 4 lookupProgram.states => d.«stacks» 2) hp,
    congrArg (fun d : Config 4 lookupProgram.states => d.«stacks» 3) hp, ?_⟩
  intro j hj
  exact KS.W01.FixedStack.liftPorts_run_preserves_other lookupProgram.toMachine ports c bits j hj

end KS.W11.FramedArray

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryStackMoves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W04.BinaryStackMoves
open KS.W01.FixedStack
open KS.W29 (StackAction)
open KS.W29.FixedSequential (Program ActiveFor HaltsAfter HaltsFromWithin)

variable {k : Nat}

theorem clear_active (port : Fin k) (xs : List Bool) (rest : Fin k → List Bool)
    (bits : List Bool) (hlen : bits.length ≤ xs.length + 1) :
    ActiveFor (clearProgram port) (oneConfig port (some (0 : Fin 1)) xs rest) bits := by
  induction bits generalizing xs with
  | nil => trivial
  | cons coin tail ih =>
      constructor
      · exact Option.some_ne_none _
      · cases xs with
        | nil =>
            have ht : tail = [] := by
              apply List.length_eq_zero_iff.mp
              simp only [List.length_cons, List.length_nil] at hlen
              omega
            subst tail
            trivial
        | cons b xs =>
            change ActiveFor (clearProgram port)
              ((clearMachine port).step (oneConfig port (some (0 : Fin 1)) (b :: xs) rest) coin) tail
            rw [clear_step_cons]
            exact ih xs (by simp only [List.length_cons] at hlen; omega)

theorem clear_haltsAfter (port : Fin k) (xs : List Bool) (rest : Fin k → List Bool)
    (bits : List Bool) (hlen : bits.length = xs.length + 1) :
    HaltsAfter (clearProgram port) (oneConfig port (some (0 : Fin 1)) xs rest) bits := by
  refine ⟨clear_active port xs rest bits hlen.le, ?_⟩
  change ((clearMachine port).run _ bits).state = none
  exact congrArg Config.state (run_clear port xs rest bits hlen)

theorem move_active (source target : Fin k) (hst : source ≠ target)
    (xs ys : List Bool) (rest : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length ≤ xs.length + 1) :
    ActiveFor (moveProgram source target) (twoConfig source target (some (0 : Fin 1)) xs ys rest) bits := by
  induction bits generalizing xs ys with
  | nil => trivial
  | cons coin tail ih =>
      constructor
      · exact Option.some_ne_none _
      · cases xs with
        | nil =>
            have ht : tail = [] := by
              apply List.length_eq_zero_iff.mp
              simp only [List.length_cons, List.length_nil] at hlen
              omega
            subst tail
            trivial
        | cons b xs =>
            change ActiveFor (moveProgram source target)
              ((moveMachine source target).step
                (twoConfig source target (some (0 : Fin 1)) (b :: xs) ys rest) coin) tail
            rw [move_step_cons source target hst]
            exact ih xs (b :: ys) (by simp only [List.length_cons] at hlen; omega)

theorem move_haltsAfter (source target : Fin k) (hst : source ≠ target)
    (xs ys : List Bool) (rest : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = xs.length + 1) :
    HaltsAfter (moveProgram source target) (twoConfig source target (some (0 : Fin 1)) xs ys rest) bits := by
  refine ⟨move_active source target hst xs ys rest bits hlen.le, ?_⟩
  change ((moveMachine source target).run _ bits).state = none
  exact congrArg Config.state (run_move source target hst xs ys rest bits hlen)

theorem clear_haltsAfter_stacks (port : Fin k) («stacks» : Fin k → List Bool)
    (bits : List Bool) (hlen : bits.length = («stacks» port).length + 1) :
    HaltsAfter (clearProgram port) ⟨some (0 : Fin 1), «stacks»⟩ bits := by
  have h := clear_haltsAfter port («stacks» port) «stacks» bits hlen
  rw [oneConfig_original] at h
  exact h

theorem move_haltsAfter_stacks (source target : Fin k) (hst : source ≠ target)
    («stacks» : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = («stacks» source).length + 1) :
    HaltsAfter (moveProgram source target) ⟨some (0 : Fin 1), «stacks»⟩ bits := by
  have h := move_haltsAfter source target hst («stacks» source) («stacks» target) «stacks» bits hlen
  rw [twoConfig_original] at h
  exact h

end KS.W04.BinaryStackMoves

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FixedSubroutineBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W29.FixedSequential

theorem lift3_run_state {k : Nat} (M : KS.W29.BinaryMachine) (ports : Fin 3 ↪ Fin k)
    (c : KS.W01.FixedStack.Config k M.states) (bits : List Bool) :
    ((KS.W01.FixedStack.lift3 M ports).run c bits).state =
      (M.run (KS.W01.FixedStack.project ports c) bits).state :=
  congrArg (fun d : KS.W29.Config M.states => d.state)
    (KS.W01.FixedStack.lift3_project_run M ports c bits)

end KS.W29.FixedSequential

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ReusableArrayLookup
attribute [-simp] _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W04.ReusableArrayLookup
open KS.W01.FixedStack
open KS.W29.FixedSequential
open KS.W03.MachineCombinators

def reoutput {k : Nat} (P : Program k) (output : Fin k) : Program k :=
  { P with output := output }

theorem step_reoutput {k : Nat} (P : Program k) (output : Fin k)
    (c : Config k P.states) (coin : Bool) :
    (reoutput P output).toMachine.step c coin = P.toMachine.step c coin := by
  cases c with
  | mk state bank => cases state <;> rfl

theorem run_reoutput {k : Nat} (P : Program k) (output : Fin k)
    (c : Config k P.states) (bits : List Bool) :
    (reoutput P output).toMachine.run c bits = P.toMachine.run c bits := by
  induction bits generalizing c with
  | nil => rfl
  | cons coin bits ih =>
      erw [Machine.run.eq_2, step_reoutput]
      exact ih _

theorem run_compose_bounded {k : Nat} (P Q : Program k)
    (initial middle final : Fin k → List Bool) (t₁ t₂ : Nat)
    (hP : ∀ bits : List Bool, t₁ ≤ bits.length →
      P.toMachine.run ⟨some P.initial, initial⟩ bits = ⟨none, middle⟩)
    (hQ : ∀ bits : List Bool, t₂ ≤ bits.length →
      Q.toMachine.run ⟨some Q.initial, middle⟩ bits = ⟨none, final⟩)
    (bits : List Bool) (hlen : t₁ + t₂ ≤ bits.length) :
    (compose P Q).toMachine.run ⟨some (compose P Q).initial, initial⟩ bits =
      ⟨none, final⟩ := by
  have hp : RunSpec P initial middle t₁ := fun b hb => hP b hb.ge
  have hq : RunSpec Q middle final t₂ := fun b hb => hQ b hb.ge
  exact (hp.compose hq).run_of_le bits hlen

theorem config_ext {k q : Nat} {c d : Config k q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

def copyPorts : Fin 3 ↪ Fin 5 where
  toFun j := if j = 0 then 0 else if j = 1 then 1 else 3
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def copyProgram : Program 5 := KS.W01.FixedCopy.program copyPorts
def lookupProgram : Program 5 := KS.W11.FramedArray.liftedLookup lookupPorts
def cleanupProgram : Program 5 := reoutput (BinaryStackMoves.clearProgram 1) 2
def lookupAndCleanup : Program 5 := compose lookupProgram cleanupProgram

def program : Program 5 := compose copyProgram lookupAndCleanup

@[simp] theorem program_input : program.input = 0 := rfl
@[simp] theorem program_output : program.output = 2 := rfl

theorem run_lookup (xs : List (List Bool)) (i : Nat) (hi : i < xs.length)
    (tail bits : List Bool)
    (hlen : 2 * (xs.flatMap KS.W01.frame ++ tail).length + i + 1 ≤ bits.length) :
    lookupProgram.toMachine.run
      ⟨some lookupProgram.initial,
        arrayStacks (xs.flatMap KS.W01.frame ++ tail) (xs.flatMap KS.W01.frame ++ tail)
          [] [] (List.replicate i true)⟩ bits =
      ⟨none, arrayStacks (xs.flatMap KS.W01.frame ++ tail)
        ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) xs[i] [] []⟩ := by
  let c : Config 5 KS.W11.FramedArray.lookupProgram.states :=
    ⟨some lookupProgram.initial,
      arrayStacks (xs.flatMap KS.W01.frame ++ tail) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true)⟩
  have hc : projectPorts lookupPorts c = KS.W11.FramedArray.config
      (some KS.W11.FramedArray.lookupProgram.initial) (xs.flatMap KS.W01.frame ++ tail)
        [] [] (List.replicate i true) := by
    refine config_ext ?_ ?_
    · rfl
    intro j
    fin_cases j <;> rfl
  have h := KS.W11.FramedArray.run_lookup_ports lookupPorts xs i hi tail bits c hc hlen
  refine config_ext h.1 ?_
  intro j
  fin_cases j
  · have ho := h.2.2.2.2.2 (0 : Fin 5) (by intro r; fin_cases r <;> decide)
    exact ho
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1

theorem suffix_length_le (xs : List (List Bool)) (i : Nat) (tail : List Bool) :
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail).length ≤
      (xs.flatMap KS.W01.frame ++ tail).length := by
  have he := congrArg (fun ys : List (List Bool) => (ys.flatMap KS.W01.frame ++ tail).length)
    (List.take_append_drop (i + 1) xs)
  simp only [List.flatMap_append, List.length_append] at he ⊢
  omega

end KS.W04.ReusableArrayLookup

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BinaryAddressLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup

def matrixCursorPorts : Fin 3 ↪ Fin 5 where
  toFun i := if i = 0 then 1 else if i = 1 then 4 else 3
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def matrixCursorProgram : Program 5 :=
  ofMachine (KS.W01.FixedStack.liftPorts KS.W03.BinaryToUnary.machine matrixCursorPorts)

theorem ofMachine_lift_run_eq {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (before after : Fin K → List Bool) (bits : List Bool)
    (h : M.run (projectPorts ports ⟨some M.initial,before⟩) bits=⟨none,fun i=>after (ports i)⟩)
    (hother : ∀ j,(∀ i,j≠ports i)→after j=before j) :
    (ofMachine (KS.W01.FixedStack.liftPorts M ports)).toMachine.run
      ⟨some (ofMachine (KS.W01.FixedStack.liftPorts M ports)).initial,before⟩ bits=⟨none,after⟩ := by
  change (KS.W01.FixedStack.liftPorts M ports).run ⟨some M.initial,before⟩ bits=⟨none,after⟩
  exact KS.W01.FixedStack.liftPorts_run_eq M ports _ bits after h hother

def binaryMatrixLookupProgram : Program 5 :=
  compose matrixCursorProgram KS.W04.ReusableArrayLookup.program

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_BorrowSubtractor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.BorrowSubtractor
open KS.W29
open KS.W19 (bitsValue digit differenceDigit nextBorrow subtractBits)

def cfg (state : Option (Fin 2)) (xs ys zs : List Bool) : Config 2 :=
  ⟨state, fun j => if j = 0 then xs else if j = 1 then ys else zs⟩

end KS.W19.BorrowSubtractor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_MachineTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.MachineTransport
open KS.W01.FixedStack KS.W29.FixedSequential

theorem run_ofMachine (M : Machine) (c : Config M.stackCount M.states) (bits : List Bool) :
    (ofMachine M).toMachine.run c bits=M.run c bits := by
  cases M
  rfl

end KS.W19.MachineTransport

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

theorem clearRemainder_run (d pending q r candidate coins : List Bool)
    (hc : coins.length = r.length + 1) :
    (KS.W04.BinaryStackMoves.clearProgram (4 : Fin 10)).toMachine.run
      ⟨some (0 : Fin 1), «stacks» d pending q r [] [] candidate []⟩ coins =
      ⟨none, «stacks» d pending q [] [] [] candidate []⟩ := by
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (4 : Fin 10)
    («stacks» d pending q r [] [] candidate []) coins hc
  refine (KS.W19.MachineTransport.run_ofMachine (KS.W04.BinaryStackMoves.clearMachine (4 : Fin 10)) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

end KS.W19.DivisionMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_DivisionInput
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.DivisionInput
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun

def parseFirst : Program 10 := ofMachine (lift3 KS.W29.FrameDecoder.machine firstPorts)
def parseSecond : Program 10 := ofMachine (lift3 KS.W29.FrameDecoder.machine secondPorts)
def reverseInput : Program 10 := KS.W04.BinaryStackMoves.moveProgram 1 3

theorem reverse_run (xs d coins : List Bool) (hc : coins.length = xs.length + 1) :
    reverseInput.toMachine.run ⟨some reverseInput.initial, «stacks» [] xs d []⟩ coins =
      ⟨none, DivisionMachine.«stacks» d xs.reverse [] [] [] [] [] []⟩ := by
  have h := KS.W04.BinaryStackMoves.run_move_stacks (1 : Fin 10) 3 (by decide)
    («stacks» [] xs d []) coins hc
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.moveMachine (1 : Fin 10) 3) _ coins).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [KS.W04.BinaryStackMoves.twoConfig, «stacks»,
      DivisionMachine.«stacks»]

theorem reverse_halts (xs d coins : List Bool) (hc : coins.length = xs.length + 1) :
    HaltsAfter reverseInput ⟨some reverseInput.initial, «stacks» [] xs d []⟩ coins :=
  KS.W04.BinaryStackMoves.move_haltsAfter_stacks (1 : Fin 10) 3 (by decide) _ coins hc

end KS.W19.DivisionInput

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SignedFloorModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SignedFloor

theorem signed_quotient (z : Int) (d : Nat) (hd : 0 < d) :
    signedBitsValue (negativeOfInt z)
      (DivisionLoop.process (Computability.encodeNat d)
        (Computability.encodeNat (KS.W01.intPayload z)).reverse [] []).1 = z / (d : Int) := by
  have hpos : 0 < bitsValue (Computability.encodeNat d) := by simpa only [bitsValue_encodeNat] using hd
  have hmatch : bitsValue (DivisionLoop.process (Computability.encodeNat d)
      (Computability.encodeNat (KS.W01.intPayload z)).reverse [] []).1 =
      bitsValue (divideBits (Computability.encodeNat d) (Computability.encodeNat (KS.W01.intPayload z))).1 := by
    rw [loop_quotient _ _ hpos, old_quotient _ _ hpos]
  have h := divideSignedBits_intPayload_quotient z d hd
  have he : (divideSignedBits (negativeOfInt z) (Computability.encodeNat d)
      (Computability.encodeNat (KS.W01.intPayload z))).1 =
      (divideBits (Computability.encodeNat d) (Computability.encodeNat (KS.W01.intPayload z))).1 := by
    cases negativeOfInt z <;> rfl
  rw [he] at h
  simpa only [signedBitsValue, hmatch] using h

theorem encodeInt_constructor (z : Int) :
    KS.W01.encodeInt z = negativeOfInt z :: KS.W01.encodeNat (KS.W01.intPayload z) := by
  cases z <;> rfl

theorem encodeInt_signedBits (sign : Bool) (payload : List Bool) :
    KS.W01.encodeInt (signedBitsValue sign payload) =
      sign :: KS.W01.encodeNat (bitsValue payload) := by
  cases sign <;> rfl

theorem encodeRat_constructor (q : Rat) :
    KS.W01.encodeRat q = negativeOfInt q.num ::
      (KS.W01.encodeNat (KS.W01.intPayload q.num) ++ KS.W01.encodeNat q.den) := by
  rw [KS.W01.encodeRat, encodeInt_constructor]
  rfl

theorem floor_wire (q : Rat) :
    negativeOfInt q.num :: KS.W01.encodeNat
      (bitsValue (DivisionLoop.process (Computability.encodeNat q.den)
        (Computability.encodeNat (KS.W01.intPayload q.num)).reverse [] []).1) =
      KS.W01.encodeInt ⌊q⌋ := by
  rw [← encodeInt_signedBits, signed_quotient q.num q.den q.den_pos, Rat.floor_def']

end KS.W19.SignedFloor

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_UnsignedPairSerializer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.UnsignedPairSerializer
open KS.W28
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def reverseProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.NormalizeOutput.machine ports)

end KS.W19.UnsignedPairSerializer

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedCanonicalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.FixedCanonicalize
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers )

def reverseProgram {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  KS.W04.BinaryStackMoves.moveProgram (ports 1) (ports 2)

end KS.W19.FixedCanonicalize

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_SignedQuotientSerializer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SignedQuotientSerializer
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers )

def wire (sign : Bool) (payload : List Bool) : List Bool := sign :: KS.W01.frame payload

def emitProgram {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 (KS.W28.PositiveWireSerializer.machine.withEntry (2 : Fin 5)) ports)
def reverseProgram {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W29.NormalizeOutput.machine ports)
def program {k : Nat} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (emitProgram ports) (reverseProgram ports)

end KS.W19.SignedQuotientSerializer

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SignedFloorMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.SignedFloorMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def stripDispatch (_state : Fin 1) (heads : Fin 11 → Fin 3) (_coin : Bool) : Instruction 11 1 :=
  if (heads 0).val = 0 then Instruction.halt 11 1
  else ⟨none, Vector.ofFn (fun j => if j = 0 then .pop
    else if j = 10 then .push ((heads 0).val == 2) else .stay)⟩

def strip : Program 11 := ofMachine (compile 0 0 0 stripDispatch)
def emit : Program 11 := SignedQuotientSerializer.program outputPorts

theorem fuel_quadratic (sign : Bool) (xs d : List Bool) :
    1 + (DivisionInput.inputFuel xs d + (6 * (EncodedDivision.resultPair xs d).1.length + 6)) ≤
      KS.W29.polynomialFuel 32 2 (sign :: (KS.W01.frame xs ++ KS.W01.frame d)).length := by
  have hq := DivisionLoop.process_quotient_length d xs.reverse [] []
  simp only [List.length_nil, List.length_reverse, Nat.zero_add] at hq
  change (EncodedDivision.resultPair xs d).1.length = xs.length at hq
  rw [hq]
  simp only [DivisionInput.inputFuel, KS.W29.polynomialFuel, List.length_cons, List.length_append, KS.W01.length_frame]
  nlinarith [Nat.zero_le (xs.length * d.length), Nat.zero_le (xs.length ^ 2), Nat.zero_le (d.length ^ 2)]

end KS.W19.SignedFloorMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SignedFloorInterface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SignedFloorMachine
open KS.W03.MachineCombinators

def rationalRemainder (q : Rat) : List Bool :=
  (EncodedDivision.resultPair (Computability.encodeNat (KS.W01.intPayload q.num))
    (Computability.encodeNat q.den)).2

end KS.W19.SignedFloorMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_FloorRationalMachine
attribute [-simp] _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W20.FloorRationalMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19

def clearDivisor : Program 11 := KS.W04.BinaryStackMoves.clearProgram 2
def clearRemainder : Program 11 := KS.W04.BinaryStackMoves.clearProgram 4

def clearScratch : Program 11 := compose clearDivisor clearRemainder

theorem clearScratch_spec (d q r : List Bool) :
    RunSpec clearScratch (SignedFloorMachine.«stacks» [] d q r []) (state [] q)
      (d.length + r.length + 2) := by
  have h₁ : RunSpec clearDivisor (SignedFloorMachine.«stacks» [] d q r [])
      (SignedFloorMachine.«stacks» [] [] q r []) (d.length + 1) := by
    convert KS.W15.RationalMultiply.clear_spec (2 : Fin 11)
      (SignedFloorMachine.«stacks» [] d q r []) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> rfl
  have h₂ : RunSpec clearRemainder (SignedFloorMachine.«stacks» [] [] q r [])
      (state [] q) (r.length + 1) := by
    convert KS.W15.RationalMultiply.clear_spec (4 : Fin 11)
      (SignedFloorMachine.«stacks» [] [] q r []) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> rfl
  convert h₁.compose h₂ using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  omega

def appendDenominator : Program 11 :=
  compose (KS.W04.BinaryStackMoves.moveProgram (5 : Fin 11) 0)
    (compose (Wire.writeBits (5 : Fin 11) (KS.W01.encodeNat 1))
      (KS.W04.BinaryStackMoves.moveProgram (0 : Fin 11) 5))

theorem appendDenominator_spec (wire : List Bool) :
    RunSpec appendDenominator (state [] wire) (state [] (wire ++ KS.W01.encodeNat 1))
      (2 * wire.length + 6) := by
  have h₁ : RunSpec (KS.W04.BinaryStackMoves.moveProgram (5 : Fin 11) 0)
      (state [] wire) (state wire.reverse []) (wire.length + 1) := by
    convert KS.W15.RationalMultiply.move_spec (5 : Fin 11) 0 (by decide) (state [] wire) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> simp [state, SignedFloorMachine.«stacks», KS.W15.RationalMultiply.moveAfter]
  have h₂ : RunSpec (Wire.writeBits (5 : Fin 11) (KS.W01.encodeNat 1))
      (state wire.reverse []) (state wire.reverse (KS.W01.encodeNat 1)) 4 := by
    convert Wire.writeBits_spec (5 : Fin 11) (KS.W01.encodeNat 1) (state wire.reverse []) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    · funext j
      fin_cases j <;> simp [state, SignedFloorMachine.«stacks», Function.update]
  have h₃ : RunSpec (KS.W04.BinaryStackMoves.moveProgram (0 : Fin 11) 5)
      (state wire.reverse (KS.W01.encodeNat 1)) (state [] (wire ++ KS.W01.encodeNat 1))
      (wire.length + 1) := by
    convert KS.W15.RationalMultiply.move_spec (0 : Fin 11) 5 (by decide)
      (state wire.reverse (KS.W01.encodeNat 1)) using 1
    · funext j
      fin_cases j <;> simp [state, SignedFloorMachine.«stacks», KS.W15.RationalMultiply.moveAfter]
    · simp [state, SignedFloorMachine.«stacks»]
  convert h₁.compose (h₂.compose h₃) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  omega

def ticks (q : ℚ) : ℕ :=
  KS.W29.polynomialFuel 32 2 (KS.W01.encodeRat q).length +
    ((Computability.encodeNat q.den).length + (SignedFloorMachine.rationalRemainder q).length + 2 +
      (2 * (KS.W01.encodeInt ⌊q⌋).length + 6))

theorem encodeRat_intCast (z : ℤ) :
    KS.W01.encodeRat (z : ℚ) = KS.W01.encodeInt z ++ KS.W01.encodeNat 1 := by
  simp [KS.W01.encodeRat]

end KS.W20.FloorRationalMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_MultiplicationInitialize
attribute [-simp] _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.MultiplicationInitialize

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody

def firstProgram : Program 7 := ofMachine (lift3 KS.W29.FrameDecoder.machine firstPorts)
def secondProgram : Program 7 := ofMachine (lift3 KS.W29.FrameDecoder.machine secondPorts)
def program : Program 7 := compose firstProgram secondProgram

@[simp] theorem input_port : program.input = 0 := rfl

end KS.W03.MultiplicationInitialize

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem core_spec (P : Program 10) (before after : Fin 10 → List Bool)
    (num den : List Bool) (negative : Bool) (ticks : ℕ)
    (h : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P corePorts)
      («stacks» before num den negative) («stacks» after num den negative) ticks :=
  KS.W01.FixedPortRunSpec.lift_runSpec P corePorts before after
    («stacks» before num den negative) («stacks» after num den negative) ticks h
    (stacks_core before num den negative) (stacks_core after num den negative)
    (stacks_spare before after num den negative)

end KS.W30.RationalMagnitudeMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMagnitudeSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

theorem zeroNumerator_spec (n : List Bool) (sgn : Bool) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram (10 : Fin 13))
      (state n [] sgn) (state [] [] sgn) (n.length + 1) := by
  intro bits hlen
  have h := KS.W04.BinaryStackMoves.run_clear_stacks (10 : Fin 13) (state n [] sgn) bits hlen
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W04.BinaryStackMoves.clearMachine (10 : Fin 13)) _ bits).trans ?_
  refine h.trans ?_
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

end KS.W30.RationalMagnitudeMachine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalMultiplicationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def inputBits (q r : ℚ) : List Bool := KS.W01.encodeRat q ++ KS.W01.encodeRat r

end KS.W15.RationalMultiply

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireProgramPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.WireProgram
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def ports3 {k : Nat} (a b c : Fin k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fin 3 ↪ Fin k := ⟨![a,b,c], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

def copyProgram {k : Nat} (a b c : Fin k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Program k := KS.W01.FixedCopy.program (ports3 a b c hab hac hbc)

def stayProgram {k : Nat} (port : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) port port (fun _ _ _ => Instruction.halt k 1))

def pushProgram {k : Nat} (port : Fin k) (b : Bool) : Program k :=
  ofMachine (compile (0 : Fin 1) port port (fun _ _ _ =>
    ⟨none,Vector.ofFn (fun j => if j = port then .push b else .stay)⟩))

def literalProgram {k : Nat} (port : Fin k) : List Bool → Program k
  | [] => stayProgram port
  | b :: bs => compose (literalProgram port bs) (pushProgram port b)

end KS.W15.WireProgram

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalDivisionStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W30.RationalDivision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def inputBits (q r : ℚ) : List Bool := KS.W01.encodeRat q ++ KS.W01.encodeRat r

end KS.W30.RationalDivision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.FixedDot

open scoped BigOperators

def pairPayload (p : ℚ × ℚ) : List Bool := KS.W01.encodeRat p.1 ++ KS.W01.encodeRat p.2

def pairWire (p : ℚ × ℚ) : List Bool := KS.W01.frame (pairPayload p)

def inputWire (ps : List (ℚ × ℚ)) : List Bool := ps.flatMap pairWire

@[simp] theorem inputWire_nil : inputWire [] = [] := rfl
@[simp] theorem inputWire_cons (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    inputWire (p :: ps) = pairWire p ++ inputWire ps := rfl

@[simp] theorem dotValue_nil : dotValue [] = 0 := rfl
@[simp] theorem dotValue_cons (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    dotValue (p :: ps) = p.1 * p.2 + dotValue ps := rfl

@[simp] theorem pairWire_length (p : ℚ × ℚ) :
    (pairWire p).length = 2 * (pairPayload p).length + 1 := KS.W01.length_frame _

theorem inputWire_cons_nonempty (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    inputWire (p :: ps) ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [inputWire_cons, List.length_append, pairWire_length, List.length_nil] at hl
  omega

theorem accumulator_step (a : ℚ) (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) :
    (a + p.1 * p.2) + dotValue ps = a + dotValue (p :: ps) := by
  rw [dotValue_cons, add_assoc]

end KS.W12.FixedDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotControl
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def boundary (source : List Bool) (a : ℚ) : Fin 19 → List Bool :=
  registers source [] [] (KS.W01.encodeRat a) []

def guard (heads : Fin 19 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 19 :=
  ⟨if (heads 16).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩

def loopProgram (body : Program 19) : Program 19 := KS.W29.FixedLoop.loop body guard

def loopConfig (body : Program 19) (source : List Bool) (a : ℚ) :
    Config 19 (loopProgram body).states :=
  ⟨some (loopProgram body).initial, boundary source a⟩

theorem step_empty (body : Program 19) (a : ℚ) (coin : Bool) :
    (loopProgram body).toMachine.step (loopConfig body [] a) coin =
      ⟨none, boundary [] a⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), boundary [] a⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  change Config.mk none _ = Config.mk none _
  congr 1
  funext j
  fin_cases j <;> rfl

theorem step_cons (body : Program 19) (b : Bool) (source : List Bool)
    (a : ℚ) (coin : Bool) :
    (loopProgram body).toMachine.step (loopConfig body (b :: source) a) coin =
      KS.W29.FixedLoop.liftBody body ⟨some body.initial, boundary (b :: source) a⟩ := by
  change (KS.W29.FixedLoop.loop body guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState body), boundary (b :: source) a⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases b <;>
    change Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _ =
      Config.mk (some (KS.W29.FixedLoop.bodyState body body.initial)) _
  all_goals
    congr 1
    funext j
    fin_cases j <;> rfl

theorem step_pair (body : Program 19) (p : ℚ × ℚ) (ps : List (ℚ × ℚ))
    (a : ℚ) (coin : Bool) :
    (loopProgram body).toMachine.step (loopConfig body (inputWire (p :: ps)) a) coin =
      KS.W29.FixedLoop.liftBody body
        ⟨some body.initial, boundary (inputWire (p :: ps)) a⟩ := by
  cases h : inputWire (p :: ps) with
  | nil => exact (inputWire_cons_nonempty p ps h).elim
  | cons b source => exact step_cons body b source a coin

theorem run_loop_of_body_spec (body : Program 19) (bodyTicks : (ℚ × ℚ) → ℚ → ℕ)
    (hbody : ∀ p ps a, RunSpec body (boundary (inputWire (p :: ps)) a)
      (boundary (inputWire ps) (a + p.1 * p.2)) (bodyTicks p a))
    (ps : List (ℚ × ℚ)) (a : ℚ) (bits : List Bool)
    (hlen : loopTicks bodyTicks ps a ≤ bits.length) :
    (loopProgram body).toMachine.run (loopConfig body (inputWire ps) a) bits =
      ⟨none, boundary [] (a + dotValue ps)⟩ := by
  induction ps generalizing a bits with
  | nil =>
      cases bits with
      | nil => simp [loopTicks] at hlen
      | cons coin rest =>
          simp only [inputWire_nil, dotValue_nil, add_zero]
          erw [Machine.run.eq_2, step_empty, Machine.run_halted _ _ rfl]
  | cons p ps ih =>
      cases bits with
      | nil => simp [loopTicks] at hlen
      | cons coin rest =>
          have ht : bodyTicks p a + loopTicks bodyTicks ps (a + p.1 * p.2) ≤ rest.length := by
            simp only [loopTicks, List.length_cons] at hlen
            omega
          obtain ⟨remaining, hremaining, hreturn⟩ :=
            (hbody p ps a).loop_body_then guard rest (by omega)
          erw [Machine.run.eq_2, step_pair]
          change (loopProgram body).toMachine.run
              (KS.W29.FixedLoop.liftBody body
                ⟨some body.initial, boundary (inputWire (p :: ps)) a⟩) rest =
            (loopProgram body).toMachine.run
              (loopConfig body (inputWire ps) (a + p.1 * p.2)) remaining at hreturn
          rw [hreturn]
          have hn : loopTicks bodyTicks ps (a + p.1 * p.2) ≤ remaining.length := by omega
          simpa only [loopConfig, loopProgram, KS.W29.FixedLoop.loop_initial,
            accumulator_step] using ih (a + p.1 * p.2) remaining hn

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.FixedDot

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def framePorts : Fin 3 ↪ Fin 19 where
  toFun i := if i = 0 then 16 else if i = 1 then 0 else 18
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def decodeProgram : Program 19 := ofMachine (lift3 KS.W29.FrameDecoder.machine framePorts)

end KS.W12.FixedDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def pushDispatch (b : Bool) (_ : Fin 1) (_heads : Fin 19 → Fin 3) (_coin : Bool) :
    Instruction 19 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 17 then .push b else .stay)⟩

def pushProgram (b : Bool) : Program 19 := ofMachine (compile 0 16 17 (pushDispatch b))

def «initialize_» : Program 19 :=
  compose (compose (compose (compose (pushProgram true) (pushProgram true))
    (pushProgram false)) (pushProgram true)) (pushProgram false)

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_FixedDotBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.FixedDot
open KS.W01 KS.W01.FixedStack KS.W29.FixedSequential

@[simp] theorem inputWire_append (xs ys : List (ℚ × ℚ)) :
    inputWire (xs ++ ys) = inputWire xs ++ inputWire ys := by simp [inputWire]

@[simp] theorem dotValue_append (xs ys : List (ℚ × ℚ)) :
    dotValue (xs ++ ys) = dotValue xs + dotValue ys := by simp [dotValue]

theorem count_le_wire (ps : List (ℚ × ℚ)) : ps.length ≤ (inputWire ps).length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [inputWire_cons, List.length_append, pairWire_length, List.length_cons]
      omega

theorem pairPayload_le_wire (p : ℚ × ℚ) (ps : List (ℚ × ℚ)) (hp : p ∈ ps) :
    (pairPayload p).length ≤ (inputWire ps).length := by
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
      simp only [List.mem_cons] at hp
      simp only [inputWire_cons, List.length_append, pairWire_length]
      rcases hp with rfl | hp
      · omega
      · have h := ih hp
        omega

end KS.W12.FixedDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotCounter
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def oneDispatch (_ : Fin 1) (_heads : Fin 29 → Fin 3) (_coin : Bool) : Instruction 29 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 7 then .push true else .stay)⟩
def oneProgram : Program 29 := ofMachine (compile 0 7 7 oneDispatch)

theorem one_spec (s : Fin 29 → List Bool) :
    RunSpec oneProgram s (put s 7 (true :: s 7)) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := by simpa using hbits
      subst rest
      refine (KS.W19.MachineTransport.run_ofMachine
        (compile (0 : Fin 1) (7 : Fin 29) 7 oneDispatch)
        (⟨some (0 : Fin 1), s⟩ : Config 29 1) [coin]).trans ?_
      simp only [Machine.run]
      refine (step_compile (0 : Fin 1) (7 : Fin 29) 7 oneDispatch
        (0 : Fin 1) s coin).trans ?_
      change Config.mk none _ = Config.mk none _
      congr 1
      funext j
      by_cases hj : j = 7
      · subst j
        simp [oneDispatch, put, Instruction.action, KS.W29.StackAction.apply]
      · simp [oneDispatch, put, Instruction.action, KS.W29.StackAction.apply, hj]

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotModel
attribute [-simp] _root_.OAI.KS.W08.AccessCounted.readMatrix_ops _root_.OAI.KS.W08.AccessCounted.readMatrix_value _root_.OAI.KS.W08.AccessCounted.readMatrix_work _root_.OAI.KS.W12.FixedDot.dotValue_append _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.RowDot
open KS.W07 Matrix
open scoped BigOperators

def vectorTape {n : ℕ} (x : Fin n → ℚ) : List Bool :=
  (List.ofFn (fun j => KS.W01.encodeRat (x j))).flatMap KS.W01.frame

def valueTape (xs : List ℚ) : List Bool := xs.flatMap (fun q => KS.W01.frame (KS.W01.encodeRat q))

def tailTape {n : ℕ} (xs : List (Fin n × ℚ)) : List Bool := valueTape (xs.map Prod.snd)

def rowPairs {n : ℕ} (M : DenseRatMatrix n) (i : Fin n) (xs : List (Fin n × ℚ)) :
    List (ℚ × ℚ) := xs.map (fun p => (DenseRatMatrix.decode M i p.1, p.2))

@[simp] theorem tailTape_indexedVector {n : ℕ} (x : Fin n → ℚ) :
    tailTape (indexedVector x) = vectorTape x := by
  simp only [tailTape, indexedVector, valueTape, vectorTape, List.map_ofFn]
  rw [show (List.ofFn (fun j => KS.W01.encodeRat (x j))) =
      (List.ofFn x).map KS.W01.encodeRat by simp [Function.comp_def]]
  rw [List.flatMap_map]
  rfl

@[simp] theorem tailTape_nil {n : ℕ} : tailTape ([] : List (Fin n × ℚ)) = [] := rfl
@[simp] theorem tailTape_cons {n : ℕ} (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) :
    tailTape (p :: xs) = KS.W01.frame (KS.W01.encodeRat p.2) ++ tailTape xs := rfl

@[simp] theorem rowPairs_nil {n : ℕ} (M : DenseRatMatrix n) (i : Fin n) : rowPairs M i [] = [] := rfl
@[simp] theorem rowPairs_cons {n : ℕ} (M : DenseRatMatrix n) (i : Fin n)
    (p : Fin n × ℚ) (xs : List (Fin n × ℚ)) :
    rowPairs M i (p :: xs) = (DenseRatMatrix.decode M i p.1, p.2) :: rowPairs M i xs := rfl

theorem rowPairs_dotValue {n : ℕ} (M : DenseRatMatrix n) (i : Fin n) (x : Fin n → ℚ) :
    FixedDot.dotValue (rowPairs M i (indexedVector x)) = (DenseRatMatrix.decode M *ᵥ x) i := by
  simp [rowPairs, indexedVector, FixedDot.dotValue, Matrix.mulVec, dotProduct, List.sum_ofFn]

def boundary {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n)
    (remaining : List (Fin n × ℚ)) (k : ℕ) (out : List Bool) : Fin 29 → List Bool :=
  state (KS.W08.denseMatrixTape M) (vectorTape x) (Computability.encodeNat i.val)
    (Computability.encodeNat n) (tailTape remaining) (Computability.encodeNat k) out

end KS.W12.RowDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixAddressArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W08.MatrixAddress

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W03.MultiplicationBody KS.W03.BinaryAccumulator

def cleanupProgram : Program 7 := KS.W04.ReusableArrayLookup.reoutput
  (KS.W04.BinaryStackMoves.clearProgram 2) 3

theorem reoutput_spec {k : ℕ} (P : Program k) (port : Fin k)
    (before after : Fin k → List Bool) (fuel : ℕ) (h : RunSpec P before after fuel) :
    RunSpec (KS.W04.ReusableArrayLookup.reoutput P port) before after fuel := by
  intro bits hbits
  erw [KS.W04.ReusableArrayLookup.run_reoutput]
  exact h bits hbits

theorem cleanup_spec (operand address : List Bool) :
    RunSpec cleanupProgram (registers [] [] operand address [] [] [])
      (registers [] [] [] address [] [] []) (operand.length + 1) := by
  apply reoutput_spec
  have h:=KS.W15.RationalMultiply.clear_spec (2 : Fin 7)
    (registers [] [] operand address [] [] [])
  have he : KS.W15.RationalMultiply.clearAfter 2 (registers [] [] operand address [] [] []) =
      registers [] [] [] address [] [] [] := by
    funext j
    fin_cases j <;> simp [KS.W15.RationalMultiply.clearAfter,registers]
  rw [he] at h
  exact h

end KS.W08.MatrixAddress

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_MatrixReadProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08.MatrixRead

open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W03.MultiplicationBody KS.W03.MachineCombinators

def accessProgram : Program 8 := KS.W29.FixedSequential.liftPorts binaryMatrixLookupProgram accessPorts

end KS.W08.MatrixRead

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotPrimitives
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def copyPorts (source target : Fin 29) (hst : source ≠ target)
    (hs : source ≠ 26) (ht : target ≠ 26) : Fin 3 ↪ Fin 29 :=
  ⟨![source, target, 26], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

def copyProgram (source target : Fin 29) (hst : source ≠ target)
    (hs : source ≠ 26) (ht : target ≠ 26) : Program 29 :=
  KS.W01.FixedCopy.program (copyPorts source target hst hs ht)

theorem copy_spec (source target : Fin 29) (hst : source ≠ target)
    (hs : source ≠ 26) (ht : target ≠ 26) (s : Fin 29 → List Bool)
    (hdst : s target = []) (hscratch : s 26 = []) :
    RunSpec (copyProgram source target hst hs ht) s (put s target (s source))
      (2 * (s source).length + 2) := by
  intro bits hbits
  refine (KS.W19.MachineTransport.run_ofMachine
    (KS.W01.FixedCopy.machine (copyPorts source target hst hs ht)) _ bits).trans ?_
  exact KS.W01.FixedCopy.run_copy_restore (copyPorts source target hst hs ht)
    s (s source) bits rfl hdst hscratch hbits

def decodeProgram : Program 29 := KS.W11.FrameWireCodec.unframeProgram decodePorts

theorem decode_spec (s : Fin 29 → List Bool) (payload tail : List Bool)
    (hs : s 23 = KS.W01.frame payload ++ tail) (hq : s 27 = []) (ht : s 26 = []) :
    RunSpec decodeProgram s (put (put s 23 tail) 27 payload) (3 * payload.length + 2) := by
  convert KS.W11.FrameWireCodec.unframe_spec decodePorts s payload tail using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> fin_cases j <;> simp [put, KS.W28.FixedPositiveSerializer.registers, decodePorts, hs, hq, ht])

def frameProgram : Program 29 := KS.W11.FrameWireCodec.frameProgram framePorts

theorem frame_spec (s : Fin 29 → List Bool) (h4 : s 4 = []) (ht : s 26 = []) :
    RunSpec frameProgram s (put s 28 (KS.W01.frame (s 28))) (4 * (s 28).length + 3) := by
  convert KS.W11.FrameWireCodec.frame_spec framePorts s (s 28) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> fin_cases j <;> simp [put, KS.W28.FixedPositiveSerializer.registers, framePorts, h4, ht])

def appendProgram : Program 29 := KS.W04.BinaryStackMoves.moveProgram 28 25

theorem append_spec (s : Fin 29 → List Bool) :
    RunSpec appendProgram s (put (put s 28 []) 25 ((s 28).reverse ++ s 25))
      ((s 28).length + 1) := by
  convert KS.W15.RationalMultiply.move_spec (28 : Fin 29) 25 (by decide) s using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  fin_cases j <;> simp [put, KS.W15.RationalMultiply.moveAfter]

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def copyColumn : Program 29 := copyProgram 24 0 (by decide) (by decide) (by decide)
def copyRow : Program 29 := copyProgram 21 1 (by decide) (by decide) (by decide)
def copyDimension : Program 29 := copyProgram 22 2 (by decide) (by decide) (by decide)

def pairProgram : Program 29 := compose (compose (compose
  (StackTransfer.program 27 28 26) (StackTransfer.program 0 28 26)) frameProgram) appendProgram

def collectTicks (n b k row : ℕ) (q : ℚ) : ℕ :=
  3 * (KS.W01.encodeRat q).length + 2 +
  (2 * (Computability.encodeNat k).length + 2) +
  (2 * (Computability.encodeNat row).length + 2) +
  (2 * (Computability.encodeNat n).length + 2) + 1024 * (n + 1) ^ 2 * (b + 1)

def pairTicks (a q : ℚ) : ℕ :=
  (2 * (KS.W01.encodeRat q).length + 2) + (2 * (KS.W01.encodeRat a).length + 2) +
  (4 * (KS.W01.encodeRat a ++ KS.W01.encodeRat q).length + 3) +
  ((KS.W01.frame (KS.W01.encodeRat a ++ KS.W01.encodeRat q)).length + 1)

def bodyTicks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ) (i : Fin n)
    (p : Fin n × ℚ) : ℕ := collectTicks n b p.1.val i.val p.2 +
  pairTicks (KS.W07.DenseRatMatrix.decode M i p.1) p.2 + incrementTicks p.1.val

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def guard (heads : Fin 29 → Fin 3) (_ : Bool) : KS.W29.FixedLoop.GuardInstruction 29 :=
  ⟨if (heads 23).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩

def loopTicks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ) (i : Fin n) :
    List (Fin n × ℚ) → ℕ
  | [] => 1
  | p :: ps => 1 + bodyTicks M b i p + loopTicks M b i ps

end KS.W12.RowDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def initialStacks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) :
    Fin 29 → List Bool :=
  state (KS.W08.denseMatrixTape M) (vectorTape x) (Computability.encodeNat i.val)
    (Computability.encodeNat n) [] [] []

def copyVector : Program 29 := copyProgram 20 23 (by decide) (by decide) (by decide)

def prepareTicks {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ) (x : Fin n → ℚ) (i : Fin n) : ℕ :=
  (2 * (vectorTape x).length + 2) + loopTicks M b i (indexedVector x)

def clearCounter : Program 29 := KS.W04.BinaryStackMoves.clearProgram 24
def restoreWire : Program 29 := KS.W04.BinaryStackMoves.moveProgram 25 16

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RowDotBounds
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W12.RowDot
open Matrix
open KS.W01 KS.W01.FixedStack KS.W07
open scoped BigOperators

def storedLength {n : ℕ} (M : DenseRatMatrix n) (x : Fin n → ℚ) (i : Fin n) : ℕ :=
  (KS.W08.denseMatrixTape M).length + (vectorTape x).length +
  (Computability.encodeNat i.val).length + (Computability.encodeNat n).length

theorem payload_le_framed (xs : List (List Bool)) (p : List Bool) (hp : p ∈ xs) :
    p.length ≤ (xs.flatMap frame).length := by
  induction xs with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      simp only [List.flatMap_cons, List.length_append, length_frame]
      rcases hp with rfl | hp
      · omega
      · have h := ih hp; omega

theorem count_le_framed (xs : List (List Bool)) : xs.length ≤ (xs.flatMap frame).length := by
  induction xs with
  | nil => simp
  | cons q qs ih => simp only [List.length_cons, List.flatMap_cons, List.length_append, length_frame]; omega

theorem dimension_le_vector {n : ℕ} (x : Fin n → ℚ) : n ≤ (vectorTape x).length := by
  simpa [vectorTape] using count_le_framed (List.ofFn (fun j => encodeRat (x j)))

end KS.W12.RowDot

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ZeroPaddedRow
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open scoped BigOperators

def literalDispatch {k : ℕ} (port : Fin k) (b : Bool) (_ : Fin 1)
    (_heads : Fin k → Fin 3) (_coin : Bool) : Instruction k 1 :=
  ⟨none, Vector.ofFn (fun j => if j = port then .push b else .stay)⟩
def literalPush {k : ℕ} (port : Fin k) (b : Bool) : Program k :=
  ofMachine (compile 0 port port (literalDispatch port b))

def prependZero {k : ℕ} (port : Fin k) : Program k :=
  compose (compose (compose (compose (compose (compose (compose (compose (compose (compose
    (literalPush port true) (literalPush port true)) (literalPush port false))
    (literalPush port true)) (literalPush port false)) (literalPush port false))
    (literalPush port false)) (literalPush port true)) (literalPush port false))
    (literalPush port false)) (literalPush port false)

theorem vectorTape_cons {n : ℕ} (a : ℚ) (y : Fin n → ℚ) :
    vectorTape (Fin.cons a y) = KS.W01.frame (KS.W01.encodeRat a) ++ vectorTape y := by
  simp [vectorTape, List.ofFn_succ]

def copyZeroPadded {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (KS.W01.FixedCopy.program ports) (prependZero (ports 1))

theorem zeroPadded_row_dot {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    (DenseRatMatrix.decode M *ᵥ zeroPadded y) 0 =
      ∑ j : Fin n, DenseRatMatrix.decode M 0 j.succ * y j := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, zeroPadded]

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_NegativeDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def minusOneProgram : Program 29 := compose (compose (compose (compose
  (literalPush 0 true) (literalPush 0 true)) (literalPush 0 false))
  (literalPush 0 true)) (literalPush 0 true)

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSignAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W16.RationalSignAction
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem liftCore_spec (P : Program 13) (before result : Fin 13 → List Bool)
    (tape : List Bool) (cost : ℕ) (h : RunSpec P before result cost) :
    RunSpec (KS.W29.FixedSequential.liftPorts P corePorts)
      (extend before tape) (extend result tape) cost :=
  KS.W01.FixedPortRunSpec.lift_runSpec P corePorts before result
    (extend before tape) (extend result tape) cost h
    (extend_on before tape) (extend_on result tape)
    (fun j hj => (extend_off result tape j hj).trans (extend_off before tape j hj).symm)

end KS.W16.RationalSignAction

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSignClassifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W06.RationalSignClassifier

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare
open KS.W04.CleanRationalCompare

def classifyDispatch (_ : Fin 1) (heads : Fin 13 → Fin 3) (_ : Bool) : Instruction 13 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 9 then
    if heads 12 = 2 then .push false else if heads 10 = 0 then .push true else .stay
    else .stay)⟩

end KS.W06.RationalSignClassifier

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RationalSubtractProgram
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W13.RationalSubtract
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem first_spec {n : ℕ} (hn : n ≤ 19) (P : Program n) (before after : Fin n → List Bool)
    (spare : Fin 19 → List Bool) (ticks : ℕ) (h : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P (firstPorts n hn))
      (extend before spare) (extend after spare) ticks := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec P (firstPorts n hn) _ _ _ _ _ h
  · intro i
    change dite (i.val < n) (fun h => before ⟨i.val, h⟩) _ = before i
    exact dite_eq_left i.isLt
  · intro i
    change dite (i.val < n) (fun h => after ⟨i.val, h⟩) _ = after i
    exact dite_eq_left i.isLt
  · intro j hj
    by_cases hb : j.val < n
    · exact (hj ⟨j.val,hb⟩ (Fin.ext rfl)).elim
    · simp [extend,hb]

def parsed (q r : ℚ) := registers (KS.W01.encodeRat r)
  (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den) [decide (q.num < 0)] [] [] [] []
def saved (q r : ℚ) := registers []
  (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den) [decide (q.num < 0)] [] (KS.W01.encodeRat r) [] []
def emitted (q r : ℚ) := registers [] (KS.W01.encodeRat q) [] [] [] (KS.W01.encodeRat r) [] []
def paired (q r : ℚ) := registers [] [] [] [] [] (KS.W01.encodeRat r) (KS.W01.encodeRat q) []
def prepared (q r : ℚ) := registers (KS.W01.encodeRat r) [] [] [] [] [] (KS.W01.encodeRat q) []
def marked (q r : ℚ) := registers (KS.W01.encodeRat r) [] [] [] [false] [] (KS.W01.encodeRat q) []
def negated (q r : ℚ) := registers [] (KS.W01.encodeRat (-r)) [] [] [false] [] (KS.W01.encodeRat q) []
def cleared (q r : ℚ) := registers [] (KS.W01.encodeRat (-r)) [] [] [] [] (KS.W01.encodeRat q) []
def withRight (q r : ℚ) := registers (KS.W01.encodeRat (-r)) [] [] [] [] [] (KS.W01.encodeRat q) []

theorem clearMark_spec (q r : ℚ) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram 13) (negated q r) (cleared q r) 2 := by
  have h := KS.W15.RationalMultiply.clear_spec (13 : Fin 19) (negated q r)
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

end KS.W13.RationalSubtract

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_SparseScalarNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.SparseScalarNodes
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.ComplexMachine

def divTicks (q r : ℚ) : ℕ := KS.W29.polynomialFuel 1100000 3
  (KS.W30.RationalDivision.inputBits q r).length

def put (s : Registers) (p : Fin 28) (q : ℚ) : Registers := Function.update s p (KS.W01.encodeRat q)

end KS.W19.SparseScalarNodes

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack
open KS.W29 (StackAction)
open KS.W29.FixedSequential

def transferDispatch (s : Fin 2) (heads : Fin 5 → Fin 3) (_coin : Bool) : Instruction 5 2 :=
  if (heads 0).val = 0 then Instruction.halt 5 2 else
    ⟨if s = 0 then (if (heads 0).val = 2 then none else some 1) else some 0,
      Vector.ofFn (fun j => if j = 0 then .pop else if j = 2 then .push ((heads 0).val == 2)
        else .stay)⟩

def transferMachine : Machine := compile 0 0 2 transferDispatch
def transferProgram : Program 5 := ofMachine transferMachine

def indexGuard (heads : Fin 5 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 5 :=
  if (heads 4).val = 0 then ⟨.halt, Vector.replicate 5 .stay⟩
  else ⟨.call, Vector.ofFn (fun j => if j = 4 then .pop else .stay)⟩

def prefixProgram : Program 5 := KS.W29.FixedLoop.loop transferProgram indexGuard

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack KS.W03.MachineCombinators
open KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup (run_compose_bounded)

def skipPorts : Fin 4 ↪ Fin 5 where
  toFun j := if j = 0 then 0 else if j = 1 then 1 else if j = 2 then 2 else 4
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def skipProgram : Program 5 :=
  KS.W29.FixedSequential.liftPorts KS.W11.FramedArray.skipProgram skipPorts

def reverseNew : Program 5 := KS.W04.BinaryStackMoves.moveProgram 1 3
def insertNew : Program 5 := KS.W04.BinaryStackMoves.moveProgram 3 0
def restorePrefix : Program 5 := KS.W04.BinaryStackMoves.moveProgram 2 0
def insertAndRestore : Program 5 := compose insertNew restorePrefix
def finishProgram : Program 5 := compose reverseNew insertAndRestore
def replaceTailProgram : Program 5 := compose skipProgram finishProgram

def program : Program 5 := compose prefixProgram replaceTailProgram

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayReplacementPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack
open KS.W29.FixedSequential

def liftedProgram {k : ℕ} (ports : Fin 5 ↪ Fin k) : Program k :=
  KS.W29.FixedSequential.liftPorts program ports

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.WireAppend

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def program {k : ℕ} (source target scratch : Fin k) : Program k :=
  compose (KS.W04.BinaryStackMoves.moveProgram source scratch)
    (KS.W04.BinaryStackMoves.moveProgram scratch target)

end KS.W07.WireAppend

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_BinaryToUnaryDeterministic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W03.BinaryToUnary
open KS.W29.FixedSequential

def program : Program 3 := ofMachine machine

end KS.W03.BinaryToUnary

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WordOperations
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.CurrentKS.Realization.listCode_nil _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.WordOperations
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine

def appendProgram : Program 3 := compose split (KS.W12.StackTransfer.program 1 0 2)
def appending : Routine (fun p : Word×Word => pair p.1 p.2) (fun p => p.1++p.2)
    (fun p => 5*p.1.length+4) where
  scratch := 2
  program := appendProgram
  spec p := by
    have h := KS.W12.StackTransfer.spec (1 : Fin 3) 0 2 (by decide) (by decide) (by decide)
      (smallState p.2 p.1 []) rfl
    have he : KS.W12.StackTransfer.after 1 0 (smallState p.2 p.1 [])=io (p.1++p.2) := by
      funext j;fin_cases j <;> simp [KS.W12.StackTransfer.after,smallState,io]
    rw [he] at h
    have h' := (split_spec p.1 p.2).compose h
    convert h' using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    simp [smallState]
    omega

end CurrentKS.WordOperations

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ZeroArrayConstructor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.ZeroArrayConstructor
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def emitDispatch (word : List Bool) (s : Fin (word.length + 1))
    (_heads : Fin 3 → Fin 3) (_coin : Bool) : Instruction 3 (word.length + 1) :=
  if h : s.val < word.length then
    ⟨some ⟨s.val + 1, by omega⟩,
      Vector.ofFn (fun j => if j = 1 then .push word[s.val] else .stay)⟩
  else Instruction.halt 3 (word.length + 1)

def emitProgram (word : List Bool) : Program 3 :=
  ofMachine (compile ⟨0, by omega⟩ 0 1 (emitDispatch word))

def zeroFrame : List Bool := KS.W01.frame (KS.W01.encodeRat 0)
def bodyProgram : Program 3 := emitProgram zeroFrame

def guard (heads : Fin 3 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 3 :=
  if (heads 0).val = 0 then ⟨.halt, Vector.replicate 3 .stay⟩
  else ⟨.call, Vector.ofFn (fun j => if j = 0 then .pop else .stay)⟩

def loopProgram : Program 3 := KS.W29.FixedLoop.loop bodyProgram guard
def finishProgram : Program 3 := KS.W04.BinaryStackMoves.moveProgram 1 2
def program : Program 3 := compose loopProgram finishProgram

end KS.W11.ZeroArrayConstructor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurReadStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurReadStage
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def copyPorts (source target : Fin 32) (hs : source ≠ target)
    (hc : source ≠ 16) (ht : target ≠ 16) : Fin 3 ↪ Fin 32 :=
  ⟨![source,target,16], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

def copyProgram (source target : Fin 32) (hs : source ≠ target)
    (hc : source ≠ 16) (ht : target ≠ 16) : Program 32 :=
  KS.W01.FixedCopy.program (copyPorts source target hs hc ht)

def prepare (row col : Bool) : Program 32 :=
  compose (copyProgram 26 2 (by decide) (by decide) (by decide))
    (compose (copyProgram (rowSource row) 1 (by cases row <;> decide)
      (by cases row <;> decide) (by decide))
      (copyProgram (colSource col) 0 (by cases col <;> decide)
        (by cases col <;> decide) (by decide)))

end KS.W07.SchurReadStage

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalZeroVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalZeroVector
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def copyProgram : Program 35 := KS.W01.FixedCopy.program copyPorts
def unaryProgram : Program 35 := liftPorts KS.W03.BinaryToUnary.program unaryPorts
def zeroProgram : Program 35 := liftPorts KS.W11.ZeroArrayConstructor.program zeroPorts
def program : Program 35 := compose copyProgram (compose unaryProgram zeroProgram)

end KS.W19.TerminalZeroVector

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalVectorReplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalVectorReplace
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators Matrix

def program : Program 35 := KS.W11.FramedArrayRewrite.liftedProgram ports

def zeroPayloads (n : ℕ) : List (List Bool) := List.replicate n (KS.W01.encodeRat 0)

def oneFrame : List Bool := KS.W01.frame (KS.W01.encodeRat 1)
def unitProgram : Program 35 := compose TerminalZeroVector.program
  (compose (KS.W15.WireProgram.literalProgram 0 oneFrame) program)

end KS.W19.TerminalVectorReplace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalSparseAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalSparseAssembly
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.TerminalVectorReplace

def unaryProgram : Program 35 := liftPorts KS.W03.BinaryToUnary.program unaryPorts

def setOneProgram : Program 35 := compose
  (KS.W15.WireProgram.literalProgram 0 oneFrame) (compose unaryProgram TerminalVectorReplace.program)

def frameProgram : Program 35 := KS.W11.FrameWireCodec.frameProgram framePorts
def headProgram : Program 35 := compose TerminalZeroVector.program
  (compose frameProgram (compose (KS.W07.WireAppend.program 28 0 16) TerminalVectorReplace.program))

def program : Program 35 := compose headProgram setOneProgram

end KS.W19.TerminalSparseAssembly

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_UniformElimination
attribute [-simp] _root_.OAI.KS.W17.schurEntryExpr_eval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

@[simp] theorem schurWitnessLift_zero_pivot {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (h : M 0 0 = 0)
    (y : Fin n → ℚ) : schurWitnessLift M y = Fin.cons 0 y := by
  simp [schurWitnessLift, h]

def pivotTerminal {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    Option (Fin (n+1) → ℚ) :=
  if M 0 0 < 0 then some (Pi.single 0 1)
  else if M 0 0 = 0 then
    (firstNonzeroOffDiagonal M).map (fun j => zeroPivotWitness M 0 j.succ)
  else none

def uniformNegativeWitness : (n : ℕ) →
    Matrix (Fin n) (Fin n) ℚ → Option (Fin n → ℚ)
  | 0, _ => none
  | n+1, M => match pivotTerminal M with
    | some q => some q
    | none => (uniformNegativeWitness n (schurTail M)).map (schurWitnessLift M)

theorem uniformNegativeWitness_eq (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ) :
    uniformNegativeWitness n M = rationalNegativeWitness n M := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : M 0 0 < 0
    · simp [uniformNegativeWitness, pivotTerminal, rationalNegativeWitness, hn]
    · by_cases hz : M 0 0 = 0
      · cases hf : firstNonzeroOffDiagonal M with
        | none =>
          have hl : schurWitnessLift M = (fun y : Fin n → ℚ => Fin.cons (0 : ℚ) y) := by
            funext y
            exact schurWitnessLift_zero_pivot M hz y
          simp [uniformNegativeWitness, pivotTerminal, rationalNegativeWitness,
            hz, hf, ih, hl]
        | some j =>
          simp [uniformNegativeWitness, pivotTerminal, rationalNegativeWitness, hz, hf]
      · simp [uniformNegativeWitness, pivotTerminal, rationalNegativeWitness, hn, hz, ih]

namespace PivotHistory

def restore : {n N : ℕ} → PivotHistory n N → (Fin n → ℚ) → (Fin N → ℚ)
  | _, _, .nil _, q => q
  | _, _, .push M rest, q => restore rest (schurWitnessLift M q)

@[simp] theorem restore_push {n N : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (h : PivotHistory (n+1) N) (q : Fin n → ℚ) :
    restore (.push M h) q = restore h (schurWitnessLift M q) := rfl

end PivotHistory
end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SavedPivotPacketMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08.SavedPivotPacket
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers)

def payload (dim row : List Bool) : List Bool := KS.W01.frame dim ++ row

def program : Program 5 := compose
  (compose (compose (KS.W11.FrameWireCodec.frameProgram dimPorts)
    (KS.W07.WireAppend.program 1 2 3))
    (KS.W11.FrameWireCodec.frameProgram packetPorts))
  (KS.W07.WireAppend.program 2 0 3)

def popProgram : Program 5 := compose
  (KS.W11.FrameWireCodec.unframeProgram outerPorts)
  (KS.W11.FrameWireCodec.unframeProgram innerPorts)

end KS.W08.SavedPivotPacket

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotHistoryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def saveProgram : Program 35 := liftPorts KS.W08.SavedPivotPacket.program savedPorts

def savedFrame (dim tape : List Bool) : List Bool :=
  KS.W01.frame (KS.W08.SavedPivotPacket.payload dim tape)

def restoreProgram : Program 35 := liftPorts KS.W08.SavedPivotPacket.popProgram savedPorts

def descendProgram : Program 35 := compose
  (compose saveProgram (KS.W07.WireAppend.program 23 31 33))
  (KS.W07.WireAppend.program 30 26 33)

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SchurWitnessHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open scoped BigOperators

def schurHead {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : ℚ :=
  -((∑ j : Fin n, DenseRatMatrix.decode M 0 j.succ * y j) / DenseRatMatrix.decode M 0 0)

end KS.W12.RowDot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_StoredWitnessLift
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W12.StoredWitnessLift
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W12.RowDot

def headBudget {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : ℕ :=
  KS.W29.polynomialFuel 10000000000000000 8 (storedLength M (zeroPadded y) 0)

def ticks {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : ℕ :=
  (2 * (vectorTape y).length + 13) + headBudget M y +
  (4 * (KS.W01.encodeRat (schurHead M y)).length + 3) +
  (2 * (vectorTape y).length + 2) +
  (2 * (KS.W01.frame (KS.W01.encodeRat (schurHead M y))).length + 2) +
  ((vectorTape (zeroPadded y)).length + 1)

def inputLength {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : ℕ :=
  (KS.W08.denseMatrixTape M).length + (Computability.encodeNat (n + 1)).length + (vectorTape y).length

theorem headBudget_le {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    headBudget M y ≤ 4299816960000000000000000 * (inputLength M y + 1) ^ 8 := by
  have hzero : (KS.W01.frame (KS.W01.encodeRat 0)).length = 11 := by decide
  have hdimZero : Computability.encodeNat 0 = [] := rfl
  have hlen : storedLength M (zeroPadded y) 0 = inputLength M y + 11 := by
    simp [storedLength, inputLength, zeroPadded, vectorTape_cons,
      List.length_append, hzero, hdimZero,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  unfold headBudget KS.W29.polynomialFuel
  rw [hlen]
  calc
    _ ≤ 10000000000000000 * (12 * (inputLength M y + 1)) ^ 8 :=
      Nat.mul_le_mul_left 10000000000000000 (Nat.pow_le_pow_left
        (show inputLength M y + 11 + 1 ≤ 12 * (inputLength M y + 1) by omega) 8)
    _ = _ := by ring

end KS.W12.StoredWitnessLift

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotWitnessMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def liftedTape {n : ℕ} (M : DenseRatMatrix (n+1)) (y : Fin n → ℚ) : List Bool :=
  KS.W12.RowDot.vectorTape (schurWitnessLift (DenseRatMatrix.decode M) y)

def replayTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (y : Fin n → ℚ) : ℕ :=
  KS.W12.StoredWitnessLift.ticks M y + KS.W12.StoredWitnessLift.inputLength M y +
    2 * (liftedTape M y).length + 6

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotReplayLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def historyTape : {n N : ℕ} → PivotHistory n N → List Bool
  | _, _, .nil _ => []
  | n, _, .push M rest =>
      savedFrame (Computability.encodeNat (n+1)) (KS.W08.denseMatrixTape (DenseRatMatrix.ofMatrix M)) ++
        historyTape rest

def replayGuard (heads : Fin 35 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 35 :=
  ⟨if (heads 32).val = 0 then .halt else .call, Vector.ofFn (fun _ => .stay)⟩

def restoreTicks : {n N : ℕ} → (h : PivotHistory n N) → (Fin n → ℚ) → ℕ
  | _, _, .nil _, _ => 1
  | n, _, .push M rest, y =>
      1 + (9 * (Computability.encodeNat (n+1)).length +
        3 * (KS.W08.denseMatrixTape (DenseRatMatrix.ofMatrix M)).length + 7 +
        replayTicks (DenseRatMatrix.ofMatrix M) y) +
        restoreTicks rest (schurWitnessLift M y)

end KS.W17.FixedPSD

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DenseElimination
attribute [-simp] _root_.OAI.KS.W08.AccessCounted.readMatrix_ops _root_.OAI.KS.W08.AccessCounted.readMatrix_value _root_.OAI.KS.W08.AccessCounted.readMatrix_work _root_.OAI.KS.W08.denseMatrixPayloads_length _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix
open KS.W07

def denseNegativeWitness : (n : ℕ) → DenseRatMatrix n → Option (Vector ℚ n)
  | 0, _ => none
  | n + 1, M =>
      let A := DenseRatMatrix.decode M
      if A 0 0 < 0 then some (Vector.ofFn (Pi.single 0 1))
      else if A 0 0 = 0 then
        match firstNonzeroOffDiagonal A with
        | some j => some (Vector.ofFn (zeroPivotWitness A 0 j.succ))
        | none =>
            (denseNegativeWitness n (DenseRatMatrix.ofMatrix (trailingMatrix A))).map
              (fun y => Vector.ofFn (Fin.cons 0 (decodeRatVector y)))
      else
        (denseNegativeWitness n (DenseRatMatrix.ofMatrix (schurTail A))).map
          (fun y => Vector.ofFn (schurWitnessLift A (decodeRatVector y)))

theorem denseNegativeWitness_decode (n : ℕ) (M : DenseRatMatrix n) :
    (denseNegativeWitness n M).map decodeRatVector =
      rationalNegativeWitness n (DenseRatMatrix.decode M) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let A := DenseRatMatrix.decode M
      have hA : DenseRatMatrix.decode M = A := rfl
      by_cases hnegative : A 0 0 < 0
      · simp [denseNegativeWitness, rationalNegativeWitness, hA, hnegative]
      · by_cases hzero : A 0 0 = 0
        · cases hfind : firstNonzeroOffDiagonal A with
          | some j =>
              simp [denseNegativeWitness, rationalNegativeWitness, hA, hzero, hfind]
          | none =>
              simp only [denseNegativeWitness, rationalNegativeWitness, hA,
                hzero, hfind, lt_self_iff_false, ite_false, if_false, ite_true, if_true]
              rw [map_materialized, ih, DenseRatMatrix.decode_ofMatrix]
        · simp only [denseNegativeWitness, rationalNegativeWitness, hA,
            hnegative, hzero, ite_false, if_false]
          rw [map_materialized, ih, DenseRatMatrix.decode_ofMatrix]

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotHistory
attribute [-simp] _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07

open Matrix

theorem selectedSchur_append_step {N k t : ℕ}
    (M : Matrix (Fin N) (Fin N) ℚ) (p : Fin k → Fin N)
    (r : Fin (t + 1) → Fin N) (hp : (M.submatrix p p).det ≠ 0)
    (ha : selectedSchur M p r 0 0 ≠ 0) :
    selectedSchur M (Fin.snoc p (r 0)) (fun i => r i.succ) =
      KS.W17.schurTail (selectedSchur M p r) := by
  let A := M.submatrix p p
  let B : Matrix (Fin k) Unit ℚ := fun i _ => M (p i) (r 0)
  let C : Matrix Unit (Fin k) ℚ := fun _ j => M (r 0) (p j)
  let D := scalarPivot (M (r 0) (r 0))
  let F := M.submatrix p (fun i : Fin t => r i.succ)
  let G : Matrix Unit (Fin t) ℚ := fun _ j => M (r 0) (r j.succ)
  let H := M.submatrix (fun i : Fin t => r i.succ) p
  let I : Matrix (Fin t) Unit ℚ := fun i _ => M (r i.succ) (r 0)
  let J := M.submatrix (fun i : Fin t => r i.succ) (fun i : Fin t => r i.succ)
  let S := selectedSchur M p r
  have hhead : D - C * A⁻¹ * B = scalarPivot (S 0 0) := by
    ext i j
    cases i; cases j
    rfl
  have hrow : G - C * A⁻¹ * F = (fun _ j => S 0 j.succ : Matrix Unit (Fin t) ℚ) := by
    ext i j
    cases i
    rfl
  have hcol : I - H * A⁻¹ * B = (fun i _ => S i.succ 0 : Matrix (Fin t) Unit ℚ) := by
    ext i j
    cases j
    rfl
  have htail : J - H * A⁻¹ * F = KS.W17.trailingMatrix S := by
    ext i j
    rfl
  have hdet : (D - C * A⁻¹ * B).det ≠ 0 := by
    rw [hhead, Matrix.det_unique]
    exact ha
  have hmap : Fin.snoc p (r 0) ∘ appendIndexEquiv k =
      Sum.elim p (fun _ : Unit => r 0) := by
    funext i
    cases i <;> simp [appendIndexEquiv]
  rw [← selectedSchur_reindex_selected M (Fin.snoc p (r 0))
    (fun i : Fin t => r i.succ) (appendIndexEquiv k), hmap]
  have hfull : M.submatrix (Sum.elim p (fun _ : Unit => r 0))
      (Sum.elim p (fun _ : Unit => r 0)) = Matrix.fromBlocks A B C D := by
    ext i j
    cases i <;> cases j <;> rfl
  have hleft : M.submatrix (fun i : Fin t => r i.succ)
      (Sum.elim p (fun _ : Unit => r 0)) = Matrix.fromCols H I := by
    ext i j
    cases j <;> rfl
  have hright : M.submatrix (Sum.elim p (fun _ : Unit => r 0))
      (fun i : Fin t => r i.succ) = Matrix.fromRows F G := by
    ext i j
    cases i <;> rfl
  unfold selectedSchur
  rw [hfull, hleft, hright]
  change J - Matrix.fromCols H I * (Matrix.fromBlocks A B C D)⁻¹ * Matrix.fromRows F G = _
  rw [KS.W30.nested_schur A B C D F G H I J hp hdet,
    hhead, hrow, hcol, htail, scalarPivot_inv ha]
  ext i j
  change S i.succ j.succ -
      (∑ _ : Unit, (∑ _ : Unit, S i.succ 0 * (S 0 0)⁻¹) * S 0 j.succ) =
    S i.succ j.succ - S i.succ 0 * S 0 j.succ / S 0 0
  simp only [Finset.univ_unique, Finset.sum_singleton]
  ring

inductive PivotTrace {N : ℕ} (M : Matrix (Fin N) (Fin N) ℚ) :
    {k t : ℕ} → (Fin k → Fin N) → (Fin t → Fin N) →
      Matrix (Fin t) (Fin t) ℚ → Prop
  | initial : PivotTrace M (fun i : Fin 0 => Fin.elim0 i) id M
  | zero {k t : ℕ} {p : Fin k → Fin N} {r : Fin (t + 1) → Fin N}
      {S : Matrix (Fin (t + 1)) (Fin (t + 1)) ℚ}
      (previous : PivotTrace M p r S) (pivot_zero : S 0 0 = 0) :
      PivotTrace M p (fun i => r i.succ) (KS.W17.schurTail S)
  | positive {k t : ℕ} {p : Fin k → Fin N} {r : Fin (t + 1) → Fin N}
      {S : Matrix (Fin (t + 1)) (Fin (t + 1)) ℚ}
      (previous : PivotTrace M p r S) (pivot_positive : 0 < S 0 0) :
      PivotTrace M (Fin.snoc p (r 0)) (fun i => r i.succ) (KS.W17.schurTail S)

theorem PivotTrace.originalSchur {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N} {r : Fin t → Fin N}
    {S : Matrix (Fin t) (Fin t) ℚ} (h : PivotTrace M p r S) :
    (M.submatrix p p).det ≠ 0 ∧ S = selectedSchur M p r := by
  induction h with
  | initial =>
    constructor
    · simp
    · ext i j
      simp [selectedSchur]
  | @zero k t p r S previous hz ih =>
    obtain ⟨hp, hs⟩ := ih
    refine ⟨hp, ?_⟩
    calc
      KS.W17.schurTail S = S.submatrix Fin.succ Fin.succ := by
        ext i j
        simp [KS.W17.schurTail, hz]
      _ = (selectedSchur M p r).submatrix Fin.succ Fin.succ := by rw [hs]
      _ = selectedSchur M p (fun i => r i.succ) :=
        (selectedSchur_restrict M p r Fin.succ).symm
  | @positive k t p r S previous hpos ih =>
    obtain ⟨hp, hs⟩ := ih
    have ha : selectedSchur M p r 0 0 ≠ 0 := by
      rw [← hs]
      exact ne_of_gt hpos
    refine ⟨selectedSchur_new_det_ne_zero M p r hp ha, ?_⟩
    rw [hs]
    exact (selectedSchur_append_step M p r hp ha).symm

theorem PivotTrace.size_bound {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N} {r : Fin t → Fin N}
    {S : Matrix (Fin t) (Fin t) ℚ} (h : PivotTrace M p r S) : k + t ≤ N := by
  induction h <;> omega

end KS.W07

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotHistoryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

open Matrix

theorem PivotTrace.entry_parts_size_le {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N} {r : Fin t → Fin N}
    {S : Matrix (Fin t) (Fin t) ℚ} (h : PivotTrace M p r S)
    (b : ℕ) (hnum : ∀ i j, (M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (M i j).den ≤ 2 ^ b) (i j : Fin t) :
    Nat.size (S i j).num.natAbs ≤ KS.W30.inverseBitBound N b ∧
      Nat.size (S i j).den ≤ KS.W30.inverseBitBound N b := by
  obtain ⟨hp, hs⟩ := h.originalSchur
  have hdim := h.size_bound
  have hi := i.isLt
  have hk : k ≤ N := by omega
  have hk1 : k + 1 ≤ N := by omega
  rw [hs, selectedSchur_entry_cleared_ratio M p r hp i j]
  exact KS.W30.cleared_minor_ratio_parts_size_le M b hnum hden
    (Fin.snoc p (r i)) (Fin.snoc p (r j)) p p hk1 hk
    (original_num_selected_det_ne_zero M p hp)

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_EliminationCallBounds
attribute [-simp] _root_.OAI.KS.W08.AccessCounted.readMatrix_ops _root_.OAI.KS.W08.AccessCounted.readMatrix_value _root_.OAI.KS.W08.AccessCounted.readMatrix_work _root_.OAI.KS.W08.denseMatrixPayloads_length _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open KS.W07

inductive DenseEliminationCall {N : ℕ} (A : DenseRatMatrix N) :
    {t : ℕ} → DenseRatMatrix t → Prop
  | initial : DenseEliminationCall A A
  | zero {t : ℕ} {S : DenseRatMatrix (t + 1)}
      (previous : DenseEliminationCall A S)
      (hzero : DenseRatMatrix.decode S 0 0 = 0)
      (hrow : firstNonzeroOffDiagonal (DenseRatMatrix.decode S) = none) :
      DenseEliminationCall A
        (DenseRatMatrix.ofMatrix (trailingMatrix (DenseRatMatrix.decode S)))
  | positive {t : ℕ} {S : DenseRatMatrix (t + 1)}
      (previous : DenseEliminationCall A S)
      (hpositive : 0 < DenseRatMatrix.decode S 0 0) :
      DenseEliminationCall A
        (DenseRatMatrix.ofMatrix (schurTail (DenseRatMatrix.decode S)))

theorem denseNegativeWitness_zero_recurse {t : ℕ} (S : DenseRatMatrix (t + 1))
    (hzero : DenseRatMatrix.decode S 0 0 = 0)
    (hrow : firstNonzeroOffDiagonal (DenseRatMatrix.decode S) = none) :
    denseNegativeWitness (t + 1) S =
      (denseNegativeWitness t
        (DenseRatMatrix.ofMatrix (trailingMatrix (DenseRatMatrix.decode S)))).map
          (fun y => Vector.ofFn (Fin.cons 0 (decodeRatVector y))) := by
  simp [denseNegativeWitness, hzero, hrow]

theorem denseNegativeWitness_positive_recurse {t : ℕ} (S : DenseRatMatrix (t + 1))
    (hpositive : 0 < DenseRatMatrix.decode S 0 0) :
    denseNegativeWitness (t + 1) S =
      (denseNegativeWitness t
        (DenseRatMatrix.ofMatrix (schurTail (DenseRatMatrix.decode S)))).map
          (fun y => Vector.ofFn (schurWitnessLift (DenseRatMatrix.decode S)
            (decodeRatVector y))) := by
  simp [denseNegativeWitness, not_lt.mpr hpositive.le, hpositive.ne']

theorem DenseEliminationCall.pivotTrace {N t : ℕ} {A : DenseRatMatrix N}
    {S : DenseRatMatrix t} (h : DenseEliminationCall A S) :
    ∃ k, ∃ p : Fin k → Fin N, ∃ r : Fin t → Fin N,
      PivotTrace (DenseRatMatrix.decode A) p r (DenseRatMatrix.decode S) := by
  induction h with
  | initial => exact ⟨0, (fun i => Fin.elim0 i), id, PivotTrace.initial⟩
  | @zero t S previous hz hrow ih =>
      obtain ⟨k, p, r, ht⟩ := ih
      refine ⟨k, p, (fun i => r i.succ), ?_⟩
      have htrace := PivotTrace.zero ht hz
      have he : schurTail (DenseRatMatrix.decode S) = trailingMatrix (DenseRatMatrix.decode S) := by
        ext i j
        simp [schurTail, trailingMatrix, hz]
      rw [he] at htrace
      simpa only [DenseRatMatrix.decode_ofMatrix] using htrace
  | @positive t S previous hp ih =>
      obtain ⟨k, p, r, ht⟩ := ih
      exact ⟨k + 1, Fin.snoc p (r 0), (fun i => r i.succ), by
        simpa using PivotTrace.positive ht hp⟩

theorem DenseEliminationCall.entry_parts_size_le {N t : ℕ} {A : DenseRatMatrix N}
    {S : DenseRatMatrix t} (h : DenseEliminationCall A S)
    (b : ℕ) (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2 ^ b) (i j : Fin t) :
    Nat.size (DenseRatMatrix.decode S i j).num.natAbs ≤ KS.W30.inverseBitBound N b ∧
      Nat.size (DenseRatMatrix.decode S i j).den ≤ KS.W30.inverseBitBound N b := by
  obtain ⟨k, p, r, ht⟩ := h.pivotTrace
  exact ht.entry_parts_size_le b hnum hden i j

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_UniformEliminationHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17
open KS.W07

theorem pivotTerminal_none_cases {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (ht : pivotTerminal M = none) :
    (M 0 0 = 0 ∧ firstNonzeroOffDiagonal M = none) ∨ 0 < M 0 0 := by
  have hn : ¬ M 0 0 < 0 := by
    intro h
    simp [pivotTerminal,h] at ht
  by_cases hz : M 0 0 = 0
  · left
    refine ⟨hz,?_⟩
    cases hf : firstNonzeroOffDiagonal M with
    | none => rfl
    | some j => simp [pivotTerminal,hz,hf] at ht
  · right
    exact lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hz)

theorem DenseEliminationCall.uniform_child {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix (n+1)} (h : DenseEliminationCall A M)
    (ht : pivotTerminal (DenseRatMatrix.decode M) = none) :
    DenseEliminationCall A (DenseRatMatrix.ofMatrix (schurTail (DenseRatMatrix.decode M))) := by
  rcases pivotTerminal_none_cases (DenseRatMatrix.decode M) ht with ⟨hz,hr⟩ | hp
  · rw [schurTail_zero_pivot _ hz]
    exact .zero h hz hr
  · exact .positive h hp

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_EliminationWitnessHeight
attribute [-simp] _root_.OAI.KS.W08.AccessCounted.readMatrix_ops _root_.OAI.KS.W08.AccessCounted.readMatrix_value _root_.OAI.KS.W08.AccessCounted.readMatrix_work _root_.OAI.KS.W08.denseMatrixPayloads_length _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open KS.W07

theorem schurWitnessLift_eq_prependLinear {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    schurWitnessLift M y =
      KS.W30.prependLinear (fun j => -(M 0 j.succ / M 0 0)) y := by
  unfold schurWitnessLift KS.W30.prependLinear
  apply congrArg (fun z : ℚ => (Fin.cons z y : Fin (n + 1) → ℚ))
  calc
    -(∑ j, M 0 j.succ * y j) / M 0 0 =
        ∑ j, -(M 0 j.succ * y j) / M 0 0 := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_neg_distrib, Finset.sum_mul]
    _ = ∑ j, -(M 0 j.succ / M 0 0) * y j := by
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem DenseEliminationCall.lift_coefficient_parts {N t : ℕ}
    {A : DenseRatMatrix N} {S : DenseRatMatrix (t + 1)}
    (h : DenseEliminationCall A S) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2 ^ b) (j : Fin t) :
    let c := -(DenseRatMatrix.decode S 0 j.succ / DenseRatMatrix.decode S 0 0)
    c.num.natAbs ≤ 2 ^ (2 * KS.W30.inverseBitBound N b) ∧
      c.den ≤ 2 ^ (2 * KS.W30.inverseBitBound N b) := by
  have hp := h.entry_parts_size_le b hnum hden 0 0
  have hr := h.entry_parts_size_le b hnum hden 0 j.succ
  have hd := KS.W30.div_parts_le_two_pow _ _
    (KS.W30.inverseBitBound N b) (KS.W30.inverseBitBound N b)
    (Nat.le_of_lt (Nat.size_le.mp hr.1)) (Nat.le_of_lt (Nat.size_le.mp hr.2))
    (Nat.le_of_lt (Nat.size_le.mp hp.1)) (Nat.le_of_lt (Nat.size_le.mp hp.2))
  simpa [Rat.num_neg_eq_neg_num, Rat.den_neg_eq_den, Int.natAbs_neg, two_mul] using hd

theorem CommonHeight.schurWitnessLift {n E H : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) {y : Fin n → ℚ}
    (hy : CommonHeight y E)
    (hcnum : ∀ j : Fin n, (-(M 0 j.succ / M 0 0)).num.natAbs ≤ 2 ^ H)
    (hcden : ∀ j : Fin n, (-(M 0 j.succ / M 0 0)).den ≤ 2 ^ H) :
    CommonHeight (schurWitnessLift M y) (E + (n + 1) * H + n + 1) := by
  obtain ⟨D, hD, hDb, Z, hy, hZ⟩ := hy
  rw [schurWitnessLift_eq_prependLinear]
  exact KS.W30.prependLinear_common_height _ y H E hcnum hcden D hD hDb Z hy hZ

theorem DenseEliminationCall.dimension_le {N t : ℕ} {A : DenseRatMatrix N}
    {S : DenseRatMatrix t} (h : DenseEliminationCall A S) : t ≤ N := by
  obtain ⟨k, p, r, hp⟩ := h.pivotTrace
  have hs := hp.size_bound
  omega

theorem denseNegativeWitness_commonHeight {N t : ℕ} (A : DenseRatMatrix N)
    (b : ℕ) (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2 ^ b)
    (S : DenseRatMatrix t) (hcall : DenseEliminationCall A S)
    (y : Vector ℚ t) (hout : denseNegativeWitness t S = some y) :
    CommonHeight (decodeRatVector y) (witnessHeightBudget N b t) := by
  let H := KS.W30.inverseBitBound N b
  let K := (N + 2) * (3 * H + 4)
  have hK : 3 * H + 3 ≤ K := by dsimp [K] <;> nlinarith
  change CommonHeight (decodeRatVector y) ((t + 1) * K)
  induction t with
  | zero => simp [denseNegativeWitness] at hout
  | succ t ih =>
      let M := DenseRatMatrix.decode S
      have hentry : ∀ i j, (M i j).num.natAbs ≤ 2 ^ H ∧ (M i j).den ≤ 2 ^ H := by
        intro i j
        have hb := hcall.entry_parts_size_le b hnum hden i j
        exact ⟨Nat.le_of_lt (Nat.size_le.mp hb.1), Nat.le_of_lt (Nat.size_le.mp hb.2)⟩
      by_cases hn : M 0 0 < 0
      · have he : y = Vector.ofFn (Pi.single 0 (1 : ℚ)) := by
          simpa [denseNegativeWitness, M, hn] using hout.symm
        subst y
        simpa using (commonHeight_single (0 : Fin (t + 1))).mono (Nat.zero_le ((t + 2) * K))
      · by_cases hz : M 0 0 = 0
        · cases hf : firstNonzeroOffDiagonal M with
          | some j =>
              have he : y = Vector.ofFn (zeroPivotWitness M 0 j.succ) := by
                simpa [denseNegativeWitness, M, hn, hz, hf] using hout.symm
              subst y
              have hq := hentry j.succ j.succ
              have hr := hentry 0 j.succ
              have hc : CommonHeight (zeroPivotWitness M 0 j.succ) (3 * H + 3) := by
                exact KS.W30.zeroPivot_pair_common_height 0 j.succ (Fin.succ_ne_zero j).symm
                  (M j.succ j.succ) (M 0 j.succ) H hq.1 hq.2 hr.1 hr.2
              simpa using hc.mono (show 3 * H + 3 ≤ (t + 2) * K by nlinarith)
          | none =>
              let T := DenseRatMatrix.ofMatrix (trailingMatrix M)
              have ht : DenseEliminationCall A T := DenseEliminationCall.zero hcall hz hf
              rw [denseNegativeWitness_zero_recurse S hz hf] at hout
              change (denseNegativeWitness t T).map
                (fun z => Vector.ofFn (Fin.cons 0 (decodeRatVector z))) = some y at hout
              cases ho : denseNegativeWitness t T with
              | none => simp [ho] at hout
              | some z =>
                  have he : y = Vector.ofFn (Fin.cons 0 (decodeRatVector z)) := by
                    simpa [ho] using hout.symm
                  subst y
                  have hc := (ih T ht z ho).cons_zero
                  simpa using hc.mono (show (t + 1) * K ≤ (t + 2) * K by nlinarith)
        · have hp : 0 < M 0 0 := lt_of_le_of_ne (not_lt.mp hn) (Ne.symm hz)
          let T := DenseRatMatrix.ofMatrix (schurTail M)
          have ht : DenseEliminationCall A T := DenseEliminationCall.positive hcall hp
          rw [denseNegativeWitness_positive_recurse S hp] at hout
          change (denseNegativeWitness t T).map
            (fun z => Vector.ofFn (schurWitnessLift M (decodeRatVector z))) = some y at hout
          cases ho : denseNegativeWitness t T with
          | none => simp [ho] at hout
          | some z =>
              have he : y = Vector.ofFn (schurWitnessLift M (decodeRatVector z)) := by
                simpa [ho] using hout.symm
              subst y
              have hc := CommonHeight.schurWitnessLift M (ih T ht z ho)
                (fun j => (hcall.lift_coefficient_parts b hnum hden j).1)
                (fun j => (hcall.lift_coefficient_parts b hnum hden j).2)
              have hdim := hcall.dimension_le
              have hinc : (t + 1) * (2 * H) + t + 1 ≤ K := by
                have hmul := Nat.mul_le_mul (show t + 1 ≤ N + 2 by omega)
                  (show 2 * H + 1 ≤ 3 * H + 4 by omega)
                dsimp [K]
                nlinarith
              simpa [H] using hc.mono
                (show (t + 1) * K + (t + 1) * (2 * H) + t + 1 ≤ (t + 2) * K by nlinarith)

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurCellMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurCellMachine

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def preparePair (source target : Fin 23) : Program 23 :=
  compose (WireAppend.program source target 16) (WireAppend.program target 0 16)

end KS.W07.SchurCellMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurCounters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurCounters

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W19.UnsignedPairSerializer (registers )

def pushDispatch {k : ℕ} (port : Fin k) (bit : Bool) (_ : Fin 1)
    (_heads : Fin k → Fin 3) (_coin : Bool) : Instruction k 1 :=
  ⟨none, Vector.ofFn (fun j => if j = port then .push bit else .stay)⟩

def pushProgram {k : ℕ} (port : Fin k) (bit : Bool) : Program k :=
  ofMachine (compile 0 port port (pushDispatch port bit))

end KS.W07.SchurCounters

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07.SchurDimension
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open SchurReadStage

def unaryProgram (column : Bool) : Program 32 := compose
  (copyProgram 30 0 (by decide) (by decide) (by decide))
  (liftPorts KS.W03.BinaryToUnary.program (unaryPorts column))

end KS.W07.SchurDimension

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurEntryMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurEntryMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def appendProgram : Program 32 := compose (KS.W11.FrameWireCodec.frameProgram framePorts)
  (KS.W04.BinaryStackMoves.moveProgram 10 23)

def finishProgram : Program 32 := compose (KS.W04.BinaryStackMoves.moveProgram 23 0)
  (WireAppend.program 0 23 16)

end KS.W07.SchurEntryMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_SchurTableMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurTableMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def guard (port : Fin 32) (heads : Fin 32 → Fin 3) (_coin : Bool) :
    KS.W29.FixedLoop.GuardInstruction 32 :=
  ⟨if (heads port).val = 0 then .halt else .call,
    Vector.ofFn (fun j => if j=port then .pop else .stay)⟩

def finish : Program 32 := compose (KS.W04.BinaryStackMoves.clearProgram 27)
  SchurEntryMachine.finishProgram

end KS.W07.SchurTableMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SchurLoopState
attribute [-simp] _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07.SchurLoopState
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def tailMatrix {n : ℕ} (M : DenseRatMatrix (n+1)) : DenseRatMatrix n :=
  DenseRatMatrix.ofMatrix (KS.W17.schurTail (DenseRatMatrix.decode M))

def «prefix» {n : ℕ} (M : DenseRatMatrix (n+1)) (s : ℕ) : List Bool :=
  ((KS.W08.denseMatrixPayloads (tailMatrix M)).take s).flatMap KS.W01.frame

@[simp] theorem prefix_zero {n : ℕ} (M : DenseRatMatrix (n+1)) : «prefix» M 0 = [] := by
  simp [«prefix»]

end KS.W07.SchurLoopState

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PivotDescentMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def matrixState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix n) : Fin 35 → List Bool :=
  state saved (Computability.encodeNat n) (KS.W08.denseMatrixTape M) [] []

def child {n : ℕ} (M : DenseRatMatrix (n+1)) : DenseRatMatrix n :=
  DenseRatMatrix.ofMatrix (schurTail (DenseRatMatrix.decode M))

def descentTicks {n : ℕ} (M : DenseRatMatrix (n+1)) (b : ℕ) : ℕ :=
  KS.W07.SchurTableMachine.totalTicks n b +
    (24*(Computability.encodeNat (n+1)).length+8*(KS.W08.denseMatrixTape M).length+
      2*(Computability.encodeNat n).length+2*(KS.W08.denseMatrixTape (child M)).length+26)

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_ControllerReachable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W07

inductive ControllerReachable {N : ℕ} (A : DenseRatMatrix N) :
    {n : ℕ} → DenseRatMatrix n → PivotHistory n N → Prop
  | initial : ControllerReachable A A (.nil N)
  | descend {n : ℕ} {M : DenseRatMatrix (n+1)} {h : PivotHistory (n+1) N}
      (previous : ControllerReachable A M h)
      (test : pivotTerminal (DenseRatMatrix.decode M) = none) :
      ControllerReachable A (child M) (.push (DenseRatMatrix.decode M) h)

theorem ControllerReachable.call {N n : ℕ} {A : DenseRatMatrix N} {M : DenseRatMatrix n}
    {h : PivotHistory n N} (hr : ControllerReachable A M h) : DenseEliminationCall A M := by
  induction hr with
  | initial => exact .initial
  | descend _ ht ih => exact ih.uniform_child ht

theorem uniform_witness_height {N n : ℕ} {A : DenseRatMatrix N}
    {M : DenseRatMatrix n} (hc : DenseEliminationCall A M) (b : ℕ)
    (hnum : ∀ i j, (DenseRatMatrix.decode A i j).num.natAbs ≤ 2^b)
    (hden : ∀ i j, (DenseRatMatrix.decode A i j).den ≤ 2^b)
    (q : Fin n → ℚ) (hq : uniformNegativeWitness n (DenseRatMatrix.decode M) = some q) :
    CommonHeight q (witnessHeightBudget N b n) := by
  have he := denseNegativeWitness_decode n M
  rw [← uniformNegativeWitness_eq, hq] at he
  cases hd : denseNegativeWitness n M with
  | none => simp [hd] at he
  | some y =>
    have hy : decodeRatVector y = q := by simpa [hd] using he
    rw [← hy]
    exact denseNegativeWitness_commonHeight A b hnum hden M hc y hd

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowBody
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W07.SchurReadStage

def select (heads : Fin 32 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 32 :=
  ⟨if (heads 29).val = 2 then .left else .right, Vector.ofFn (fun _ => .stay)⟩

end KS.W17.PivotRowBody

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def entry {n : ℕ} (M : DenseRatMatrix (n+1)) (a : ℕ) : ℚ :=
  if h : a < n+1 then DenseRatMatrix.decode M 0 ⟨a,h⟩ else 0

def state {n : ℕ} (M : DenseRatMatrix (n+1)) (a k : ℕ) (found : Bool) : Fin 32 → List Bool :=
  fun j => if j=31 then KS.W08.denseMatrixTape M else
    if j=26 then Computability.encodeNat (n+1) else if j=28 then Computability.encodeNat a else
    if j=25 then List.replicate k true else if j=24 then if found then [true] else [] else []

def guard (heads : Fin 32 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 32 :=
  if (heads 24).val ≠ 0 ∨ (heads 25).val = 0 then
    ⟨.halt, Vector.ofFn (fun _ => .stay)⟩
  else ⟨.call, Vector.ofFn (fun j => if j=25 then .pop else .stay)⟩

end KS.W17.PivotRowLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowInitialize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def initial {n : ℕ} (M : DenseRatMatrix (n+1)) : Fin 32 → List Bool := state M 0 0 false

end KS.W17.PivotRowLoop

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotRowFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotRowLoop
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def finishSelect (heads : Fin 32 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 32 :=
  ⟨if (heads 24).val = 0 then .right else .left, Vector.ofFn (fun _ => .stay)⟩

end KS.W17.PivotRowLoop

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotDecisionMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.PivotDecision
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def select (heads : Fin 32 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 32 :=
  ⟨if (heads 29).val = 2 then .left else .right, Vector.ofFn (fun _ => .stay)⟩

end KS.W17.PivotDecision

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotDecisionPorts
attribute [-simp] _root_.OAI.KS.W12.RowDot.rowPairs_cons _root_.OAI.KS.W12.RowDot.rowPairs_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

@[simp] theorem withSaved_initial {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) :
    withSaved saved (PivotRowLoop.initial M) = matrixState saved M := by
  funext j; fin_cases j <;>
    simp [withSaved,PivotRowLoop.initial,PivotRowLoop.state,matrixState,state,Computability.encodeNat,Computability.encodeNum]

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotTerminalMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def terminalSelect (heads : Fin 35 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 35 :=
  ⟨if (heads 29).val = 1 then .left else .right, Vector.ofFn (fun _ => .stay)⟩

def unitTicks (n : ℕ) : ℕ :=
  KS.W19.TerminalZeroVector.ticks (n+1) + (KS.W19.TerminalVectorReplace.oneFrame.length+1+
    (2*((KS.W19.TerminalVectorReplace.zeroPayloads (n+1)).flatMap KS.W01.frame).length+
      2*KS.W19.TerminalVectorReplace.oneFrame.length+3))

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotControllerBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def afterDecisionSelect (heads : Fin 35 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 35 :=
  ⟨if (heads 29).val = 0 then .left else .right, Vector.ofFn (fun _ => .stay)⟩

def finishTicks {n N : ℕ} (h : PivotHistory n N) (M : DenseRatMatrix n) (q : Fin n → ℚ) : ℕ :=
  (KS.W08.denseMatrixTape M).length+(Computability.encodeNat n).length+3+restoreTicks h q

end KS.W17.FixedPSD

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotControllerLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def controllerGuard (heads : Fin 35 → Fin 3) (_coin : Bool) : KS.W29.FixedLoop.GuardInstruction 35 :=
  if (heads 23).val ≠ 0 then ⟨.halt,Vector.ofFn (fun _ => .stay)⟩
  else if (heads 26).val ≠ 0 then ⟨.call,Vector.ofFn (fun _ => .stay)⟩
  else if (heads 32).val ≠ 0 then ⟨.restart,Vector.ofFn (fun j => if j=32 then .pop else .stay)⟩
  else ⟨.halt,Vector.ofFn (fun _ => .stay)⟩

def localBits {n : ℕ} (M : DenseRatMatrix n) : ℕ := (KS.W08.denseMatrixTape M).length

end KS.W17.FixedPSD

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotControllerCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

def witnessState {N : ℕ} (q : Option (Fin N → ℚ)) : Fin 35 → List Bool :=
  state [] [] [] [] (q.elim [] KS.W12.RowDot.vectorTape)

end KS.W17.FixedPSD

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FramedMapRoutine
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.CurrentKS.Realization.listCode_nil _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.FramedMapRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine

variable {α : Type*} {input output : α → Word} {cost : α → ℕ}

def state (n : ℕ) (value tail acc : Word) : Fin (n+5) → Word :=
  fun j => if j.val=0 then value else if j.val=n+1 then tail else if j.val=n+2 then acc else []

def decode (n : ℕ) : Program (n+5) := KS.W11.FrameWireCodec.unframeProgram (decodePorts n)
def frame (n : ℕ) : Program (n+5) := KS.W11.FrameWireCodec.frameProgram (framePorts n)
def append (n : ℕ) : Program (n+5) := KS.W04.BinaryStackMoves.moveProgram 0 (accumulator n)
def body (r : Routine input output cost) : Program (r.scratch+5) :=
  compose (decode r.scratch) (compose (liftPorts r.program (ports r.scratch))
    (compose (frame r.scratch) (append r.scratch)))
def scan (r : Routine input output cost) : Program (r.scratch+5) :=
  FiniteControl.whileNonempty (source r.scratch) (body r)
def setup (n : ℕ) : Program (n+5) := CleanRoutine.transfer 0 (work n) (source n)
def finish (n : ℕ) : Program (n+5) := KS.W04.BinaryStackMoves.moveProgram (accumulator n) 0

def program (r : Routine input output cost) : Program (r.scratch+5) :=
  compose (setup r.scratch) (compose (scan r) (finish r.scratch))

lemma state_ports (n : ℕ) (value tail acc : Word) (i : Fin (n+1)) :
    state n value tail acc (ports n i)=io value i := by
  have h₁ : i.val≠n+1 := by omega
  have h₂ : i.val≠n+2 := by omega
  simp [state,ports,io,h₁,h₂]

lemma state_other (n : ℕ) (u v tail acc : Word) (j : Fin (n+5))
    (hj : ∀ i,j≠ports n i) : state n u tail acc j=state n v tail acc j := by
  have hz : j.val≠0 := by intro hz;exact hj 0 (Fin.ext hz)
  simp [state,hz]

lemma element_spec (r : Routine input output cost) (x : α) (tail acc : Word) :
    RunSpec (liftPorts r.program (ports r.scratch))
      (state r.scratch (input x) tail acc) (state r.scratch (output x) tail acc) (cost x) := by
  exact KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (r.spec x)
    (state_ports _ _ _ _) (state_ports _ _ _ _) (state_other _ _ _ _ _)

lemma decode_spec (n : ℕ) (value tail acc : Word) :
    RunSpec (decode n) (state n [] (KS.W01.frame value++tail) acc)
      (state n value tail acc) (3*value.length+2) := by
  have h := KS.W11.FrameWireCodec.unframe_spec (decodePorts n) (state n [] [] acc) value tail
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> simp only [KS.W28.FixedPositiveSerializer.registers,decodePorts_0,decodePorts_1,decodePorts_2, state,source,work,Fin.ext_iff,Fin.val_zero] <;> split_ifs <;> simp_all)

lemma frame_spec (n : ℕ) (value tail acc : Word) :
    RunSpec (frame n) (state n value tail acc) (state n (KS.W01.frame value) tail acc)
      (4*value.length+3) := by
  have h := KS.W11.FrameWireCodec.frame_spec (framePorts n) (state n [] tail acc) value
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl) <;> funext j <;> simp only [KS.W28.FixedPositiveSerializer.registers,framePorts_0,framePorts_1,framePorts_2, state,work,scratch,Fin.ext_iff,Fin.val_zero] <;> split_ifs <;> simp_all)

lemma append_spec (n : ℕ) (value tail acc : Word) :
    RunSpec (append n) (state n value tail acc) (state n [] tail (value.reverse++acc))
      (value.length+1) := by
  have h := KS.W15.RationalMultiply.move_spec (0 : Fin (n+5)) (accumulator n)
    (by simp [Fin.ext_iff]) (state n value tail acc)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j
    dsimp [state,KS.W15.RationalMultiply.moveAfter]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all

def bodyTicks (input output : α → Word) (cost : α → ℕ) (x : α) :=
  (3*(input x).length+2)+cost x+(4*(output x).length+3)+
    ((KS.W01.frame (output x)).length+1)

lemma body_spec (r : Routine input output cost) (x : α) (tail acc : Word) :
    RunSpec (body r) (state r.scratch [] (KS.W01.frame (input x)++tail) acc)
      (state r.scratch [] tail ((KS.W01.frame (output x)).reverse++acc))
      (bodyTicks input output cost x) := by
  have h := (decode_spec r.scratch (input x) tail acc).compose
    ((element_spec r x tail acc).compose ((frame_spec r.scratch (output x) tail acc).compose
      (append_spec r.scratch (KS.W01.frame (output x)) tail acc)))
  simp only [bodyTicks,Nat.add_assoc] at h ⊢
  exact h

def scanTicks (input output : α → Word) (cost : α → ℕ) (xs : List α) : ℕ :=
  (xs.map (fun x => bodyTicks input output cost x+1)).sum+1

lemma scan_trace (r : Routine input output cost) (xs : List α) (acc : Word) :
    FiniteControl.Trace (source r.scratch) (body r)
      (state r.scratch [] (tape input xs) acc)
      (state r.scratch [] [] ((tape output xs).reverse++acc)) (scanTicks input output cost xs) := by
  induction xs generalizing acc with
  | nil =>
    simpa [tape,scanTicks] using (FiniteControl.Trace.stop (body := body r)
      (port := source r.scratch) (state r.scratch [] [] acc) (by simp [state]))
  | cons x xs ih =>
    have hs : state r.scratch [] (KS.W01.frame (input x)++tape input xs) acc (source r.scratch)≠[] := by
      have hn : KS.W01.frame (input x) ≠ [] := by
        intro he
        have hl := KS.W01.length_frame (input x)
        rw [he] at hl
        simp only [List.length_nil] at hl
        omega
      simpa [state] using (List.append_ne_nil_of_left_ne_nil hn _ : KS.W01.frame (input x)++tape input xs≠[])
    have h := FiniteControl.Trace.step hs (body_spec r x (tape input xs) acc)
      (ih ((KS.W01.frame (output x)).reverse++acc))
    have hc : bodyTicks input output cost x+scanTicks input output cost xs+1 =
        scanTicks input output cost (x::xs) := by simp [scanTicks]; omega
    rw [hc] at h
    simpa only [tape,List.flatMap_cons,List.reverse_append,List.append_assoc] using h

lemma setup_spec (n : ℕ) (word : Word) :
    RunSpec (setup n) (io word) (state n [] word []) (2*word.length+2) := by
  have h := CleanRoutine.transfer_spec (0 : Fin (n+5)) (work n) (source n)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (io word) (by simp [io]) (by simp [io])
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j
  dsimp [state,io,Function.update]
  simp only [Fin.ext_iff,Fin.val_zero]
  split_ifs <;> simp_all

lemma finish_spec (n : ℕ) (word : Word) :
    RunSpec (finish n) (state n [] [] word.reverse) (io word) (word.length+1) := by
  have h := KS.W15.RationalMultiply.move_spec (accumulator n) (0 : Fin (n+5))
    (by simp [Fin.ext_iff]) (state n [] [] word.reverse)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  · funext j
    dsimp [state,io,KS.W15.RationalMultiply.moveAfter]
    simp only [Fin.ext_iff,Fin.val_zero]
    split_ifs <;> simp_all
  · simp [state]

def ticks (input output : α → Word) (cost : α → ℕ) (xs : List α) :=
  2*(tape input xs).length+2+scanTicks input output cost xs+(tape output xs).length+1

def routine (r : Routine input output cost) :
    Routine (tape input) (tape output) (ticks input output cost) where
  scratch := r.scratch+4
  program := program r
  spec xs := by
    have h := FiniteControl.trace_spec (scan_trace r xs [])
    simp only [List.append_nil] at h
    have h' := (setup_spec r.scratch (tape input xs)).compose
      (h.compose (finish_spec r.scratch (tape output xs)))
    simp only [ticks,Nat.add_assoc] at h' ⊢
    exact h'

end CurrentKS.FramedMapRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ δ : Type*} {encA : α → Word} {encB : β → Word}
  {encC : γ → Word} {encD : δ → Word}

def Realizes.map {f : α → β} (r : Realizes encA encB f) :
    Realizes (listCode encA) (listCode encB) (List.map f) where
  cost := FramedMapRoutine.ticks encA (fun x => encB (f x)) r.cost
  routine := by
    have h := FramedMapRoutine.routine r.routine
    refine { scratch := h.scratch, program := h.program, spec := ?_ }
    intro xs
    simpa only [listCode,FramedMapRoutine.tape,List.flatMap_map,Function.comp_def] using h.spec xs

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_NaturalRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

def natAdd : Realizes (prodCode natCode natCode) natCode (fun p => p.1+p.2) where
  cost := fun p => 5*p.1+4
  routine := by
    have h := WordOperations.appending.reindex (fun p : ℕ×ℕ => (natCode p.1,natCode p.2))
    refine { scratch := h.scratch,program := h.program,spec := ?_ }
    intro p
    have hp := h.spec p
    simp only [natCode,List.length_replicate,List.replicate_add] at hp ⊢
    exact hp

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FloorCleanRoutine
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.CurrentKS.Realization.listCode_nil _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.FloorCleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine KS.W20.FloorRationalMachine

abbrev encode := KS.W01.encodeRat

def extract : Program 11 := CleanRoutine.transfer 5 10 0
lemma extract_spec (q : ℚ) : RunSpec extract (state [] (encode q)) (io (encode q))
    (2*(encode q).length+2) := by
  have h := CleanRoutine.transfer_spec (5 : Fin 11) 10 0 (by decide) (by decide) (by decide)
    (state [] (encode q)) rfl rfl
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
  funext j;fin_cases j <;> simp [state,KS.W19.SignedFloorMachine.«stacks»,io,Function.update]

def ticks (q : ℚ) : ℕ := KS.W29.polynomialFuel 64 2 (encode q).length+
  (2*(encode (⌊q⌋ : ℚ)).length+2)

end CurrentKS.FloorCleanRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArrayRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α γ : Type*}

def lengthList (ea : α → Word) : Realizes (listCode ea) natCode List.length :=
  (((constant (listCode ea) natCode 0).both (identity (listCode ea))).then
    ((first natCode ea).then natSucc).fold).congr (by
      intro xs
      simp)

def natMul : Realizes (prodCode natCode natCode) natCode (fun p => p.1*p.2) :=
  let l := first natCode natCode
  let r := second natCode natCode
  let init := r.both (constant (prodCode natCode natCode) natCode 0)
  let step := (first natCode natCode).both natAdd
  (((l.both init).then step.iterate).then (second natCode natCode)).congr (by
    intro p
    simp only [fold_natAdd,Nat.add_zero])

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_DependentBranchRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

variable {α β : Type*} {ea : α → Word} {eb : β → Word} {P : α → Prop} [DecidablePred P]

def Realizes.dite {f : {a // P a} → β} {g : {a // ¬P a} → β}
    (test : Realizes ea boolCode (fun a => decide (P a)))
    (r : Realizes (fun a : {a // P a} => ea a.val) eb f)
    (s : Realizes (fun a : {a // ¬P a} => ea a.val) eb g) :
    Realizes ea eb (fun a => if h : P a then f ⟨a,h⟩ else g ⟨a,h⟩) :=
  let n := r.routine.scratch+s.routine.scratch
  let r' := r.routine.pad n (Nat.le_add_right _ _)
  let s' := s.routine.pad n (Nat.le_add_left _ _)
  let encoded (a : α) : Word := prodCode boolCode ea (decide (P a),a)
  let prep : Realizes ea encoded id :=
    (test.both (identity ea)).changeOutput encoded id (fun _ => rfl)
  let branch : Realizes encoded eb (fun a => if h : P a then f ⟨a,h⟩ else g ⟨a,h⟩) := {
    cost := fun a => 5+(if h : P a then r.cost ⟨a,h⟩ else s.cost ⟨a,h⟩)+1
    routine := {
      scratch := n+2
      program := ConditionalRoutine.program n r'.program s'.program
      spec := fun a => by
        by_cases hp : P a
        · have h := (ConditionalRoutine.parse_spec n (ea a) true).compose
            (ConditionalRoutine.choose_true n _ (liftPorts s'.program (ConditionalRoutine.ports n)) _ _ _
              (ConditionalRoutine.core_spec n _ _ _ _ (r'.spec ⟨a,hp⟩)))
          simp only [encoded,prodCode,boolCode,hp,decide_true,dite_eq_left,Nat.add_assoc] at h ⊢
          exact h
        · have h := (ConditionalRoutine.parse_spec n (ea a) false).compose
            (ConditionalRoutine.choose_false n (liftPorts r'.program (ConditionalRoutine.ports n)) _ _ _ _
              (ConditionalRoutine.core_spec n _ _ _ _ (s'.spec ⟨a,hp⟩)))
          simp only [encoded,prodCode,boolCode,hp,decide_false,Nat.add_assoc] at h ⊢
          exact h } }
  prep.then branch

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VectorRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α β γ : Type*}

def singleton (ea : α → Word) : Realizes ea (listCode ea) (fun value => [value]) :=
  ((identity ea).both (constant ea (listCode ea) [])).then (consList ea)

def matVecValue (p : MatrixData×List ℚ) : List ℚ := p.1.map (fun row => dotValue (row,p.2))

def quadraticValue (p : List ℚ×MatrixData) : ℚ := dotValue (p.1,matVecValue (p.2,p.1))

lemma matrixAdd_data {n m : ℕ} (A B : Matrix (Fin n) (Fin m) ℚ) :
    zipDefault (zipDefault (fun p : ℚ×ℚ => p.1+p.2) 0 0) [] [] (matrixData A,matrixData B)=
      matrixData (A+B) := by
  rw [matrixData,matrixData,zipDefault_ofFn]
  simp only [vectorAdd_ofFn]
  rfl

lemma matrixScale_data {n m : ℕ} (q : ℚ) (A : Matrix (Fin n) (Fin m) ℚ) :
    (matrixData A).map (fun row => row.map (fun x => q*x))=matrixData (q • A) := by
  simp only [matrixData,List.map_ofFn,Function.comp_def]
  rfl

lemma matVec_data {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) (v : Fin m → ℚ) :
    matVecValue (matrixData A,List.ofFn v)=List.ofFn (A *ᵥ v) := by
  simp only [matVecValue,matrixData,List.map_ofFn,Function.comp_def,dot_ofFn]
  rfl

lemma quadratic_data {n : ℕ} (v : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    quadraticValue (List.ofFn v,matrixData A)=dotProduct v (A *ᵥ v) := by
  rw [quadraticValue,matVec_data,dot_ofFn]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_MatrixStructureRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

variable {α : Type*}
def Realizes.matrixTabulate {ea : α → Word} {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) :
    Realizes (prodCode (prodCode ea natCode) natCode) matrixCode
      (fun p => (List.range p.1.2).map (fun i => (List.range p.2).map (fun j => f ((p.1.1,i),j)))) :=
  let ec := prodCode ea natCode
  let ctx := first ec natCode
  let a := ctx.then (first ea natCode)
  let cols := ctx.then (second ea natCode)
  let i := second ec natCode
  let row := ((a.both i).both cols).then r.tabulate
  let input := first (prodCode ea natCode) natCode
  let av := input.then (first ea natCode)
  let rows := input.then (second ea natCode)
  let cv := second (prodCode ea natCode) natCode
  ((av.both cv).both rows).then row.tabulate

lemma identityMatrix_data (n : ℕ) :
    (List.range n).map (fun i => (List.range n).map (fun j => if i=j then (1:ℚ) else 0))=
      matrixData (1 : Matrix (Fin n) (Fin n) ℚ) := by
  rw [range_map_fin]
  simp only [range_map_fin,matrixData]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp [Matrix.one_apply,Fin.ext_iff]

def transposeData (M : MatrixData) : MatrixData :=
  (List.range M.length).map (fun i => (List.range M.length).map (fun j => (M.getD j []).getD i 0))

lemma transpose_data {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    transposeData (matrixData M)=matrixData M.transpose := by
  unfold transposeData matrixData
  simp only [List.length_ofFn,range_map_fin]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [getD_ofFn,getD_ofFn]
  rfl

def matrixMulData (p : MatrixData×MatrixData) : MatrixData :=
  p.1.map (fun row => (transposeData p.2).map (fun col => dotValue (row,col)))

lemma matrixMul_data {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    matrixMulData (matrixData A,matrixData B)=matrixData (A*B) := by
  unfold matrixMulData
  rw [transpose_data]
  simp only [matrixData,List.map_ofFn,Function.comp_def,dot_ofFn]
  rfl

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_DependentRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*}

def Realizes.tabulateFin {ea : α → Word} {eb : β → Word} {n : α → ℕ}
    {f : (Σ a,Fin (n a)) → β} (r : Realizes (finFamilyCode ea n) eb f)
    (rn : Realizes ea natCode n) :
    Realizes ea (listCode eb) (fun a => List.ofFn (fun i => f ⟨a,i⟩)) :=
  let pairs := ((identity ea).both (rn.then range)).then (identity (prodCode ea natCode)).mapCtx
  let typed := pairs.changeOutput (listCode (finFamilyCode ea n))
    (fun a => (List.finRange (n a)).map (fun i => (⟨a,i⟩ : Σ a,Fin (n a)))) (by
      intro a
      simp only [listCode,FramedMapRoutine.tape,List.flatMap_map,finFamilyCode,id_eq]
      rw [range_finRange,List.flatMap_map])
  (typed.then r.map).congr (by
    intro a
    rw [List.map_map]
    exact List.ofFn_eq_map.symm)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PSDCleanRoutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.PSDCleanRoutine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W07 KS.W17 KS.W17.FixedPSD
open CleanRoutine

abbrev Datum := Σ n : ℕ,DenseRatMatrix n

def input (a : Datum) : Word :=
  KS.W01.frame (Computability.encodeNat a.1)++KS.W08.denseMatrixTape a.2
def output (a : Datum) : Word :=
  (rationalNegativeWitness a.1 (DenseRatMatrix.decode a.2)).elim [] KS.W12.RowDot.vectorTape

def parsed (dimension data : Word) : Fin 35 → Word :=
  fun j => if j=26 then dimension else if j=0 then data else []

def controllerTicks (a : Datum) : ℕ :=
  KS.W29.polynomialFuel KS.W23.PSDControllerPolynomial.coefficient 58
    (KS.W08.denseMatrixTape a.2).length

def ticks (a : Datum) : ℕ :=
  (3*(Computability.encodeNat a.1).length+2)+(2*(KS.W08.denseMatrixTape a.2).length+2)+
    controllerTicks a+(2*(output a).length+2)

end CurrentKS.PSDCleanRoutine

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PencilArrayRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

abbrev PencilData := MatrixData×List MatrixData
abbrev pencilCode := prodCode matrixCode (listCode matrixCode)

def accumMatrix (p : MatrixData×(ℚ×MatrixData)) : MatrixData :=
  zipDefault (zipDefault (fun r : ℚ×ℚ => r.1+r.2) 0 0) [] []
    (p.1,p.2.2.map (fun row => row.map (fun x => p.2.1*x)))

def evalPencilData (p : PencilData×List ℚ) : MatrixData :=
  (zipDefault (id : ℚ×MatrixData → ℚ×MatrixData) 0 [] (p.2,p.1.2)).foldl
    (fun a b => accumMatrix (a,b)) p.1.1

def normalData (p : PencilData×List ℚ) : List ℚ :=
  p.1.2.map (fun m => -quadraticValue (p.2,m))

def pencilData {n m : ℕ} (B : RationalSDP.Pencil n m) : PencilData :=
  (matrixData B.constant,List.ofFn (fun i => matrixData (B.coeff i)))

lemma accumMatrix_data {m : ℕ} (A M : Matrix (Fin m) (Fin m) ℚ) (q : ℚ) :
    accumMatrix (matrixData A,(q,matrixData M))=matrixData (A+q • M) := by
  unfold accumMatrix
  rw [matrixScale_data,matrixAdd_data]

lemma fold_matrixData {m : ℕ} (xs : List (ℚ×Matrix (Fin m) (Fin m) ℚ))
    (A : Matrix (Fin m) (Fin m) ℚ) :
    (xs.map (fun p => (p.1,matrixData p.2))).foldl (fun a b => accumMatrix (a,b)) (matrixData A)=
      matrixData (A+(xs.map (fun p => p.1 • p.2)).sum) := by
  induction xs generalizing A with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,accumMatrix_data,ih,List.sum_cons]
    rw [add_assoc]

lemma evalPencil_data {n m : ℕ} (B : RationalSDP.Pencil n m) (y : Fin n → ℚ) :
    evalPencilData (pencilData B,List.ofFn y)=matrixData (B.eval y) := by
  unfold evalPencilData pencilData
  rw [zipDefault_ofFn]
  have he : List.ofFn (fun i => (y i,matrixData (B.coeff i)))=
      (List.ofFn (fun i => (y i,B.coeff i))).map (fun p => (p.1,matrixData p.2)) := by
    simp only [List.map_ofFn,Function.comp_def]
  change (List.ofFn (fun i => (y i,matrixData (B.coeff i)))).foldl _ _=_
  rw [he,fold_matrixData]
  simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn,RationalSDP.Pencil.eval]

lemma normalPencil_data {n m : ℕ} (B : RationalSDP.Pencil n m) (v : Fin m → ℚ) :
    normalData (pencilData B,List.ofFn v)=List.ofFn (B.normal v) := by
  simp only [normalData,pencilData,List.map_ofFn,Function.comp_def,quadratic_data]
  rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PencilCompileRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def matrixNegData (A : MatrixData) := A.map (fun row => row.map (fun x => -x))
def matrixSubData (p : MatrixData×MatrixData) : MatrixData :=
  zipDefault (zipDefault (fun q : ℚ×ℚ => q.1+q.2) 0 0) [] [] (p.1,matrixNegData p.2)
lemma matrixNeg_data {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    matrixNegData (matrixData A)=matrixData (-A) := by
  simp only [matrixNegData,matrixData,List.map_ofFn,Function.comp_def];rfl
lemma matrixSub_data {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    matrixSubData (matrixData A,matrixData B)=matrixData (A-B) := by
  rw [matrixSubData,matrixNeg_data,matrixAdd_data,sub_eq_add_neg]

variable {α : Type*}
def pencilFromEvalData (f : α×List ℚ → MatrixData) (p : α×ℕ) : PencilData :=
  let c := f (p.1,List.replicate p.2 0)
  (c,(List.range p.2).map (fun i => matrixSubData (f (p.1,basisData (p.2,i)),c)))

lemma pencilFromEval_data {n m : ℕ} (B : RationalSDP.Pencil n m)
    (f : α×List ℚ → MatrixData) (a : α)
    (h : ∀ y : Fin n → ℚ,f (a,List.ofFn y)=matrixData (B.eval y)) :
    pencilFromEvalData f (a,n)=pencilData B := by
  have hc : f (a,List.replicate n 0)=matrixData B.constant := by
    simpa [RationalSDP.Pencil.eval,Pi.zero_def] using h 0
  unfold pencilFromEvalData
  simp only [hc]
  rw [range_map_fin]
  unfold pencilData
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [basis_data,h,matrixSub_data]
  congr 1
  simp [RationalSDP.Pencil.eval,Pi.single_apply]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_StoredPSDRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

def matrixObjectCode (a : MatrixObject) : Word := prodCode natCode matrixCode (a.1,matrixData a.2)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoundedStepRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

abbrev stepParametersCode := prodCode ratCode ratCode
abbrev updateCode := prodCode stepParametersCode (prodCode vectorCode vectorCode)

def roundedUpdateValue (p : UpdateData) : List ℚ :=
  (zipDefault (fun q : ℚ×ℚ => q.1-q.2) 0 0
    (p.2.1,p.2.2.map (fun a => (p.1.1/(p.2.2.map abs).sum)*a))).map
      (fun q => RationalSDP.roundScalar p.1.2 q)

lemma roundedUpdate_ofFn {n : ℕ} (step mesh : ℚ) (y a : Fin n → ℚ) :
    roundedUpdateValue ((step,mesh),(List.ofFn y,List.ofFn a))=
      List.ofFn (RationalSDP.roundVector mesh (fun i => y i-step*a i/RationalSDP.l1 a)) := by
  unfold roundedUpdateValue
  simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn]
  rw [zipDefault_ofFn]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext i
  congr 2
  simp only [RationalSDP.l1]
  ring

structure PencilState where
  n : ℕ
  m : ℕ
  B : RationalSDP.Pencil n m
  step : ℚ
  mesh : ℚ
  y : Fin n → ℚ

abbrev pencilStateDataCode := prodCode pencilCode (prodCode stepParametersCode vectorCode)
def pencilStateData (s : PencilState) : PencilData×(StepParameters×List ℚ) :=
  (pencilData s.B,((s.step,s.mesh),List.ofFn s.y))
def pencilStateCode (s : PencilState) : Word := pencilStateDataCode (pencilStateData s)

def stateView : Realizes pencilStateCode pencilStateDataCode pencilStateData :=
  (identity pencilStateDataCode).reindex pencilStateCode pencilStateData (fun _ => rfl)

def statePencil : Realizes pencilStateCode pencilCode (fun s => pencilData s.B) :=
  stateView.then (first pencilCode (prodCode stepParametersCode vectorCode))
def stateParameters : Realizes pencilStateCode stepParametersCode (fun s => (s.step,s.mesh)) :=
  stateView.then ((second pencilCode (prodCode stepParametersCode vectorCode)).then
    (first stepParametersCode vectorCode))

lemma nonempty_witness_dimension {m : ℕ} (M : Matrix (Fin m) (Fin m) ℚ)
    (v : Fin m → ℚ) (h : KS.W17.rationalNegativeWitness m M=some v) : m≠0 := by
  cases m with
  | zero => simp only [KS.W17.rationalNegativeWitness] at h;cases h
  | succ m => omega

def PencilState.next (s : PencilState) : PencilState :=
  { s with y := s.B.next s.step s.mesh s.y }

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_SearchRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

structure SearchState where
  n : ℕ
  m : ℕ
  B : RationalSDP.Pencil n m
  r : ℚ
  R : ℚ
  y : Fin n → ℚ

def searchStateData (s : SearchState) : PencilData×(StepParameters×List ℚ) :=
  (pencilData s.B,((s.r,s.R),List.ofFn s.y))
def searchStateCode (s : SearchState) : Word := pencilStateDataCode (searchStateData s)

def SearchState.init (s : SearchState) : PencilState :=
  ⟨s.n,s.m,s.B,RationalSDP.searchStep s.n s.r,RationalSDP.searchMesh s.n s.r s.R,s.y⟩

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueDataRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def weightedSumData (p : ℕ×(List ℚ×List MatrixData)) : MatrixData :=
  (zipDefault (id : ℚ×MatrixData → ℚ×MatrixData) 0 [] p.2).foldl
    (fun a b => accumMatrix (a,b)) (matrixData (0 : Matrix (Fin p.1) (Fin p.1) ℚ))
lemma weightedSum_data {n N : ℕ} (A : Fin N → Matrix (Fin n) (Fin n) ℚ) (x : Fin N → ℚ) :
    weightedSumData (n,(List.ofFn x,List.ofFn (fun i => matrixData (A i))))=
      matrixData (∑ i,x i • A i) := by
  unfold weightedSumData
  rw [zipDefault_ofFn]
  have he : List.ofFn (fun i => (x i,matrixData (A i)))=
      (List.ofFn (fun i => (x i,A i))).map (fun p => (p.1,matrixData p.2)) := by
    simp only [List.map_ofFn,Function.comp_def]
  change (List.ofFn (fun i => (x i,matrixData (A i)))).foldl _ _=_
  rw [he,fold_matrixData]
  simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn,zero_add]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueEvalRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def matrixAddData (p : MatrixData×MatrixData) :=
  zipDefault (zipDefault (fun q : ℚ×ℚ => q.1+q.2) 0 0) [] [] p
def matrixScaleData (p : ℚ×MatrixData) := p.2.map (fun row => row.map (fun x => p.1*x))

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Algorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization algorithm. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree
open scoped MatrixOrder
variable {m d : ℕ}

def heavy (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) : Option (Fin m) :=
  (List.finRange m).find? (fun e => (KS.W17.rationalNegativeWitness d (testMatrix q t v s e)).isSome)

def advance (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ)
    (s : Fin m → ℚ) : Fin m → ℚ :=
  (heavy q t v s).elim s (fun e => Function.update s e (t*s e))

def scalesAt (q : ℕ) (t : ℚ) (v : Fin m → Fin d → ℚ) (k : ℕ) : Fin m → ℚ :=
  (advance q t v)^[k] (fun _ => 1)

def normalizedScales (q r : ℕ) (v : Fin m → Fin d → ℚ) : Fin m → ℚ :=
  scalesAt q (multiplier r) v (normalizationLength m r)

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization realization. -/

section


namespace AlgorithmicThinTrees.Normalization.Stack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open Matrix
lemma outer_data {d : ℕ} (v : Fin d → ℚ) :
    (List.ofFn v).map (fun q => (List.ofFn v).map (fun r => q*r))=
      matrixData (vecMulVec v v) := by
  simp only [List.map_ofFn,Function.comp_def,matrixData]
  rfl

def unaryPow (k : ℕ) : Realizes natCode natCode (fun n => n^k) :=
  match k with
  | 0 => (constant natCode natCode 1).congr (fun _ => rfl)
  | k+1 => (((unaryPow k).both (identity natCode)).then natMul).congr
      (fun _ => (pow_succ _ _).symm)

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_MatrixRealization
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

abbrev matrixView : Realizes matrixObjectCode (prodCode natCode matrixCode)
    (fun a => (a.1,matrixData a.2)) :=
  (identity (prodCode natCode matrixCode)).reindex matrixObjectCode
    (fun a => (a.1,matrixData a.2)) (fun _ => rfl)

abbrev matrixDim := matrixView.then (first natCode matrixCode)
abbrev matrixEntries := matrixView.then (second natCode matrixCode)

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ArraySums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array sums. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def matrixSumData (p : ℕ×List MatrixData) : MatrixData :=
  weightedSumData (p.1,(List.replicate p.2.length 1,p.2))
lemma matrixSum_data {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ) :
    matrixSumData (n,List.ofFn (fun i => matrixData (A i)))=matrixData (∑i,A i) := by
  unfold matrixSumData
  rw [List.length_ofFn,←List.ofFn_const (n:=m) (1:ℚ),weightedSum_data]
  simp

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_BinaryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

lemma intPayload_natCast (n : ℕ) : KS.W01.intPayload (n:ℤ)=n := rfl

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

def natSub : Realizes (prodCode natCode natCode) natCode (fun p => p.1-p.2) :=
  (((second natCode natCode).both (first natCode natCode)).then natPred.iterate).congr
    (fun p => pred_iterate p.1 p.2)

variable {α : Type*} {ea : α → Word} {f g : α → ℕ}
def Realizes.nadd (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natAdd
def Realizes.nmul (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natMul
def Realizes.nsub (r : Realizes ea natCode f) (s : Realizes ea natCode g) :=
  (r.both s).then natSub

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary root. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

abbrev rootCode := prodCode natCode natCode

end CurrentKS.Realization
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

def lowerPencil (H : MultiGraph n m) (x : StepFree n m) := x.matrix-H.laplacian univ
def upperPencil (H : MultiGraph n m) (x : StepFree n m) :=
  (3 : ℝ) • H.laplacian univ-x.matrix-∑ijk, x.multiplier ijk • triangleGenerator ijk

def edgePencil (H : MultiGraph n m) (s : ℝ) (x : StepFree n m) (e : Fin m) :=
  x.matrix-(6*s*x.y e) • vecMulVec (H.incidence e) (H.incidence e)

end StepFree

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Interior
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_z
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

lemma lowerPencil_hermitian (H : MultiGraph n m) (x : StepFree n m) :
    (x.lowerPencil H).IsHermitian :=
  (responseMatrix_hermitian x.1).sub (H.laplacian_psd univ).isHermitian

lemma upperPencil_hermitian (H : MultiGraph n m) (x : StepFree n m) :
    (x.upperPencil H).IsHermitian := by
  apply ((H.laplacian_psd univ).smul (by norm_num : (0 : ℝ) ≤ 3)).isHermitian.sub (responseMatrix_hermitian x.1) |>.sub
  change (∑ijk, x.multiplier ijk • triangleGenerator ijk)ᴴ = _
  rw [conjTranspose_sum]
  apply sum_congr rfl
  intro ijk _
  exact (triangleMatrix_hermitian _ _ _).smul (by rfl)

lemma edgePencil_hermitian (H : MultiGraph n m) (s : ℝ) (x : StepFree n m) (e : Fin m) :
    (x.edgePencil H s e).IsHermitian :=
  (responseMatrix_hermitian x.1).sub ((ShortcutDual.outer_posSemidef _).isHermitian.smul (by rfl))

end
end AlgorithmicThinTrees.MetricTests
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

@[simp] lemma encode_x (c : StepFree n m) (F : FlowPoint n m) (e : Fin m) :
    encode c F (edgeIndex 2 e)=F.x e := by simp [encode,edgeIndex]
@[simp] lemma encode_a (c : StepFree n m) (F : FlowPoint n m) (r : Fin n) (e : Fin m) :
    encode c F (flowIndex 0 r e)=F.a r e := by simp [encode,flowIndex]
@[simp] lemma encode_b (c : StepFree n m) (F : FlowPoint n m) (r : Fin n) (e : Fin m) :
    encode c F (flowIndex 1 r e)=F.b r e := by simp [encode,flowIndex]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_AffinePencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Affine pencil. -/

section

namespace AlgorithmicThinTrees.RationalForms
open Matrix Finset
open scoped BigOperators

def pencil {d N : ℕ} (A : Matrix (Fin N) (Fin N) (Affine d)) (hA : A.IsSymm) :
    CurrentKS.RationalSDP.Pencil d N where
  constant i j := (A i j).1
  coeff k i j := (A i j).2 k
  symmetric_constant := IsSymm.ext fun i j => congrArg Prod.fst (hA.apply i j)
  symmetric_coeff k := IsSymm.ext fun i j => congrArg (fun a => a.2 k) (hA.apply i j)

end AlgorithmicThinTrees.RationalForms
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Pencil
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_add _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_coord _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_cst _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_smul _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_sub _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_sum _root_.OAI.AlgorithmicThinTrees.RationalForms.Affine.rat_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation pencil. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations RationalForms
open scoped BigOperators
variable {n m : ℕ}

def qlap (H : MultiGraph n m) : Matrix (Fin n) (Fin n) ℚ :=
  ∑e, vecMulVec (qdiff (H.left e) (H.right e)) (qdiff (H.left e) (H.right e))

lemma cast_qinc (H : MultiGraph n m) (e : Fin m) (i : Fin n) :
    (qdiff (H.left e) (H.right e) i : ℝ)=H.incidence e i := cast_qdiff _ _ _
lemma cast_qlap (H : MultiGraph n m) (i j : Fin n) : (qlap H i j : ℝ)=H.laplacian univ i j := by
  simp [qlap,laplacian,Matrix.sum_apply,Rat.cast_sum,vecMulVec,cast_qinc]

def lowerForm (H : MultiGraph n m) : Matrix (Fin n) (Fin n) (Form n m) :=
  fun i j => matrixForm i j-Affine.cst (qlap H i j)

def upperForm (H : MultiGraph n m) : Matrix (Fin n) (Fin n) (Form n m) :=
  fun i j => Affine.cst (3*qlap H i j)-matrixForm i j-
    ∑ijk : DistinctTriple n, (qtriangle ijk i j) • Affine.coord (mulIndex ijk.val)

def edgeForm (H : MultiGraph n m) (s : ℚ) (e : Fin m) : Matrix (Fin n) (Fin n) (Form n m) :=
  fun i j => matrixForm i j-
    (6*s*qdiff (H.left e) (H.right e) i*qdiff (H.left e) (H.right e) j) • Affine.coord (edgeIndex 0 e)

lemma real_lowerForm (H : MultiGraph n m) (v : Fin (dimension n m) → ℝ) :
    (lowerForm H).map (Affine.real v)=(step v).lowerPencil H := by
  ext i j
  simp [lowerForm,real_matrixForm,cast_qlap,StepFree.lowerPencil,Matrix.sub_apply]
lemma real_upperForm (H : MultiGraph n m) (v : Fin (dimension n m) → ℝ) :
    (upperForm H).map (Affine.real v)=(step v).upperPencil H := by
  ext i j
  simp only [Matrix.map_apply,upperForm,Affine.real_sub,Affine.real_cst,Affine.real_sum,
    Affine.real_smul,Affine.real_coord,real_matrixForm,Rat.cast_mul,Rat.cast_ofNat,cast_qlap,cast_qtriangle]
  simp only [StepFree.upperPencil,step,StepFree.multiplier,multiplier,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]
  congr 1
  apply sum_congr rfl
  intro ijk _
  ring
lemma real_edgeForm (H : MultiGraph n m) (s : ℚ) (e : Fin m) (v : Fin (dimension n m) → ℝ) :
    (edgeForm H s e).map (Affine.real v)=(step v).edgePencil H (s:ℝ) e := by
  ext i j
  simp [edgeForm,real_matrixForm,cast_qinc,StepFree.edgePencil,step,StepFree.y,y,
    Matrix.sub_apply,vecMulVec]
  ring

def matrixBlocks (H : MultiGraph n m) (s : ℚ) (u : Fin m → ℚ) :
    MatBlock m → Matrix (Fin n) (Fin n) (Form n m)
  | .inl p => if p=0 then lowerForm H else upperForm H
  | .inr e => if 0<u e then edgeForm H s e else 0

lemma matrixBlocks_symmetric (H : MultiGraph n m) (s : ℚ) (u : Fin m → ℚ) (b : MatBlock m) :
    (matrixBlocks H s u b).IsSymm := by
  apply symmetric_of_real
  intro v
  cases b with
  | inl p =>
    simp only [matrixBlocks]
    split_ifs
    · rw [real_lowerForm]
      exact isHermitian_iff_isSymm.mp (lowerPencil_hermitian H _)
    · rw [real_upperForm]
      exact isHermitian_iff_isSymm.mp (upperPencil_hermitian H _)
  | inr e =>
    simp only [matrixBlocks]
    split_ifs
    · rw [real_edgeForm]
      exact isHermitian_iff_isSymm.mp (edgePencil_hermitian H _ _ _)
    · simp

def capacityForm (κ : ℚ) (u : Fin m → ℚ) (e : Fin m) : Form n m :=
  if 0<u e then Affine.coord (edgeIndex 1 e) else Affine.cst κ

def scalarForms (H : MultiGraph n m) (κ t qbar ε : ℚ) (u : Fin m → ℚ) :
    ScalarBlock n m → Form n m
  | .inl ijk => if ijk.1≠ijk.2.1 ∧ ijk.2.1≠ijk.2.2 ∧ ijk.1≠ijk.2.2 then Affine.coord (mulIndex ijk) else 0
  | .inr (.inl (p,e)) =>
    ![Affine.coord (edgeIndex 0 e),Affine.cst 1-Affine.coord (edgeIndex 0 e),
      Affine.coord (edgeIndex 1 e),Affine.cst (κ+1)-Affine.coord (edgeIndex 1 e),
      if 0<u e then Affine.cst (κ+u e)-Affine.coord (edgeIndex 1 e)+
        t • ((5:ℚ) • Affine.coord (edgeIndex 0 e)-Affine.cst 4) else 0,
      Affine.coord (edgeIndex 2 e),capacityForm κ u e-Affine.coord (edgeIndex 2 e)] p
  | .inr (.inr (.inl (p,(r,e)))) =>
    ![Affine.coord (flowIndex 0 r e),Affine.coord (flowIndex 1 r e),
      Affine.coord (flowIndex 0 r e)+Affine.coord (flowIndex 1 r e)-Affine.coord (edgeIndex 2 e)] p
  | .inr (.inr (.inr (.inl (r,v)))) =>
    Affine.cst (if v=r then ε else qbar)-∑e,
      ((if H.left e=v then Affine.coord (flowIndex 0 r e) else 0)+
        (if H.right e=v then Affine.coord (flowIndex 1 r e) else 0))
  | .inr (.inr (.inr (.inr _))) =>
    (∑e, Affine.coord (edgeIndex 2 e))-Affine.cst (qbar*((n:ℚ)-1)-ε)

def affineMatrix (H : MultiGraph n m) (s κ t qbar ε : ℚ) (u : Fin m → ℚ) :
    Matrix (Fin (order n m)) (Fin (order n m)) (Form n m) :=
  (Matrix.fromBlocks (Matrix.blockDiagonal (matrixBlocks H s u)) 0 0
    (Matrix.diagonal (scalarForms H κ t qbar ε u))).submatrix (rowIndex n m).symm (rowIndex n m).symm

lemma affineMatrix_symmetric (H : MultiGraph n m) (s κ t qbar ε : ℚ) (u : Fin m → ℚ) :
    (affineMatrix H s κ t qbar ε u).IsSymm := by
  apply IsSymm.submatrix
  apply IsSymm.ext
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [Matrix.fromBlocks_apply₁₁,Matrix.blockDiagonal,Matrix.of_apply]
      by_cases h : i.2=j.2
      · simp only [h,ite_true, if_true]
        exact (matrixBlocks_symmetric H s u j.2).apply _ _
      · simp only [h,Ne.symm h,ite_false, if_false]
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j =>
      exact (Matrix.isSymm_diagonal _).apply i j

def continuationPencil (H : MultiGraph n m) (s κ t qbar ε : ℚ) (u : Fin m → ℚ) :
    CurrentKS.RationalSDP.Pencil (dimension n m) (order n m) :=
  pencil (affineMatrix H s κ t qbar ε u) (affineMatrix_symmetric H s κ t qbar ε u)

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PencilCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation pencil correctness. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations RationalForms
open scoped BigOperators
variable {n m : ℕ}

@[simp] lemma step_y (v : Fin (dimension n m) → ℝ) (e : Fin m) :
    (step v).y e = v (edgeIndex 0 e) := rfl
@[simp] lemma step_z (v : Fin (dimension n m) → ℝ) (e : Fin m) :
    (step v).z e = v (edgeIndex 1 e) := rfl
@[simp] lemma step_mul (v : Fin (dimension n m) → ℝ) (ijk : DistinctTriple n) :
    (step v).multiplier ijk = v (mulIndex ijk.val) := rfl
@[simp] lemma flow_x (v : Fin (dimension n m) → ℝ) (e : Fin m) :
    (flow v).x e = v (edgeIndex 2 e) := rfl
@[simp] lemma flow_a (v : Fin (dimension n m) → ℝ) (r : Fin n) (e : Fin m) :
    (flow v).a r e = v (flowIndex 0 r e) := rfl
@[simp] lemma flow_b (v : Fin (dimension n m) → ℝ) (r : Fin n) (e : Fin m) :
    (flow v).b r e = v (flowIndex 1 r e) := rfl

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Search
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation search. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations
open scoped BigOperators
variable {n m : ℕ}

def boundQ (n m : ℕ) : ℚ := 6*sizeQ n m*(dimension n m+1)
@[simp] lemma cast_boundQ (n m : ℕ) : (boundQ n m:ℝ)=6*graphSize n m*(dimension n m+1) := by
  simp [boundQ]
@[simp] lemma cast_errorQ (n m : ℕ) : (errorQ n m:ℝ)=(graphSize n m)^(-10:ℤ) := by
  simp [errorQ]

def search (H : MultiGraph n m) (s qbar : ℚ) (u : Fin m → ℚ) : Fin (dimension n m) → ℚ :=
  (continuationPencil H s (baselineQ m) (stepQ m) qbar (errorQ n m) u).search
    (radiusQ n m) (boundQ n m) 0

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

def update (H : MultiGraph n m) (r : ℕ) (g : ℚ) (a : State n m) : State n m :=
  let v := search H a.scale (target m r a.quality g) a.capacity
  { scale := (1+stepQ m)*a.scale
    quality := a.quality-2*g*r*stepQ m
    matrix := (1-stepQ m) • a.matrix+stepQ m • qresponse (rawMatrix v)
    capacity := fun e => if 0 < a.capacity e then max 0 (z v e-baselineQ m) else 0 }

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GraphRealization
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

def numEdges : Realizes graphCode natCode Graph.m :=
  (lefts.then (lengthList natCode)).congr (fun _a => List.length_ofFn)

end AlgorithmicThinTrees.GraphStack

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix
open scoped BigOperators

lemma matIndex_val {n m : ℕ} (i j : Fin n) : (matIndex (m:=m) i j).val=j.val+n*i.val := rfl

abbrev dimsCode := prodCode natCode natCode
abbrev variablesCode := prodCode dimsCode vectorCode
abbrev variablesDims := first dimsCode vectorCode
abbrev variablesN := variablesDims.then (first natCode natCode)
abbrev variableValues := second dimsCode vectorCode

def dimensionProgram : Realizes dimsCode natCode (fun p => dimension p.1 p.2) :=
  let n := first natCode natCode
  let m := second natCode natCode
  (n.nmul n).nadd ((n.nmul (n.nmul n)).nadd
    (((constant dimsCode natCode 3).nmul m).nadd
      ((constant dimsCode natCode 2).nmul (n.nmul m))))

abbrev varEntryCode := prodCode (prodCode variablesCode natCode) natCode
abbrev varEntryContext := first (prodCode variablesCode natCode) natCode
abbrev varEntryVars := varEntryContext.then (first variablesCode natCode)
abbrev varEntryI := varEntryContext.then (second variablesCode natCode)
abbrev varEntryJ := second (prodCode variablesCode natCode) natCode

lemma raw_data {n m : ℕ} (v : Fin (dimension n m) → ℚ) :
    (List.range n).map (fun i => (List.range n).map
      (fun j => (List.ofFn v).getD (j+n*i) 0))=matrixData (rawMatrix v) := by
  simp only [range_map_fin,matrixData]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  rw [←matIndex_val i j,getD_ofFn]
  rfl

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation start. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

def initial (H : MultiGraph n m) (r : ℕ) : State n m :=
  ⟨1/2,r,qlap H,fun _ => 1⟩

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Loop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation loop. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

def advance (H : MultiGraph n m) (r : ℕ) (a : State n m) : State n m :=
  if a.scale^4 < (r:ℚ) then update H r (gain r) a else a

def stateAt (H : MultiGraph n m) (r i : ℕ) : State n m :=
  (advance H r)^[i] (initial H r)

def extractState (H : MultiGraph n m) (r : ℕ) : State n m :=
  stateAt H r (scheduleLength m r)

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_FiniteFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite families. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
variable {I J : α → Type*} {n m : α → ℕ}

def indexedCode (ea : α → Word) (e : (a : α) → I a ≃ Fin (n a)) (p : Σ a,I a) : Word :=
  prodCode ea natCode (p.1,(e p.1 p.2).val)

def indexedFirst (e : (a : α) → I a ≃ Fin (n a)) :
    Realizes (indexedCode ea e) ea (fun p => p.1) :=
  (first ea natCode).reindex (indexedCode ea e) (fun p => (p.1,(e p.1 p.2).val))
    (fun _ => rfl)
def indexedIndex (e : (a : α) → I a ≃ Fin (n a)) :
    Realizes (indexedCode ea e) natCode (fun p => (e p.1 p.2).val) :=
  (second ea natCode).reindex (indexedCode ea e) (fun p => (p.1,(e p.1 p.2).val))
    (fun _ => rfl)

def Realizes.tabulateIndexed {e : (a : α) → I a ≃ Fin (n a)} {f : (Σ a,I a) → β}
    (r : Realizes (indexedCode ea e) eb f) (rn : Realizes ea natCode n) :
    Realizes ea (listCode eb) (fun a => List.ofFn (fun i => f ⟨a,(e a).symm i⟩)) :=
  (r.reindex (finFamilyCode ea n) (fun p => ⟨p.1,(e p.1).symm p.2⟩)
    (fun p => by simp only [indexedCode,finFamilyCode,Equiv.apply_symm_apply])).tabulateFin rn

lemma sumLeft_code (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (p : {p : Σ a,I a ⊕ J a // p.2.isLeft=true}) :
    indexedCode ea (sumEquiv e e') p.val=indexedCode ea e (sumLeft e e' p) := by
  rcases p with ⟨⟨a,i|j⟩,h⟩
  · rfl
  · simp at h

def indexedSumRight (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (rn : Realizes ea natCode n) :
    Realizes (fun p : {p : Σ a,I a ⊕ J a // ¬p.2.isLeft=true} =>
      indexedCode ea (sumEquiv e e') p.val) (indexedCode ea e') (sumRight e e') :=
  let view := (identity (indexedCode ea (sumEquiv e e'))).reindex
    (fun p : {p : Σ a,I a ⊕ J a // ¬p.2.isLeft=true} => indexedCode ea (sumEquiv e e') p.val)
    Subtype.val (fun _ => rfl)
  let a := view.then (indexedFirst (sumEquiv e e'))
  let i := view.then (indexedIndex (sumEquiv e e'))
  (a.both (i.nsub (a.then rn))).changeOutput (indexedCode ea e') (sumRight e e') (by
    intro p
    change prodCode ea natCode (p.val.1,(sumEquiv e e' p.val.1 p.val.2).val-n p.val.1) =
      prodCode ea natCode ((sumRight e e' p).1,(e' (sumRight e e' p).1 (sumRight e e' p).2).val)
    rw [sumRight_index]
    rfl)

def Realizes.not {P : α → Prop} [DecidablePred P]
    (r : Realizes ea boolCode (fun a => decide (P a))) :
    Realizes ea boolCode (fun a => decide (¬ P a)) :=
  (r.ite (constant ea boolCode false) (constant ea boolCode true)).congr (by intro a;simp)

def Realizes.and {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) :
    Realizes ea boolCode (fun a => decide (P a ∧ Q a)) :=
  (r.ite s (constant ea boolCode false)).congr (by intro a;simp)
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil parameters. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

structure Params where
  graph : Graph
  s : ℚ
  κ : ℚ
  t : ℚ
  q : ℚ
  ε : ℚ
  u : Fin graph.m → ℚ

def Params.pencil (p : Params) := continuationPencil p.graph.G p.s p.κ p.t p.q p.ε p.u
abbrev paramsDataCode := prodCode graphCode (prodCode vectorCode vectorCode)
def Params.data (p : Params) := (p.graph,([p.s,p.κ,p.t,p.q,p.ε],List.ofFn p.u))
def paramsCode (p : Params) : Word := paramsDataCode p.data
abbrev paramsView : Realizes paramsCode paramsDataCode Params.data :=
  (identity paramsDataCode).reindex paramsCode Params.data (fun _ => rfl)

abbrev paramsGraph : Realizes paramsCode graphCode Params.graph := paramsView.then (first graphCode (prodCode vectorCode vectorCode))

abbrev paramsTail := paramsView.then (second graphCode (prodCode vectorCode vectorCode))
abbrev paramsFields := paramsTail.then (first vectorCode vectorCode)
abbrev paramsU := paramsTail.then (second vectorCode vectorCode)
abbrev paramsM : Realizes paramsCode natCode (fun p => p.graph.m) := paramsGraph.then numEdges

structure Point where
  p : Params
  v : Fin (dimension p.graph.n p.graph.m) → ℚ

def Point.data (a : Point) := (a.p,List.ofFn a.v)
def pointCode (a : Point) : Word := prodCode paramsCode vectorCode a.data
abbrev pointView : Realizes pointCode (prodCode paramsCode vectorCode) Point.data :=
  (identity (prodCode paramsCode vectorCode)).reindex pointCode Point.data (fun _ => rfl)

abbrev pointParams : Realizes pointCode paramsCode Point.p := pointView.then (first paramsCode vectorCode)

abbrev pointVector := pointView.then (second paramsCode vectorCode)
abbrev pointGraph : Realizes pointCode graphCode (fun a => a.p.graph) := pointParams.then paramsGraph
abbrev pointM : Realizes pointCode natCode (fun a => a.p.graph.m) := pointParams.then paramsM
abbrev pointU := pointParams.then paramsU

def parsePoint (a : Params×List ℚ) : Point := ⟨a.1,fun i => a.2.getD i.val 0⟩
lemma parsePoint_ofFn (p : Params) (v : Fin (dimension p.graph.n p.graph.m) → ℚ) :
    parsePoint (p,List.ofFn v)=⟨p,v⟩ := by
  unfold parsePoint
  congr 1
  funext i
  exact getD_ofFn v i 0

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_PointPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine
variable {α β : Type*} {ea : α → Word} {eb : β → Word}
def Realizes.cons {f : α → β} {g : α → List β}
    (r : Realizes ea eb f) (s : Realizes ea (listCode eb) g) :
    Realizes ea (listCode eb) (fun a => f a :: g a) := (r.both s).then (consList eb)
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {a : α → Point}

def graphEdge (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val)) :
    Realizes ea GraphStack.edgeCode (fun b => ⟨(a b).p.graph,e b⟩) :=
  ((r.then pointGraph).both re).changeOutput GraphStack.edgeCode (fun b => ⟨(a b).p.graph,e b⟩)
    (fun _ => rfl)

abbrev vEquiv (a : Point) := Equiv.refl (Fin a.p.graph.n)
abbrev eEquiv (a : Point) := Equiv.refl (Fin a.p.graph.m)
abbrev pairEquiv := prodEquiv vEquiv vEquiv
abbrev tripleEquiv := prodEquiv vEquiv pairEquiv
abbrev tripleCode := indexedCode pointCode tripleEquiv
abbrev triplePoint := indexedFirst (ea:=pointCode) tripleEquiv

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_BlockAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Block assembly. -/

section

namespace CurrentKS.Realization
open CleanRoutine Matrix KS.W23

abbrev BlocksData := ℕ × (List MatrixData × List ℚ)
abbrev blocksCode := prodCode natCode (prodCode (listCode matrixCode) vectorCode)
def stitchEntry (p : (BlocksData×ℕ)×ℕ) : ℚ :=
  let k := p.1.1.2.1.length
  let cut := p.1.1.1*k
  if p.1.2 < cut then
    if p.2 < cut then
      if p.1.2%k=p.2%k then
        (((p.1.1.2.1.getD (p.1.2%k) []).getD (p.1.2/k) []).getD (p.2/k) 0)
      else 0
    else 0
  else if p.1.2=p.2 then p.1.1.2.2.getD (p.1.2-cut) 0 else 0

def stitchData (a : BlocksData) : MatrixData :=
  (List.range (a.1*a.2.1.length+a.2.2.length)).map (fun i =>
    (List.range (a.1*a.2.1.length+a.2.2.length)).map (fun j => stitchEntry ((a,i),j)))

abbrev stitchCode := prodCode (prodCode blocksCode natCode) natCode
abbrev stFirst := first (prodCode blocksCode natCode) natCode
abbrev stBlocks := stFirst.then (first blocksCode natCode)
abbrev stI := stFirst.then (second blocksCode natCode)
abbrev stJ := second (prodCode blocksCode natCode) natCode
abbrev stN := stBlocks.then (first natCode (prodCode (listCode matrixCode) vectorCode))
abbrev stTail := stBlocks.then (second natCode (prodCode (listCode matrixCode) vectorCode))
abbrev stMatrices := stTail.then (first (listCode matrixCode) vectorCode)
abbrev stScalars := stTail.then (second (listCode matrixCode) vectorCode)
def stK := stMatrices.then (lengthList matrixCode)
def stCut := stN.nmul stK

variable {n k l : ℕ}
lemma stitch_top (B : Fin k → Matrix (Fin n) (Fin n) ℚ) (D : Fin l → ℚ)
    (i j : Fin n) (b c : Fin k) :
    stitchEntry (((n,(List.ofFn (fun b => matrixData (B b)),List.ofFn D)),b.val+k*i.val),c.val+k*j.val)=
      if b=c then B b i j else 0 := by
  have hi := (finProdFinEquiv (i,b)).isLt
  have hj := (finProdFinEquiv (j,c)).isLt
  change b.val+k*i.val<n*k at hi
  change c.val+k*j.val<n*k at hj
  have hk : 0 < k := by omega
  simp only [stitchEntry,List.length_ofFn,ite_eq_left hi,ite_eq_left hj]
  simp only [Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt b.isLt,
    Nat.mod_eq_of_lt c.isLt,Nat.add_mul_div_left _ _ hk,Nat.div_eq_of_lt b.isLt,
    Nat.div_eq_of_lt c.isLt,Nat.zero_add]
  rw [getD_ofFn,matrixData,getD_ofFn,getD_ofFn]
  simp [Fin.ext_iff]

lemma stitch_top_bottom (B : Fin k → Matrix (Fin n) (Fin n) ℚ) (D : Fin l → ℚ)
    (i : Fin n) (b : Fin k) (s : Fin l) :
    stitchEntry (((n,(List.ofFn (fun b => matrixData (B b)),List.ofFn D)),b.val+k*i.val),n*k+s.val)=0 := by
  have hi := (finProdFinEquiv (i,b)).isLt
  change b.val+k*i.val<n*k at hi
  simp [stitchEntry,hi]

lemma stitch_bottom_top (B : Fin k → Matrix (Fin n) (Fin n) ℚ) (D : Fin l → ℚ)
    (s : Fin l) (j : Fin n) (c : Fin k) :
    stitchEntry (((n,(List.ofFn (fun b => matrixData (B b)),List.ofFn D)),n*k+s.val),c.val+k*j.val)=0 := by
  have hj := (finProdFinEquiv (j,c)).isLt
  change c.val+k*j.val<n*k at hj
  have hne : n*k+s.val≠c.val+k*j.val := by omega
  simp [stitchEntry,hne]

lemma stitch_bottom (B : Fin k → Matrix (Fin n) (Fin n) ℚ) (D : Fin l → ℚ)
    (s t : Fin l) :
    stitchEntry (((n,(List.ofFn (fun b => matrixData (B b)),List.ofFn D)),n*k+s.val),n*k+t.val)=
      if s=t then D s else 0 := by
  have hnot : ¬ n*k+s.val<n*k := by omega
  simp only [stitchEntry,List.length_ofFn,ite_eq_right hnot,
    Nat.add_left_cancel_iff,Nat.add_sub_cancel_left]
  rw [getD_ofFn]
  simp [Fin.ext_iff]

lemma stitch_data {U S : Type*} [DecidableEq U] [DecidableEq S]
    (eb : U ≃ Fin k) (es : S ≃ Fin l)
    (B : U → Matrix (Fin n) (Fin n) ℚ) (D : S → ℚ) :
    stitchData (n,(List.ofFn (fun i => matrixData (B (eb.symm i))),List.ofFn (fun i => D (es.symm i))))=
      matrixData ((Matrix.fromBlocks (Matrix.blockDiagonal B) 0 0 (Matrix.diagonal D)).submatrix
        (blockRowEquiv eb es).symm (blockRowEquiv eb es).symm) := by
  simp only [stitchData,List.length_ofFn,range_map_fin]
  conv_rhs => unfold matrixData
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  obtain ⟨i,rfl⟩ := (blockRowEquiv eb es).surjective i
  obtain ⟨j,rfl⟩ := (blockRowEquiv eb es).surjective j
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply]
  rcases i with ⟨i,b⟩ | s <;> rcases j with ⟨j,c⟩ | t
  · simp only [blockRowEquiv_left]
    rw [stitch_top]
    simp [Matrix.blockDiagonal,eb.injective.eq_iff]
  · simp only [blockRowEquiv_left,blockRowEquiv_right]
    rw [stitch_top_bottom]
    rfl
  · simp only [blockRowEquiv_left,blockRowEquiv_right]
    rw [stitch_bottom_top]
    rfl
  · simp only [blockRowEquiv_right]
    rw [stitch_bottom]
    simp [Matrix.diagonal_apply,es.injective.eq_iff]
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_RationalAffineEval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational affine eval. -/

section


namespace AlgorithmicThinTrees.RationalForms
open Matrix Finset
open scoped BigOperators
lemma pencil_eval {d N : ℕ} (A : Matrix (Fin N) (Fin N) (Affine d)) (hA : A.IsSymm)
    (v : Fin d → ℚ) : (pencil A hA).eval v=A.map (Affine.rat v) := by
  ext i j
  simp only [CurrentKS.RationalSDP.Pencil.eval,pencil,Matrix.map_apply,Affine.rat]
  erw [Matrix.add_apply,Matrix.sum_apply]
  congr 1
  apply sum_congr rfl
  intro k _
  change v k * (A i j).2 k = (A i j).2 k * v k
  ring
end AlgorithmicThinTrees.RationalForms
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_MatrixConstraintRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix constraint realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

lemma rat_matrixForm {n m : ℕ} (v : Fin (dimension n m) → ℚ) (i j : Fin n) :
    Affine.rat v (matrixForm i j)=qresponse (rawMatrix v) i j := by
  simp only [matrixForm,Affine.rat_sum,Affine.rat_smul,Affine.rat_add,Affine.rat_coord]
  simp only [qresponse,Matrix.mul_apply,Matrix.smul_apply,Matrix.add_apply,
    Matrix.transpose_apply,rawMatrix,smul_eq_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

namespace Stack

def weightedTriangle (a : Point) (t : Triple a.p.graph.n) : Matrix (Fin a.p.graph.n) (Fin a.p.graph.n) ℚ :=
  if t.1≠t.2.1 ∧ t.2.1≠t.2.2 ∧ t.1≠t.2.2 then a.v (mulIndex t) • triangleAt t else 0

lemma weightedTriangle_sum (a : Point) :
    ∑t,weightedTriangle a t = ∑t : DistinctTriple a.p.graph.n,a.v (mulIndex t.val) • qtriangle t := by
  classical
  let P (t : Triple a.p.graph.n) := t.1≠t.2.1 ∧ t.2.1≠t.2.2 ∧ t.1≠t.2.2
  rw [←Fintype.sum_subtype_add_sum_subtype P (weightedTriangle a)]
  have hz : ∑ t : {t // ¬ P t}, weightedTriangle a t.val = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    exact ite_eq_right t.property
  rw [hz,add_zero]
  apply Finset.sum_congr rfl
  intro t _
  unfold weightedTriangle
  rw [ite_eq_left t.property]
  rfl

abbrev matrixBlockEquiv := sumEquiv (fun _ : Point => Equiv.refl (Fin 2)) eEquiv

end Stack
end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_ScalarConstraintRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar constraint realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

def scalarValue (a : Point) (b : ScalarBlock a.p.graph.n a.p.graph.m) : ℚ :=
  Affine.rat a.v (scalarForms a.p.graph.G a.p.κ a.p.t a.p.q a.p.ε a.p.u b)

abbrev edgeScalarEquiv := prodEquiv (fun _ : Point => Equiv.refl (Fin 7)) eEquiv
abbrev edgeScalarCode := indexedCode pointCode edgeScalarEquiv
abbrev esPoint := indexedFirst (ea:=pointCode) edgeScalarEquiv

abbrev rootEdgeEquiv := prodEquiv vEquiv eEquiv
abbrev rePoint := indexedFirst (ea:=pointCode) rootEdgeEquiv

abbrev flowScalarEquiv := prodEquiv (fun _ : Point => Equiv.refl (Fin 3)) rootEdgeEquiv
abbrev flowScalarCode := indexedCode pointCode flowScalarEquiv

abbrev budgetCode := indexedCode pointCode pairEquiv
abbrev bsPoint := indexedFirst (ea:=pointCode) pairEquiv
abbrev budgetEdgeCode := finFamilyCode budgetCode (fun a => a.1.p.graph.m)
abbrev beBudget : Realizes budgetEdgeCode budgetCode (fun a => a.1) := familyFirst
abbrev beE : Realizes budgetEdgeCode natCode (fun a => a.2.val) := familyIndex
abbrev bePoint := beBudget.then bsPoint
abbrev beGraphEdge := graphEdge bePoint (fun a => a.2) beE

abbrev xePoint : Realizes (finFamilyCode pointCode (fun a => a.p.graph.m)) pointCode (fun a => a.1) := familyFirst
abbrev xeE : Realizes (finFamilyCode pointCode (fun a => a.p.graph.m)) natCode (fun a => a.2.val) := familyIndex

abbrev scalarEquiv := sumEquiv tripleEquiv (sumEquiv edgeScalarEquiv
  (sumEquiv flowScalarEquiv (sumEquiv pairEquiv (fun _ : Point => Equiv.refl (Fin 1)))))
abbrev scalarCode := indexedCode pointCode scalarEquiv

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree RationalForms
open AlgorithmicThinTrees.GraphStack

abbrev matrixCount := (constant pointCode natCode 2).nadd pointM

lemma rowIndex_blocks (a : Point) :
    blockRowEquiv (n:=a.p.graph.n) (matrixBlockEquiv a) (scalarEquiv a)=
      rowIndex a.p.graph.n a.p.graph.m := by
  apply Equiv.ext
  intro i
  rcases i with ⟨i,b|e⟩ | (t | (e | (f | (v | u)))) <;> rfl

lemma affineMatrix_rat (a : Point) :
    (affineMatrix a.p.graph.G a.p.s a.p.κ a.p.t a.p.q a.p.ε a.p.u).map (Affine.rat a.v)=
      (Matrix.fromBlocks
        (Matrix.blockDiagonal (fun b => (matrixBlocks a.p.graph.G a.p.s a.p.u b).map (Affine.rat a.v)))
        0 0 (Matrix.diagonal (scalarValue a))).submatrix
          (rowIndex a.p.graph.n a.p.graph.m).symm (rowIndex a.p.graph.n a.p.graph.m).symm := by
  ext i j
  obtain ⟨i,rfl⟩ := (rowIndex a.p.graph.n a.p.graph.m).surjective i
  obtain ⟨j,rfl⟩ := (rowIndex a.p.graph.n a.p.graph.m).surjective j
  simp only [affineMatrix,Matrix.map_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  rcases i with ⟨i,b⟩ | s <;> rcases j with ⟨j,c⟩ | t
  · simp only [Matrix.fromBlocks_apply₁₁,Matrix.blockDiagonal,Matrix.of_apply]
    split_ifs <;> simp
  · simp
  · simp
  · by_cases h : s=t <;> simp [scalarValue,h]

lemma pencilEval_data (p : Params) (v : Fin (dimension p.graph.n p.graph.m) → ℚ) :
    matrixData ((affineMatrix (parsePoint (p,List.ofFn v)).p.graph.G
      (parsePoint (p,List.ofFn v)).p.s (parsePoint (p,List.ofFn v)).p.κ
      (parsePoint (p,List.ofFn v)).p.t (parsePoint (p,List.ofFn v)).p.q
      (parsePoint (p,List.ofFn v)).p.ε (parsePoint (p,List.ofFn v)).p.u).map
        (Affine.rat (parsePoint (p,List.ofFn v)).v)) = matrixData (p.pencil.eval v) := by
  rw [parsePoint_ofFn]
  unfold Params.pencil continuationPencil
  rw [pencil_eval]

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_SearchRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Search realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

def Params.searchState (p : Params) : SearchState :=
  ⟨dimension p.graph.n p.graph.m,order p.graph.n p.graph.m,p.pencil,
    radiusQ p.graph.n p.graph.m,boundQ p.graph.n p.graph.m,0⟩

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

structure Loop where
  graph : Graph
  count : ℕ
  state : State graph.n graph.m

abbrev loopTailCode := prodCode ratCode (prodCode ratCode (prodCode matrixCode vectorCode))
abbrev loopDataCode := prodCode graphCode (prodCode natCode loopTailCode)
def Loop.data (a : Loop) :=
  (a.graph,(a.count,(a.state.scale,(a.state.quality,(matrixData a.state.matrix,List.ofFn a.state.capacity)))))
def loopCode (a : Loop) : Word := loopDataCode a.data
abbrev loopView : Realizes loopCode loopDataCode Loop.data :=
  (identity loopDataCode).reindex loopCode Loop.data (fun _ => rfl)

abbrev loopGraph : Realizes loopCode graphCode Loop.graph :=
  loopView.then (first graphCode (prodCode natCode loopTailCode))

abbrev loopRest := loopView.then (second graphCode (prodCode natCode loopTailCode))
abbrev loopCount : Realizes loopCode natCode Loop.count := loopRest.then (first natCode loopTailCode)

abbrev loopState := loopRest.then (second natCode loopTailCode)
abbrev loopScale : Realizes loopCode ratCode (fun a => a.state.scale) :=
  loopState.then (first ratCode (prodCode ratCode (prodCode matrixCode vectorCode)))

abbrev loopTail := loopState.then (second ratCode (prodCode ratCode (prodCode matrixCode vectorCode)))
abbrev loopQuality : Realizes loopCode ratCode (fun a => a.state.quality) :=
  loopTail.then (first ratCode (prodCode matrixCode vectorCode))

abbrev loopArrays := loopTail.then (second ratCode (prodCode matrixCode vectorCode))
abbrev loopCapacity := loopArrays.then (second matrixCode vectorCode)
abbrev loopM := loopGraph.then numEdges

def Loop.params (a : Loop) : Params :=
  ⟨a.graph,a.state.scale,baselineQ a.graph.m,stepQ a.graph.m,
    target a.graph.m a.count a.state.quality (gain a.count),errorQ a.graph.n a.graph.m,a.state.capacity⟩

def Loop.vector (a : Loop) := search a.graph.G a.state.scale
  (target a.graph.m a.count a.state.quality (gain a.count)) a.state.capacity

abbrev LoopEdge := Σ a : Loop, Fin a.graph.m
abbrev loopEdgeCode := finFamilyCode loopCode (fun a : Loop => a.graph.m)
abbrev edgeLoop : Realizes loopEdgeCode loopCode (fun x : LoopEdge => x.1) := familyFirst
abbrev edgeNumber : Realizes loopEdgeCode natCode (fun x : LoopEdge => x.2.val) := familyIndex

def Loop.updated (a : Loop) : Loop :=
  ⟨a.graph,a.count,update a.graph.G a.count (gain a.count) a.state⟩

def Loop.next (a : Loop) : Loop := ⟨a.graph,a.count,advance a.graph.G a.count a.state⟩

abbrev extractionInputCode := prodCode graphCode natCode
abbrev extractionGraph := first graphCode natCode
abbrev extractionCount := second graphCode natCode

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_GraphicNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graphic normalization. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
variable {d m q : ℕ}

def integerColumns (G : MultiGraph (d+1) m) (B : Finset (Fin m)) : Fin m → Fin d → ℤ :=
  fun e i => if e ∈ B then (if G.left e=i.succ then 1 else 0)-(if G.right e=i.succ then 1 else 0) else 0

def graphColumns (G : MultiGraph (d+1) m) (B : Finset (Fin m)) : Fin m → Fin d → ℚ :=
  fun e i => (integerColumns G B e i:ℚ)

end AlgorithmicThinTrees.Normalization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_GraphicHalf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graphic half. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {n d m : ℕ}

def fullColumns (G : MultiGraph n m) (B : Finset (Fin m)) : Fin m → Fin n → ℚ :=
  fun e => if e ∈ B then qdiff (G.left e) (G.right e) else 0

def scaledColumns (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ) :
    Fin m → Fin d → ℚ := fun e => s e • graphColumns G B e

def scaledForm (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (s : Fin m → ℚ) :=
  covariance (graphColumns G B) (weights s)

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparsification realization. -/

section

namespace AlgorithmicThinTrees.GraphicHalf.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree Finset
open MetricTests MetricTests.RationalStep Normalization GraphStack
open MetricTests.RationalStep.Stack

structure Problem where
  d : ℕ
  m : ℕ
  r : ℕ
  G : MultiGraph (d+1) m

def Problem.graph (p : Problem) : Graph := ⟨p.d+1,p.m,p.G⟩
def problemCode (p : Problem) : Word := extractionInputCode (p.graph,p.r)
abbrev problemView : Realizes problemCode extractionInputCode (fun p => (p.graph,p.r)) :=
  (identity extractionInputCode).reindex problemCode (fun p => (p.graph,p.r)) (fun _ => rfl)
abbrev Problem.state (p : Problem) := extractState p.G p.r
abbrev Problem.active (p : Problem) := p.state.active
abbrev Problem.q (p : Problem) := p.state.packingTarget
abbrev Problem.scales (p : Problem) := normalizedScales p.q p.r (graphColumns p.G p.active)

abbrev Edge := Σ p : Problem, Fin p.m
abbrev edgeCode := finFamilyCode problemCode Problem.m
abbrev context : Realizes edgeCode problemCode (fun p : Edge => p.1) := familyFirst

abbrev Coordinate := Σ e : Edge, Fin e.1.d
abbrev coordCode := finFamilyCode edgeCode (fun e : Edge => e.1.d)
abbrev coordEdge : Realizes coordCode edgeCode (fun x : Coordinate => x.1) := familyFirst
abbrev coordIndex : Realizes coordCode natCode (fun x : Coordinate => x.2.val) := familyIndex

def Problem.normalization (p : Problem) : Normalization.Stack.Params :=
  ⟨p.d,p.m,p.q,0,graphColumns p.G p.active⟩

def Problem.forms (p : Problem) : Signing.Stack.FormPair :=
  ⟨⟨p.d+1,positiveForm p.state.matrix⟩,⟨p.d,scaledForm p.G p.active p.scales⟩,
    p.m,fullColumns p.G p.active,scaledColumns p.G p.active p.scales⟩

abbrev MaskInput := Problem × List Bool
abbrev MaskEdge := Σ p : MaskInput, Fin p.1.m

end AlgorithmicThinTrees.GraphicHalf.Stack
end

end OAI
end


