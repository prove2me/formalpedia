-- Prove2me | Definitions.Def_OAIQ241TT009
-- name    : OAIQ241TT009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:19.943701+00:00
-- url     : https://prove2.me/theorems/b05956aa-cadb-4b40-bdcc-8612b8bbd865
-- title:
--   Definitions bundle OAIQ241TT009 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 273 declarations of OpenAI's Lean: 193 definitions, 2 inductive types or structures, 16 instances and 62 theorems. The definitions and types are `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.edgeGraphInput`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.maskCode`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.maskContext`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.maskEdgeCode`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.maskEdgeInput`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.maskIndex`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.maskProblem`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.maskSigns`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.number`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.problemCount`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.problemD`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.problemGraph`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.problemM`, `OAI.AlgorithmicThinTrees.GraphicHalf.Stack.problemN`, `OAI.AlgorithmicThinTrees.GraphicHalf.halfEdges`, `OAI.AlgorithmicThinTrees.GraphicHalf.sparsify`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.arcLeft`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.arcRight`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.leftReached`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.reachM`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.reachN`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.reached`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.rightReached`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.selected`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.subgraphM`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.subgraphN`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.whole`, `OAI.AlgorithmicThinTrees.InputStack.bEdges`, `OAI.AlgorithmicThinTrees.InputStack.bEndpointBinary`, `OAI.AlgorithmicThinTrees.InputStack.bKBinary`, `OAI.AlgorithmicThinTrees.InputStack.bNBinary`, `OAI.AlgorithmicThinTrees.InputStack.bOutput`, `OAI.AlgorithmicThinTrees.InputStack.bPBinary`, `OAI.AlgorithmicThinTrees.InputStack.bProblem`, `OAI.AlgorithmicThinTrees.InputStack.bRecordBinary`, `OAI.AlgorithmicThinTrees.InputStack.bView`, `OAI.AlgorithmicThinTrees.InputStack.eEdges`, `OAI.AlgorithmicThinTrees.InputStack.eEndpointBinary`, `OAI.AlgorithmicThinTrees.InputStack.eKBinary`, `OAI.AlgorithmicThinTrees.InputStack.eMBinary` and 155 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Complexity_PolynomialOptimize`, `MatrixSigning_Complexity_PolynomialRoots`, `MatrixSigning_Complexity_PolynomialRoundedStep`, `MatrixSigning_Complexity_PolynomialSearch`, `MatrixSigning_Encoding_FramedArrayPrefix`, `MatrixSigning_Encoding_FramedArrayReplacement`, `MatrixSigning_Encoding_ReusableArrayLookup`, `MatrixSigning_Encoding_WireProgramPrimitives`, `MatrixSigning_Encoding_ZeroArrayConstructor`, `MatrixSigning_Machines_TerminalVectorReplace`, `MatrixSigning_Machines_UnaryLengthMachine`, `MatrixSigning_Matrices_PivotControllerLoop`, `MatrixSigning_Optimization_TerminalWitnessMachine`, `MatrixSigning_Optimization_TerminalWitnessTapes`, `MatrixSigning_Realization_CoordinateRealization`, `MatrixSigning_Realization_FaceQueryRealization`, `MatrixSigning_Realization_FaceRunRealization`, `MatrixSigning_Realization_LevelPencilRealization`, `MatrixSigning_Realization_ListRealization`, `MatrixSigning_Realization_OptimizeRealization`, `MatrixSigning_Realization_OriginalFieldsRealization`, `MatrixSigning_Realization_OriginalSignRealization`, `MatrixSigning_Realization_PotentialRealization`, `MatrixSigning_Realization_RatFieldsRealization`, `MatrixSigning_Realization_RoundedStepRealization`, `MatrixSigning_Realization_ScheduleRealization`, `MatrixSigning_Realization_SearchRealization`, `MatrixSigning_Realization_SelectionRealization`, `MatrixSigning_Realization_StoredPSDRealization`, `MatrixSigning_Realization_ValueDataRealization`, `MatrixSigning_Realization_ValueEvalRealization`, `MatrixSigning_Realization_ValueObjectiveRealization`, `MatrixSigning_Realization_VarianceRealization`, `MatrixSigning_Realization_VectorRealization`, `MatrixSigning_Realization_WitnessRealization`, `ThinTrees_Arithmetic_ScalarRealization`, `ThinTrees_Continuation_BitBound`, `ThinTrees_Continuation_Encoding`, `ThinTrees_Continuation_FiniteContinuation`, `ThinTrees_Continuation_Iteration`, `ThinTrees_Continuation_Realization`, `ThinTrees_Encoding_GreedyRealization`, `ThinTrees_Encoding_InputArrays`, `ThinTrees_Encoding_InputDispatch`, `ThinTrees_Encoding_InputExpansion`, `ThinTrees_Encoding_InputOutput`, `ThinTrees_Encoding_SelectionRealization`, `ThinTrees_Normalization_Realization`, `ThinTrees_Pencil_Parameters`, `ThinTrees_RationalMatrix_InverseRealization`, `ThinTrees_RationalMatrix_MatrixRealization`, `ThinTrees_RationalMatrix_SchurHistory`, `ThinTrees_Signing_GramRealization`, `ThinTrees_Signing_Realization`, `ThinTrees_Sparsification_GraphicHalf`, `ThinTrees_Sparsification_IterationRealization`, `ThinTrees_Sparsification_RationalIteration`, `ThinTrees_Sparsification_Realization`, `ThinTrees_Sparsification_Step`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`; the bundles `OAIQ241TT004`, `OAIQ241TT005` and `OAIQ241TT006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ241TT010` and `OAIQ241TT011`; the statements `OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds`, `OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response` and `OAI.AlgorithmicThinTrees.MetricTests.finite_continuation_inner_cube`; the proofs of `OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds`, `OAI.AlgorithmicThinTrees.GraphicHalf.sparsification_correct`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.uniform_search_response`, `OAI.AlgorithmicThinTrees.MetricTests.finite_continuation_inner_cube`, `OAI.CurrentKS.Realization.isPoly_orbitScore` and `OAI.CurrentKS.Realization.isPoly_orbitStencil`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT004
import Definitions.Def_OAIQ241TT005
import Definitions.Def_OAIQ241TT006

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ListRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ : Type*}

def appendList (ea : α → Word) :
    Realizes (prodCode (listCode ea) (listCode ea)) (listCode ea) (fun p => p.1++p.2) where
  cost := fun p => 5*(listCode ea p.1).length+4
  routine := by
    have h := WordOperations.appending.reindex (fun p : List α×List α => (listCode ea p.1,listCode ea p.2))
    refine { scratch := h.scratch,program := h.program,spec := ?_ }
    intro p
    have hp := h.spec p
    simp only [listCode_append] at hp ⊢
    exact hp

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_WireProgramPrimitives
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W15.WireProgram
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem copy_spec {k : Nat} (a b c : Fin k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (before : Fin k → List Bool) (hb : before b = []) (hc : before c = []) :
    RunSpec (copyProgram a b c hab hac hbc) before
      (Function.update before b (before a)) (2 * (before a).length + 2) := by
  intro bits hlen
  exact KS.W01.FixedCopy.run_copy_restore (ports3 a b c hab hac hbc) before
    (before a) bits rfl hb hc hlen

theorem stay_spec {k : Nat} (port : Fin k) (before : Fin k → List Bool) :
    RunSpec (stayProgram port) before before 1 := by
  intro bits hlen
  rcases bits with _ | ⟨coin,tail⟩
  · simp at hlen
  have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
  subst tail
  change (compile (0 : Fin 1) port port (fun _ _ _ => Instruction.halt k 1)).step
    (⟨some (0 : Fin 1),before⟩ : Config k 1) coin = _
  erw [step_compile]
  simp [Instruction.halt, Instruction.action, KS.W29.StackAction.apply]
  rfl

end KS.W15.WireProgram

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VectorRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α β γ : Type*}

def joinList (ea : α → Word) : Realizes (listCode (listCode ea)) (listCode ea) List.flatten :=
  (((constant (listCode (listCode ea)) (listCode ea) []).both
    (identity (listCode (listCode ea)))).then (appendList ea).fold).congr (by
      intro lists
      simpa using List.foldl_append_eq_append (l := lists) (f := id) (l' := ([] : List α)))

def Realizes.filterCtx {ec : γ → Word} {ea : α → Word} {p : γ×α → Bool}
    (r : Realizes (prodCode ec ea) boolCode p) :
    Realizes (prodCode ec (listCode ea)) (listCode ea)
      (fun input => input.2.filter (fun value => p (input.1,value))) :=
  let one := r.ite ((second ec ea).then (singleton ea))
    (constant (prodCode ec ea) (listCode ea) [])
  (one.mapCtx.then (joinList ea)).congr (by
    intro input
    induction input.2 with
    | nil => rfl
    | cons value values inductionHypothesis =>
      simp only [List.map_cons,List.flatten_cons]
      cases predicateValue : p (input.1,value) <;> simp_all)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CoordinateRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def squareTabulate {f : (MatrixData×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode f) :
    Realizes (prodCode natCode matrixCode) matrixCode (squareTabData f) :=
  let n := first natCode matrixCode
  let M := second natCode matrixCode
  ((M.both n).both n).then r.matrixTabulate

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_LevelPencilRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α : Type*}

def blockScalar : Realizes (prodCode matrixCode ratCode) matrixCode blockScalarData :=
  let M := first matrixCode ratCode
  let q := second matrixCode ratCode
  let top := M.then (((identity vectorCode).both (constant vectorCode vectorCode [0])).then
    (appendList ratCode)).map
  let zeros := ((constant (prodCode matrixCode ratCode) ratCode 0).both
    (M.then (lengthList vectorCode))).then (replicateList ratCode)
  let bottom := (zeros.both (q.then (singletonList ratCode))).then (appendList ratCode)
  (top.both (bottom.then (singletonList vectorCode))).then (appendList vectorCode)

abbrev levelInputCode := prodCode pencilCode (prodCode vectorCode ratCode)
def withLevelData (p : PencilData×(List ℚ×ℚ)) : PencilData :=
  (blockScalarData (p.1.1,p.2.2),
    zipDefault (fun z : MatrixData×ℚ => blockScalarData (z.1,-z.2)) [] 0 (p.1.2,p.2.1))

lemma withLevel_data {n m : ℕ} (B : RationalSDP.Pencil n m) (f : Fin n → ℚ) (q : ℚ) :
    withLevelData (pencilData B,(List.ofFn f,q))=pencilData (B.withLevel f q) := by
  unfold withLevelData pencilData
  rw [zipDefault_ofFn,blockScalar_data]
  simp only [blockScalar_data,RationalSDP.Pencil.withLevel]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueDataRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def realDimension : Realizes natCode natCode (fun d => d+d) :=
  ((identity natCode).both (identity natCode)).then natAdd
def valueDimension : Realizes natCode natCode RationalSDP.valueDimension :=
  let sq := ((identity natCode).both (identity natCode)).then natMul
  (((sq.both sq).then natAdd).then natSucc).congr (by intro d;simp [RationalSDP.valueDimension,Nat.add_comm])

def coordinateIndexRealizes (second : Bool) :
    Realizes (prodCode (prodCode natCode natCode) natCode) natCode (coordinateIndex second) :=
  let p := first (prodCode natCode natCode) natCode
  let d := p.then (first natCode natCode)
  let i := p.then (Realization.second natCode natCode)
  let j := Realization.second (prodCode natCode natCode) natCode
  let offset := (constant _ boolCode second).ite ((d.both d).then natMul) (constant _ natCode 0)
  let start := ((constant _ natCode 1).both offset).then natAdd
  let row := (d.both i).then natMul
  (start.both ((j.both row).then natAdd)).then natAdd

def coordinateEntry (second : Bool) :
    Realizes (prodCode (prodCode matrixVarCode natCode) natCode) ratCode
      (fun p => p.1.1.2.getD (coordinateIndex second ((p.1.1.1,p.1.2),p.2)) 0) :=
  let ctx := first (prodCode matrixVarCode natCode) natCode
  let data := ctx.then (first matrixVarCode natCode)
  let d := data.then (first natCode vectorCode)
  let y := data.then (Realization.second natCode vectorCode)
  let i := ctx.then (Realization.second matrixVarCode natCode)
  let j := Realization.second (prodCode matrixVarCode natCode) natCode
  let idx := ((d.both i).both j).then (coordinateIndexRealizes second)
  (idx.both y).then (getD ratCode 0)

def coordinates (second : Bool) : Realizes matrixVarCode matrixCode (coordinateData second) :=
  let d := first natCode vectorCode
  (((identity matrixVarCode).both d).both d).then (coordinateEntry second).matrixTabulate

def sandwichData (p : MatrixData×MatrixData) : MatrixData :=
  matrixMulData (matrixMulData (p.1,p.2),p.1)
lemma sandwich_data {n : ℕ} (A Z : Matrix (Fin n) (Fin n) ℚ) :
    sandwichData (matrixData A,matrixData Z)=matrixData (A*Z*A) := by
  rw [sandwichData,matrixMul_data,matrixMul_data]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_UnaryLengthMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W19.FixedRun.project_pack _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W28.UnaryLength
open KS.W29

theorem run_length (xs ys zs bits : List Bool) (hlen : bits.length = xs.length+1) :
    machine.run (cfg (some 0) xs ys zs) bits =
      cfg none [] (List.replicate xs.length true ++ ys) zs := by
  induction xs generalizing ys bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin bits =>
          erw [BinaryMachine.run.eq_2, step_empty, BinaryMachine.run_halted _ _ rfl]
          rfl
  | cons a xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin bits =>
          have ht : bits.length = xs.length+1 := by simpa using Nat.succ.inj hlen
          erw [BinaryMachine.run.eq_2, step_cons, ih _ bits ht]
          simp only [List.length_cons, List.replicate_succ', List.append_assoc, List.singleton_append]
          rfl

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers registers_other)

theorem length_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Fin k → List Bool)
    (xs ys zs : List Bool) :
    RunSpec (program ports) (registers ports spare xs ys zs)
      (registers ports spare [] (List.replicate xs.length true ++ ys) zs) (xs.length+1) := by
  intro bits hbits
  change (lift3 machine ports).run ⟨some (0 : Fin 1), registers ports spare xs ys zs⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports
        (⟨some 0, registers ports spare xs ys zs⟩ : KS.W01.FixedStack.Config k 1) = cfg (some 0) xs ys zs := by
      change KS.W29.Config.mk (some (0 : Fin 1)) _ = KS.W29.Config.mk (some (0 : Fin 1)) _
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 1)))
      funext j
      fin_cases j <;> simp [registers, ports.injective.eq_iff]
    erw [hp, run_length xs ys zs bits hbits]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    fin_cases j <;> simp
  · intro j hj
    change registers ports spare [] (List.replicate xs.length true ++ ys) zs j =
      registers ports spare xs ys zs j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

end KS.W28.UnaryLength

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RatFieldsRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
attribute [-simp] _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open KS.W29.FixedSequential KS.W03.MachineCombinators

def unframeNat : Realizes KS.W01.encodeNat binaryNatCode id :=
  (first binaryNatCode (fun _ : Unit => ([] : Word))).reindex KS.W01.encodeNat
    (fun n => (n,())) (by intro n;simp [prodCode,PairRoutine.pair,KS.W01.encodeNat])

def wordLength : Realizes (id : Word → Word) natCode List.length where
  cost := fun w => 3*w.length+3
  routine := {
    scratch := 2
    program := compose (KS.W28.UnaryLength.program ⟨![0,1,2],by decide⟩)
      (CleanRoutine.transfer 1 2 0)
    spec := fun w => by
      have hd : RunSpec (KS.W28.UnaryLength.program (⟨![0,1,2],by decide⟩ : Fin 3 ↪ Fin 3))
          (io w) (PairRoutine.smallState [] (natCode w.length) []) (w.length+1) := by
        have h := KS.W28.UnaryLength.length_spec
          (⟨![0,1,2],by decide⟩ : Fin 3 ↪ Fin 3) (fun _ => []) w [] []
        convert h using 1 <;> first | (with_reducible_and_instances rfl) | (funext j <;> fin_cases j <;> simp [io,PairRoutine.smallState,natCode,KS.W28.FixedPositiveSerializer.registers])
      have h := hd.compose (PairRoutine.take_first (natCode w.length))
      convert h using 1 <;> (try rfl); simp only [natCode,List.length_replicate]; omega }

def binarySize : Realizes binaryNatCode natCode Nat.size :=
  (wordLength.reindex binaryNatCode binaryNatCode (fun _ => rfl)).congr
    KS.W01.natPayloadLength_eq_size

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoots
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize

local notation "X" => NaturalPolynomial.variable

instance poly_wordLength : PolyTime wordLength := ⟨⟨3*X+3,fun _ => le_rfl⟩⟩
instance poly_binarySize : PolyTime binarySize := by unfold binarySize;apply poly_congr
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ReusableArrayLookup
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W04.ReusableArrayLookup
open KS.W01.FixedStack
open KS.W29.FixedSequential
open KS.W03.MachineCombinators

theorem run_halted_of_length_ge (M : Machine) (c result : Config M.stackCount M.states)
    (fuel : Nat) (hresult : result.state = none)
    (hexact : ∀ bits : List Bool, bits.length = fuel → M.run c bits = result)
    (bits : List Bool) (hlen : fuel ≤ bits.length) : M.run c bits = result := by
  have ht : (bits.take fuel).length = fuel := by
    simp [List.length_take, Nat.min_eq_left hlen]
  conv_lhs => rw [← List.take_append_drop fuel bits]
  rw [Machine.run_append, hexact _ ht, Machine.run_halted M result hresult]

end KS.W04.ReusableArrayLookup

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayPrefix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack
open KS.W29 (StackAction)
open KS.W29.FixedSequential

theorem roundtrip_step (M : Machine) (c : Config M.stackCount M.states) (coin : Bool) :
    (ofMachine M).toMachine.step c coin = M.step c coin := by
  cases M
  rfl
theorem roundtrip_run (M : Machine) (c : Config M.stackCount M.states) (bits : List Bool) :
    (ofMachine M).toMachine.run c bits = M.run c bits := by
  cases M
  rfl
theorem transferProgram_step (c : Config 5 2) (coin : Bool) :
    transferProgram.toMachine.step c coin = transferMachine.step c coin := roundtrip_step transferMachine c coin
theorem transferProgram_run (c : Config 5 2) (bits : List Bool) :
    transferProgram.toMachine.run c bits = transferMachine.run c bits := roundtrip_run transferMachine c bits

theorem transfer_tag_false (xs rep pref tmp ix : List Bool) (coin : Bool) :
    transferMachine.step (config (some (0 : Fin 2)) (false :: xs) rep pref tmp ix) coin =
      config (some (1 : Fin 2)) xs rep (false :: pref) tmp ix := by
  unfold transferMachine config
  erw [step_compile]
  apply config_ext
  · simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode]
  · intro j
    fin_cases j <;> simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode,
      Instruction.action, StackAction.apply]

theorem transfer_tag_true (xs rep pref tmp ix : List Bool) (coin : Bool) :
    transferMachine.step (config (some (0 : Fin 2)) (true :: xs) rep pref tmp ix) coin =
      config none xs rep (true :: pref) tmp ix := by
  unfold transferMachine config
  erw [step_compile]
  apply config_ext
  · simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode]
    rfl
  · intro j
    fin_cases j <;> simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode,
      Instruction.action, StackAction.apply]

theorem transfer_data (bit : Bool) (xs rep pref tmp ix : List Bool) (coin : Bool) :
    transferMachine.step (config (some (1 : Fin 2)) (bit :: xs) rep pref tmp ix) coin =
      config (some (0 : Fin 2)) xs rep (bit :: pref) tmp ix := by
  unfold transferMachine config
  erw [step_compile]
  cases bit <;> apply config_ext
  all_goals
    first | (solve | simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode]) |
      (intro j; fin_cases j <;> simp [transferDispatch, observedHeads, «stacks», KS.W29.topCode,
        Instruction.action, StackAction.apply])

theorem run_two_of_steps (M : Machine) (c d e : Config M.stackCount M.states)
    (b₀ b₁ : Bool) (rest : List Bool) (h₀ : M.step c b₀ = d) (h₁ : M.step d b₁ = e) :
    M.run c (b₀ :: b₁ :: rest) = M.run e rest := by
  rw [Machine.run, h₀, Machine.run, h₁]

theorem transfer_frame (payload tail rep pref tmp ix bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    transferMachine.run (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) rep pref tmp ix) bits =
      config none tail rep ((KS.W01.frame payload).reverse ++ pref) tmp ix ∧
    ActiveFor transferProgram
      (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) rep pref tmp ix) bits := by
  induction payload generalizing pref bits with
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
          · simpa [KS.W01.frame, Machine.run] using transfer_tag_true tail rep pref tmp ix coin
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
              obtain ⟨he, ha⟩ := ih (bit :: false :: pref) rest hr
              constructor
              · have hs := run_two_of_steps transferMachine _ _ _ c₀ c₁ rest
                  (transfer_tag_false (bit :: (KS.W01.frame payload ++ tail)) rep pref tmp ix c₀)
                  (transfer_data bit (KS.W01.frame payload ++ tail) rep (false :: pref) tmp ix c₁)
                exact hs.trans (by
                  simp only [KS.W01.frame, List.reverse_cons, List.append_assoc,
                    List.singleton_append] at he ⊢
                  exact he)
              · erw [ActiveFor.eq_2]
                refine ⟨Option.some_ne_none _, ?_⟩
                erw [transferProgram_step]
                simp only [KS.W01.frame, List.cons_append]
                erw [transfer_tag_false]
                erw [ActiveFor.eq_2]
                refine ⟨Option.some_ne_none _, ?_⟩
                erw [transferProgram_step]
                erw [transfer_data]
                exact ha

theorem transfer_frame_haltsAfter (payload tail rep pref tmp ix bits : List Bool)
    (hlen : bits.length = 2 * payload.length + 1) :
    HaltsAfter transferProgram
      (config (some (0 : Fin 2)) (KS.W01.frame payload ++ tail) rep pref tmp ix) bits := by
  have h := transfer_frame payload tail rep pref tmp ix bits hlen
  refine ⟨h.2, ?_⟩
  erw [transferProgram_run]
  exact congrArg (fun c : Config 5 2 => c.state) h.1

theorem prefix_guard_nil (src rep pref tmp : List Bool) (coin : Bool) :
    prefixProgram.toMachine.step (config (some prefixProgram.initial) src rep pref tmp []) coin =
      config none src rep pref tmp [] := by
  change (KS.W29.FixedLoop.loop transferProgram indexGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState transferProgram), «stacks» src rep pref tmp []⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, config]
    rfl
  · intro j
    fin_cases j <;> simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, Instruction.action, StackAction.apply, config]

theorem prefix_guard_cons (src rep pref tmp ix : List Bool) (coin : Bool) :
    prefixProgram.toMachine.step
      (config (some prefixProgram.initial) src rep pref tmp (true :: ix)) coin =
      KS.W29.FixedLoop.liftBody transferProgram (config (some (0 : Fin 2)) src rep pref tmp ix) := by
  change (KS.W29.FixedLoop.loop transferProgram indexGuard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState transferProgram), «stacks» src rep pref tmp (true :: ix)⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody, config]
    rfl
  · intro j
    fin_cases j <;> simp [indexGuard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody,
      Instruction.action, StackAction.apply, config]

theorem transfer_prefix («prefix» : List (List Bool)) (tail rep pref tmp bits : List Bool)
    (hlen : bits.length = KS.W11.FramedArray.scanFuel «prefix») :
    prefixProgram.toMachine.run
      (config (some prefixProgram.initial) («prefix».flatMap KS.W01.frame ++ tail)
        rep pref tmp (List.replicate «prefix».length true)) bits =
      config none tail rep ((«prefix».flatMap KS.W01.frame).reverse ++ pref) tmp [] := by
  induction «prefix» generalizing pref bits with
  | nil =>
      cases bits with
      | nil => simp [KS.W11.FramedArray.scanFuel] at hlen
      | cons coin rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [KS.W11.FramedArray.scanFuel, List.flatMap_nil, List.length_nil,
              List.length_cons] at hlen
            omega
          subst rest
          simpa [Machine.run] using prefix_guard_nil tail rep pref tmp coin
  | cons p ps ih =>
      cases bits with
      | nil => simp [KS.W11.FramedArray.scanFuel] at hlen
      | cons coin rest =>
          have hr : rest.length = (2 * p.length + 1) + KS.W11.FramedArray.scanFuel ps := by
            rw [KS.W11.FramedArray.scanFuel_cons] at hlen
            simp only [List.length_cons] at hlen
            omega
          have ht : (rest.take (2 * p.length + 1)).length = 2 * p.length + 1 := by
            simp only [List.length_take, hr]
            omega
          have hd : (rest.drop (2 * p.length + 1)).length = KS.W11.FramedArray.scanFuel ps := by
            simp only [List.length_drop, hr]
            omega
          simp only [List.flatMap_cons, List.append_assoc, List.length_cons,
            List.replicate_succ, Machine.run]
          rw [prefix_guard_cons]
          conv_lhs => rw [← List.take_append_drop (2 * p.length + 1) rest]
          erw [KS.W29.FixedLoop.run_body_then transferProgram indexGuard _ _ _
            (transfer_frame_haltsAfter p (ps.flatMap KS.W01.frame ++ tail) rep pref tmp
              (List.replicate ps.length true) _ ht)]
          erw [transferProgram_run]
          erw [(transfer_frame p (ps.flatMap KS.W01.frame ++ tail) rep pref tmp
            (List.replicate ps.length true) _ ht).1]
          have hi := ih ((KS.W01.frame p).reverse ++ pref) _ hd
          simp only [List.reverse_append, List.append_assoc] at hi ⊢
          exact hi

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_FramedArrayReplacement
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack KS.W03.MachineCombinators
open KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup (run_halted_of_length_ge run_compose_bounded)

theorem run_prefix («prefix» : List (List Bool)) (tail replacement bits : List Bool)
    (hlen : KS.W11.FramedArray.scanFuel «prefix» ≤ bits.length) :
    prefixProgram.toMachine.run
      (config (some prefixProgram.initial) («prefix».flatMap KS.W01.frame ++ tail)
        replacement [] [] (List.replicate «prefix».length true)) bits =
      config none tail replacement («prefix».flatMap KS.W01.frame).reverse [] [] := by
  apply run_halted_of_length_ge prefixProgram.toMachine _ _
    (KS.W11.FramedArray.scanFuel «prefix») rfl _ bits hlen
  intro bs hb
  simpa only [List.append_nil] using transfer_prefix «prefix» tail replacement [] [] bs hb

theorem run_skip (old tail replacement «prefix» scratch bits : List Bool)
    (hlen : 2 * old.length + 1 ≤ bits.length) :
    skipProgram.toMachine.run
      (config (some skipProgram.initial) (KS.W01.frame old ++ tail) replacement «prefix» scratch [])
      bits = config none tail replacement «prefix» scratch [] := by
  have hs : RunSpec KS.W11.FramedArray.skipProgram
      (KS.W11.FramedArray.«stacks» (KS.W01.frame old ++ tail) replacement «prefix» [])
      (KS.W11.FramedArray.«stacks» tail replacement «prefix» []) (2*old.length+1) := by
    intro bs hb
    erw [KS.W11.FramedArray.skipProgram_run]
    exact (KS.W11.FramedArray.skip_frame old tail replacement «prefix» [] bs hb).1
  have hl : RunSpec skipProgram
      («stacks» (KS.W01.frame old ++ tail) replacement «prefix» scratch [])
      («stacks» tail replacement «prefix» scratch []) (2*old.length+1) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ skipPorts _ _ _ _ _ hs
    · intro j;fin_cases j <;> rfl
    · intro j;fin_cases j <;> rfl
    · intro j hj
      have h0 : j ≠ (0 : Fin 5) := hj 0
      simp [«stacks»,h0]
  exact hl.run_of_le bits hlen

theorem run_reverseNew (src replacement «prefix» bits : List Bool)
    (hlen : replacement.length + 1 ≤ bits.length) :
    reverseNew.toMachine.run
      (config (some reverseNew.initial) src replacement «prefix» [] []) bits =
      config none src [] «prefix» replacement.reverse [] := by
  have h : RunSpec reverseNew («stacks» src replacement «prefix» [] [])
      («stacks» src [] «prefix» replacement.reverse []) (replacement.length+1) := by
    convert KS.W15.RationalMultiply.move_spec (1 : Fin 5) 3 (by decide)
      («stacks» src replacement «prefix» [] []) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> simp [«stacks»,KS.W15.RationalMultiply.moveAfter]
  exact h.run_of_le bits hlen

theorem run_insertNew (src «prefix» reversed bits : List Bool)
    (hlen : reversed.length + 1 ≤ bits.length) :
    insertNew.toMachine.run
      (config (some insertNew.initial) src [] «prefix» reversed []) bits =
      config none (reversed.reverse ++ src) [] «prefix» [] [] := by
  have h : RunSpec insertNew («stacks» src [] «prefix» reversed [])
      («stacks» (reversed.reverse ++ src) [] «prefix» [] []) (reversed.length+1) := by
    convert KS.W15.RationalMultiply.move_spec (3 : Fin 5) 0 (by decide)
      («stacks» src [] «prefix» reversed []) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> simp [«stacks»,KS.W15.RationalMultiply.moveAfter]
  exact h.run_of_le bits hlen

theorem run_restorePrefix (src «prefix» bits : List Bool)
    (hlen : «prefix».length + 1 ≤ bits.length) :
    restorePrefix.toMachine.run
      (config (some restorePrefix.initial) src [] «prefix» [] []) bits =
      config none («prefix».reverse ++ src) [] [] [] [] := by
  have h : RunSpec restorePrefix («stacks» src [] «prefix» [] [])
      («stacks» («prefix».reverse ++ src) [] [] [] []) («prefix».length+1) := by
    convert KS.W15.RationalMultiply.move_spec (2 : Fin 5) 0 (by decide)
      («stacks» src [] «prefix» [] []) using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    funext j
    fin_cases j <;> simp [«stacks»,KS.W15.RationalMultiply.moveAfter]
  exact h.run_of_le bits hlen

theorem run_finish (src replacement «prefix» bits : List Bool)
    (hlen : 2 * replacement.length + «prefix».length + 3 ≤ bits.length) :
    finishProgram.toMachine.run
      (config (some finishProgram.initial) src replacement «prefix» [] []) bits =
      config none («prefix».reverse ++ replacement ++ src) [] [] [] [] := by
  apply run_compose_bounded reverseNew insertAndRestore
    («stacks» src replacement «prefix» [] [])
    («stacks» src [] «prefix» replacement.reverse [])
    («stacks» («prefix».reverse ++ replacement ++ src) [] [] [] [])
    (replacement.length + 1) (replacement.length + «prefix».length + 2)
  · exact run_reverseNew src replacement «prefix»
  · intro bs hb
    apply run_compose_bounded insertNew restorePrefix
      («stacks» src [] «prefix» replacement.reverse [])
      («stacks» (replacement ++ src) [] «prefix» [] [])
      («stacks» («prefix».reverse ++ replacement ++ src) [] [] [] [])
      (replacement.length + 1) («prefix».length + 1)
    · intro cs hc
      have h := run_insertNew src «prefix» replacement.reverse cs (by simpa using hc)
      simp only [List.reverse_reverse] at h ⊢
      exact h
    · intro cs hc
      have h := run_restorePrefix (replacement ++ src) «prefix» cs hc
      simp only [List.append_assoc] at h ⊢
      exact h
    · omega
  · omega

theorem run_replaceTail (old tail replacement «prefix» bits : List Bool)
    (hlen : 2 * old.length + 2 * replacement.length + «prefix».length + 4 ≤ bits.length) :
    replaceTailProgram.toMachine.run
      (config (some replaceTailProgram.initial)
        (KS.W01.frame old ++ tail) replacement «prefix» [] []) bits =
      config none («prefix».reverse ++ replacement ++ tail) [] [] [] [] := by
  apply run_compose_bounded skipProgram finishProgram
    («stacks» (KS.W01.frame old ++ tail) replacement «prefix» [] [])
    («stacks» tail replacement «prefix» [] [])
    («stacks» («prefix».reverse ++ replacement ++ tail) [] [] [] [])
    (2 * old.length + 1) (2 * replacement.length + «prefix».length + 3)
  · exact run_skip old tail replacement «prefix» []
  · exact run_finish tail replacement «prefix»
  · omega

end KS.W11.FramedArrayRewrite

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Encoding_ZeroArrayConstructor
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W11.ZeroArrayConstructor
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

theorem emit_step (word : List Bool) (p : ℕ) (hp : p < word.length)
    (count accum output : List Bool) (coin : Bool) :
    (emitProgram word).toMachine.step
      ⟨some ⟨p, by change p < word.length+1;omega⟩, «stacks» count accum output⟩ coin =
      ⟨some ⟨p + 1, by change p+1 < word.length+1;omega⟩, «stacks» count (word[p] :: accum) output⟩ := by
  change (compile _ _ _ (emitDispatch word)).step _ coin = _
  erw [step_compile]
  apply config_ext
  · simp [emitDispatch, hp]
    rfl
  · intro j
    fin_cases j <;> simp [emitDispatch, hp, «stacks», Instruction.action, KS.W29.StackAction.apply]

theorem emit_done (word : List Bool) (count accum output : List Bool) (coin : Bool) :
    (emitProgram word).toMachine.step
      ⟨some ⟨word.length, by change word.length < word.length+1;omega⟩, «stacks» count accum output⟩ coin =
      ⟨none, «stacks» count accum output⟩ := by
  change (compile _ _ _ (emitDispatch word)).step _ coin = _
  erw [step_compile]
  apply config_ext
  · simp [emitDispatch, Instruction.halt]
    rfl
  · intro j
    simp [emitDispatch, Instruction.halt, Instruction.action, KS.W29.StackAction.apply]

theorem run_emit_aux (word : List Bool) (remaining p : ℕ) (hp : p + remaining = word.length)
    (count accum output bits : List Bool) (hlen : bits.length = remaining + 1) :
    (emitProgram word).toMachine.run
      ⟨some ⟨p, by change p < word.length+1;omega⟩, «stacks» count accum output⟩ bits =
      ⟨none, «stacks» count ((word.drop p).reverse ++ accum) output⟩ := by
  induction remaining generalizing p accum bits with
  | zero =>
      have hpe : p = word.length := by omega
      subst p
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          have hr : rest = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [List.length_cons] at hlen
            omega
          subst rest
          simpa [Machine.run] using emit_done word count accum output coin
  | succ remaining ih =>
      have hpl : p < word.length := by omega
      cases bits with
      | nil => simp at hlen
      | cons coin rest =>
          have hr : rest.length = remaining + 1 := by simpa using hlen
          rw [Machine.run, emit_step word p hpl]
          have h := ih (p + 1) (by omega) (word[p] :: accum) rest hr
          rw [List.drop_eq_getElem_cons hpl]
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h

theorem emit_spec (word count accum output : List Bool) :
    RunSpec (emitProgram word) («stacks» count accum output)
      («stacks» count (word.reverse ++ accum) output) (word.length + 1) := by
  intro bits hbits
  have h := run_emit_aux word word.length 0 (by omega) count accum output bits hbits
  simp only [List.drop_zero] at h
  exact h

theorem guard_nil (accum : List Bool) (coin : Bool) :
    loopProgram.toMachine.step ⟨some loopProgram.initial, «stacks» [] accum []⟩ coin =
      ⟨none, «stacks» [] accum []⟩ := by
  change (KS.W29.FixedLoop.loop bodyProgram guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState bodyProgram), _⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  apply config_ext
  · simp [guard, observedHeads, «stacks», KS.W29.topCode, KS.W29.FixedLoop.guardInstruction]
    rfl
  · intro j
    fin_cases j <;> simp [guard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, Instruction.action, KS.W29.StackAction.apply]

theorem guard_cons (count accum : List Bool) (mark coin : Bool) :
    loopProgram.toMachine.step ⟨some loopProgram.initial, «stacks» (mark :: count) accum []⟩ coin =
      KS.W29.FixedLoop.liftBody bodyProgram ⟨some bodyProgram.initial, «stacks» count accum []⟩ := by
  change (KS.W29.FixedLoop.loop bodyProgram guard).toMachine.step
    ⟨some (KS.W29.FixedLoop.guardState bodyProgram), _⟩ coin = _
  rw [KS.W29.FixedLoop.step_guard]
  cases mark <;> apply config_ext
  all_goals
    first | (solve | simp [guard, observedHeads, «stacks», KS.W29.topCode,
      KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody]) |
      (intro j; fin_cases j <;> simp [guard, observedHeads, «stacks», KS.W29.topCode,
        KS.W29.FixedLoop.guardInstruction, KS.W29.FixedLoop.liftBody,
        Instruction.action, KS.W29.StackAction.apply])

theorem finish_spec (word : List Bool) :
    RunSpec finishProgram («stacks» [] word.reverse []) («stacks» [] [] word) (word.length + 1) := by
  intro bits hbits
  have h := KS.W04.BinaryStackMoves.run_move_stacks (1 : Fin 3) 2 (by decide)
    («stacks» [] word.reverse []) bits (by simpa [«stacks»] using hbits)
  change (KS.W04.BinaryStackMoves.moveMachine (1 : Fin 3) 2).run
    ⟨some (0 : Fin 1), «stacks» [] word.reverse []⟩ bits = _
  rw [h]
  apply congrArg (Config.mk none)
  funext j
  fin_cases j <;> simp [«stacks»]

end KS.W11.ZeroArrayConstructor

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_TerminalVectorReplace
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W19.TerminalVectorReplace
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators Matrix

def prepared (s : Fin 35 → List Bool) (new : List Bool) (i : ℕ) : Fin 35 → List Bool :=
  Function.update (Function.update s 0 (KS.W01.frame new)) 3 (List.replicate i true)

end KS.W19.TerminalVectorReplace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_TerminalWitnessTapes
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalVectorReplace

theorem zeroPayloads_ofFn (n : ℕ) : zeroPayloads n = List.ofFn (fun _ : Fin n => KS.W01.encodeRat 0) := by
  simp [zeroPayloads,List.ofFn_const]

def sparsePayloads (n j : ℕ) (c : ℚ) : List (List Bool) :=
  ((zeroPayloads n).set 0 (KS.W01.encodeRat c)).set j (KS.W01.encodeRat 1)

theorem sparse_tape {n : ℕ} (j : Fin (n+1)) (hj : j ≠ 0) (c : ℚ) :
    (sparsePayloads (n+1) j.val c).flatMap KS.W01.frame =
      KS.W12.RowDot.vectorTape (sparseVector j c) := by
  unfold sparsePayloads
  erw [zeroPayloads_ofFn,ofFn_set _ (0 : Fin (n+1)),ofFn_set _ j]
  unfold KS.W12.RowDot.vectorTape
  congr 2
  funext i
  by_cases hij : i = j
  · subst i
    simp [sparseVector,hj]
  · by_cases hi0 : i = 0
    · subst i
      simp [sparseVector,Ne.symm hj]
    · simp [Function.update_of_ne,hij,hi0,sparseVector]

end KS.W19.TerminalVectorReplace

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_TerminalWitnessMachine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W19.TerminalWitnessMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07 Matrix

def outputState {n : ℕ} (saved : List Bool) (M : DenseRatMatrix (n+1)) (j : Fin (n+1)) :
    Fin 35 → List Bool := fun i => if i=31 then KS.W08.denseMatrixTape M else
      if i=26 then Computability.encodeNat (n+1) else if i=32 then saved else
      if i=23 then KS.W12.RowDot.vectorTape (KS.W17.zeroPivotWitness (DenseRatMatrix.decode M) 0 j) else []

end KS.W19.TerminalWitnessMachine

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotControllerLoop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W17.FixedPSD
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07

theorem vectorTape_nonempty {N : ℕ} (hN : 0<N) (q : Fin N → ℚ) : KS.W12.RowDot.vectorTape q ≠ [] := by
  cases N with
  | zero => omega
  | succ N =>
    intro he
    have hl := congrArg List.length he
    simp [KS.W12.RowDot.vectorTape,List.ofFn_succ,KS.W01.length_frame] at hl

end KS.W17.FixedPSD

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_StoredPSDRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

def flattenList {α : Type*} (ea : α → Word) :
    Realizes (listCode (listCode ea)) (listCode ea) List.flatten :=
  (((constant (listCode (listCode ea)) (listCode ea) []).both
    (identity (listCode (listCode ea)))).then (appendList ea).fold).congr (by
      intro xs
      simpa using fold_append_flatten xs [])

lemma vector_tape {n : ℕ} (v : Fin n → ℚ) :
    vectorCode (List.ofFn v)=KS.W12.RowDot.vectorTape v := by
  change (List.ofFn v).flatMap (fun x => KS.W01.frame (ratCode x))=
    (List.ofFn (ratCode ∘ v)).flatMap KS.W01.frame
  rw [←List.map_ofFn,List.flatMap_map]

lemma matrixData_tape {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    vectorCode (matrixData M).flatten=KS.W08.denseMatrixTape (KS.W07.DenseRatMatrix.ofMatrix M) := by
  rw [matrixData_flatten,vector_tape]
  simp only [KS.W12.RowDot.vectorTape,KS.W08.denseMatrixTape,KS.W08.denseMatrixPayloads,
    KS.W07.DenseRatMatrix.decode_ofMatrix]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScheduleRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*} {ea : α → Word} {f g : α → ℚ}

def Realizes.min (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) :
    Realizes ea ratCode (fun x => min (f x) (g x)) :=
  ((r.le s).ite r s).congr (by intro x;simp [min_def])
def Realizes.max (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) :
    Realizes ea ratCode (fun x => max (f x) (g x)) :=
  ((r.le s).ite s r).congr (by intro x;simp [max_def])
def Realizes.eq (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) :
    Realizes ea boolCode (fun x => decide (f x = g x)) :=
  ((r.le s).ite (s.le r) (constant ea boolCode false)).congr (by
    intro x
    rcases lt_trichotomy (f x) (g x) with h|h|h
    · simp [h.le,not_le.mpr h,ne_of_lt h]
    · simp [h]
    · simp [not_le.mpr h,ne_of_gt h])

def parameterField (i : ℕ) : Realizes parametersCode ratCode (fun p => (parametersData p).getD i 0) :=
  let view := (identity vectorCode).reindex parametersCode parametersData (fun _ => rfl)
  ((constant parametersCode natCode i).both view).then (getD ratCode 0)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoundedStepRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

def stateY : Realizes pencilStateCode vectorCode (fun s => List.ofFn s.y) :=
  stateView.then ((second pencilCode (prodCode stepParametersCode vectorCode)).then
    (second stepParametersCode vectorCode))

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_SearchRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def searchView : Realizes searchStateCode pencilStateDataCode searchStateData :=
  (identity pencilStateDataCode).reindex searchStateCode searchStateData (fun _ => rfl)
def searchPencil : Realizes searchStateCode pencilCode (fun s => pencilData s.B) :=
  searchView.then (first pencilCode (prodCode stepParametersCode vectorCode))
def searchParameters : Realizes searchStateCode stepParametersCode (fun s => (s.r,s.R)) :=
  searchView.then ((second pencilCode (prodCode stepParametersCode vectorCode)).then
    (first stepParametersCode vectorCode))
def searchY : Realizes searchStateCode vectorCode (fun s => List.ofFn s.y) :=
  searchView.then ((second pencilCode (prodCode stepParametersCode vectorCode)).then
    (second stepParametersCode vectorCode))
def searchDim : Realizes searchStateCode natCode SearchState.n :=
  (searchY.then (lengthList ratCode)).congr (fun _ => List.length_ofFn)

lemma pencilNext_iterate (s : PencilState) (k : ℕ) :
    PencilState.next^[k] s={s with y := (s.B.next s.step s.mesh)^[k] s.y} := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply'];rfl

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_SelectionRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*}

def better (ea : α → Word) : Realizes (prodCode (scoredCode ea) (scoredCode ea)) (scoredCode ea) betterData :=
  let old := first (scoredCode ea) (scoredCode ea)
  let new := second (scoredCode ea) (scoredCode ea)
  let comparison := ((old.then (second ea ratCode)).le (new.then (second ea ratCode))).ite
    (constant (prodCode (scoredCode ea) (scoredCode ea)) boolCode false)
    (constant (prodCode (scoredCode ea) (scoredCode ea)) boolCode true)
  (comparison.ite new old).congr (by
    intro input
    by_cases hcompare : input.1.2 ≤ input.2.2
    · simp [betterData,hcompare,not_lt_of_ge hcompare]
    · simp [betterData,hcompare,lt_of_not_ge hcompare])

def selectScored (ea : α → Word) := (better ea).fold

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoundedStep
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize
open scoped BigOperators

instance poly_stateView : PolyTime stateView := by unfold stateView;apply poly_reindex
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSearch
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_searchView : PolyTime searchView := by unfold searchView;apply poly_reindex
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_WitnessRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def witnessStateData (a : WitnessState) : PencilData×List ℚ := (pencilData a.B,List.ofFn a.y)
def witnessStateCode (a : WitnessState) := prodCode pencilCode vectorCode (witnessStateData a)
def witnessStateView : Realizes witnessStateCode (prodCode pencilCode vectorCode) witnessStateData :=
  (identity (prodCode pencilCode vectorCode)).reindex witnessStateCode witnessStateData (fun _ => rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OptimizeRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

abbrev optDataCode := prodCode pencilCode (prodCode vectorCode optScalarsCode)
def optData (p : OptParams) := (pencilData p.B,(List.ofFn p.f,(p.delta,(p.r,(p.R,p.U)))))
def optCode (p : OptParams) : Word := optDataCode (optData p)
def optView : Realizes optCode optDataCode optData :=
  (identity optDataCode).reindex optCode optData (fun _ => rfl)
def optB : Realizes optCode pencilCode (fun p => pencilData p.B) :=
  optView.then (first pencilCode (prodCode vectorCode optScalarsCode))
def optF : Realizes optCode vectorCode (fun p => List.ofFn p.f) :=
  optView.then ((second pencilCode (prodCode vectorCode optScalarsCode)).then
    (first vectorCode optScalarsCode))
def optScalars : Realizes optCode optScalarsCode (fun p => (p.delta,(p.r,(p.R,p.U)))) :=
  optView.then ((second pencilCode (prodCode vectorCode optScalarsCode)).then
    (second vectorCode optScalarsCode))
def optDelta : Realizes optCode ratCode OptParams.delta :=
  optScalars.then (first ratCode (prodCode ratCode (prodCode ratCode ratCode)))
def optRest : Realizes optCode (prodCode ratCode (prodCode ratCode ratCode)) (fun p => (p.r,(p.R,p.U))) :=
  optScalars.then (second ratCode (prodCode ratCode (prodCode ratCode ratCode)))
def optRadius : Realizes optCode stepParametersCode (fun p => (p.r,p.R)) :=
  (optRest.then (first ratCode (prodCode ratCode ratCode))).both
    (optRest.then ((second ratCode (prodCode ratCode ratCode)).then (first ratCode ratCode)))
def optUpper : Realizes optCode ratCode OptParams.U :=
  optRest.then ((second ratCode (prodCode ratCode ratCode)).then (second ratCode ratCode))

def candidateSearch (p : OptParams×ℕ) : SearchState :=
  ⟨p.1.n,p.1.m+1,p.1.B.withLevel p.1.f (RationalSDP.level p.1.delta p.1.U p.2),p.1.r,p.1.R,0⟩
abbrev optStateDataCode := prodCode optCode (prodCode natCode vectorCode)
def optStateCode (s : OptState) : Word := optStateDataCode (optStateData s)
def optStateView : Realizes optStateCode optStateDataCode optStateData :=
  (identity optStateDataCode).reindex optStateCode optStateData (fun _ => rfl)
def osP : Realizes optStateCode optCode OptState.p :=
  optStateView.then (first optCode (prodCode natCode vectorCode))
def osK : Realizes optStateCode natCode OptState.k :=
  optStateView.then ((second optCode (prodCode natCode vectorCode)).then (first natCode vectorCode))
def osY : Realizes optStateCode vectorCode (fun s => List.ofFn s.y) :=
  optStateView.then ((second optCode (prodCode natCode vectorCode)).then (second natCode vectorCode))

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOptimize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_optView : PolyTime optView := by unfold optView;apply poly_reindex
instance poly_optStateView : PolyTime optStateView := by unfold optStateView;apply poly_reindex
instance poly_witnessStateView : PolyTime witnessStateView := by unfold witnessStateView;apply poly_reindex
variable {ι : Type*} {L : ι → ℕ}

def candidateResource (p : OptParams×ℕ) : ℕ := (optCode p.1).length+p.2+p.1.searchCount

def nextResource (s : OptState) : ℕ := (optStateCode s).length+s.p.searchCount
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueEvalRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def veN := veD.then realDimension

def veTime : Realizes valueEvalCode ratCode (fun p => p.2.getD 0 0) :=
  ((constant valueEvalCode natCode 0).both veY).then (getD ratCode 0)

def sumData (p : ValueData) : MatrixData := weightedSumData (p.1+p.1,(p.2.2.1,p.2.1))
lemma sumData_value {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) :
    sumData (valueData coords x θ ε)=matrixData (RationalSDP.rationalSum coords x) := by
  apply weightedSum_data

def etaData (p : ValueData×MatrixData) : MatrixData :=
  weightedSumData (p.1.1+p.1.1,(p.1.2.2.2.1.map (fun z => 384*z),
    p.1.2.1.map (fun A => sandwichData (A,p.2))))
lemma etaData_value {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (Z : Matrix (Fin (d+d)) (Fin (d+d)) ℚ) :
    etaData (valueData coords x θ ε,matrixData Z)=matrixData (RationalSDP.rationalEta coords θ Z) := by
  unfold etaData valueData
  simp only [List.map_ofFn,Function.comp_def,sandwich_data]
  rw [weightedSum_data]
  simp only [RationalSDP.rationalEta,LinearMap.sum_apply,LinearMap.smul_apply,RationalSDP.sandwichLinear,LinearMap.coe_mk,AddHom.coe_mk]

def schurEvalData (second : Bool) (p : ValueEvalData) : MatrixData :=
  let I := eyeData (p.1.1+p.1.1)
  let S := if second then sumData p.1 else matrixNegData (sumData p.1)
  let etaZ := etaData (p.1,matrixVariableData (!second) (p.1.1,p.2))
  let top := matrixSubData (matrixAddData (matrixScaleData (p.2.getD 0 0,I),S),etaZ)
  fromBlocksData ((top,I),(I,matrixVariableData second (p.1.1,p.2)))

lemma schurEval_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    schurEvalData second (valueData coords x θ ε,List.ofFn y)=
      matrixData ((RationalSDP.schurPencil coords x θ second).eval y) := by
  have hd : (valueData coords x θ ε).1=d := rfl
  cases second <;> simp only [schurEvalData,hd,eyeData,identityMatrix_data,
    matrixVariable_data,time_getD,sumData_value,etaData_value,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
    matrixNeg_data,matrixScaleData,matrixScale_data,matrixAddData,matrixAdd_data,
    matrixSub_data,fromBlocks_data]
  all_goals rw [RationalSDP.schurPencil_eval];rfl

def lowerBoxData (second : Bool) (p : ValueEvalData) : MatrixData :=
  matrixSubData (matrixVariableData second (p.1.1,p.2),matrixScaleData (1/400,eyeData (p.1.1+p.1.1)))

def upperBoxData (second : Bool) (p : ValueEvalData) : MatrixData :=
  matrixSubData (matrixScaleData (200/p.1.2.2.2.2,eyeData (p.1.1+p.1.1)),matrixVariableData second (p.1.1,p.2))

def valueEvalData (p : ValueEvalData) : MatrixData :=
  blockDiagonalData (blockDiagonalData (blockDiagonalData (blockDiagonalData (blockDiagonalData
    (blockDiagonalData (blockDiagonalData (schurEvalData false p,schurEvalData true p),
      lowerBoxData false p),upperBoxData false p),lowerBoxData true p),upperBoxData true p),
        [[p.2.getD 0 0]]),[[100-p.2.getD 0 0]])

lemma lowerBox_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    lowerBoxData second (valueData coords x θ ε,List.ofFn y)=
      matrixData ((RationalSDP.lowerMatrixPencil d second).eval y) := by
  unfold lowerBoxData
  change matrixSubData (matrixVariableData second (d,List.ofFn y),matrixScaleData (1/400,eyeData (d+d)))=_
  rw [matrixVariable_data,eyeData,identityMatrix_data,matrixScaleData,matrixScale_data,matrixSub_data,
    RationalSDP.lowerMatrixPencil_eval]
lemma upperBox_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (second : Bool) (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    upperBoxData second (valueData coords x θ ε,List.ofFn y)=
      matrixData ((RationalSDP.upperMatrixPencil d ε second).eval y) := by
  unfold upperBoxData
  change matrixSubData (matrixScaleData (200/ε,eyeData (d+d)),matrixVariableData second (d,List.ofFn y))=_
  rw [matrixVariable_data,eyeData,identityMatrix_data,matrixScaleData,matrixScale_data,matrixSub_data,
    RationalSDP.upperMatrixPencil_eval]

lemma valueEval_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ)
    (y : Fin (RationalSDP.valueDimension d) → ℚ) :
    valueEvalData (valueData coords x θ ε,List.ofFn y)=
      matrixData ((RationalSDP.valuePencil coords x θ ε).eval y) := by
  unfold valueEvalData
  rw [schurEval_data,schurEval_data,lowerBox_data,lowerBox_data,upperBox_data,upperBox_data,time_getD]
  simp only [tinyMatrix_data,blockDiagonal_data,RationalSDP.valuePencil,pencil_blockDiagonal_eval]
  congr 1
  have hl : (RationalSDP.lowerTimePencil d).eval y=RationalSDP.timeCoordinate d y •
      (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    erw [RationalSDP.lowerTimePencil,RationalSDP.Pencil.ofAffine_eval,zero_add];rfl
  have hu : (RationalSDP.upperTimePencil d).eval y=(100-RationalSDP.timeCoordinate d y) •
      (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    erw [RationalSDP.upperTimePencil,RationalSDP.Pencil.ofAffine_eval]
    change (100:ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ) + -(RationalSDP.timeCoordinate d y • (1 : Matrix (Fin 1) (Fin 1) ℚ)) = _
    rw [← sub_eq_add_neg,← sub_smul]
  rw [hl,hu]

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

def valuePencilData (p : ValueData) : PencilData :=
  pencilFromEvalData valueEvalData (p,RationalSDP.valueDimension p.1)
lemma valuePencil_data {d N : ℕ} (coords : Fin N → Fin d×Fin d → ℚ) (x θ : Fin N → ℚ) (ε : ℚ) :
    valuePencilData (valueData coords x θ ε)=pencilData (RationalSDP.valuePencil coords x θ ε) :=
  pencilFromEval_data _ _ _ (valueEval_data coords x θ ε)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PotentialRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def ppN : Realizes potentialCode natCode PotentialParams.N :=
  (ppX.then (lengthList ratCode)).congr (by intro p;exact List.length_ofFn)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceQueryRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def gather : Realizes (prodCode vectorCode indicesCode) vectorCode gatherData :=
  (((second vectorCode natCode).both (first vectorCode natCode)).then (getD ratCode 0)).mapCtx

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceRunRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def minList : Realizes vectorCode ratCode Descent.minList :=
  let one := constant vectorCode ratCode 1
  let op := (first ratCode ratCode).min (second ratCode ratCode)
  ((one.both (reverseList ratCode)).then op.fold).congr minList_reverse

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalFieldsRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def originalN : Realizes originalCode natCode Input.N :=
  (originalRecords.then (lengthList vectorCode)).congr (fun _ => List.length_ofFn)

def recordEntry (imag : Bool) : Realizes recordPointCode ratCode (recordEntryData imag) :=
  let r := (first (prodCode recordCode natCode) natCode).then (first recordCode natCode)
  let d := r.then (first natCode vectorCode)
  let fields := r.then (second natCode vectorCode)
  let i := (first (prodCode recordCode natCode) natCode).then (second recordCode natCode)
  let j := second (prodCode recordCode natCode) natCode
  let offset := (((i.both d).then natMul).both j).then natAdd
  let twice := ((constant recordPointCode natCode 2).both offset).then natMul
  (((twice.both (constant recordPointCode natCode (if imag then 1 else 0))).then natAdd).both fields).then (getD ratCode 0)

def originalRecord : Realizes (finFamilyCode originalCode Input.N) recordCode
    (fun p => (p.1.d,fieldValues p.1 p.2)) :=
  let x : Realizes (finFamilyCode originalCode Input.N) originalCode (fun p => p.1) := familyFirst
  let i : Realizes (finFamilyCode originalCode Input.N) natCode (fun p => p.2.val) := familyIndex
  ((x.then originalD).both ((i.both (x.then originalRecords)).then (getD vectorCode []))).congr
    (by intro p;rw [getD_ofFn])

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VarianceRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

lemma foldAdd_matrixData {n : ℕ} (xs : List (Matrix (Fin n) (Fin n) ℚ))
    (A : Matrix (Fin n) (Fin n) ℚ) :
    (xs.map matrixData).foldl
      (fun A B => zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] [] (A,B))
      (matrixData A)=matrixData (A+xs.sum) := by
  induction xs generalizing A with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,matrixAdd_data,ih,List.sum_cons,add_assoc]
lemma matrix_fold_sum {n m : ℕ} (f : Fin n → Matrix (Fin m) (Fin m) ℚ) :
    (List.ofFn (fun i => matrixData (f i))).foldl
      (fun A B => zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] [] (A,B))
      (matrixData (0 : Matrix (Fin m) (Fin m) ℚ))=matrixData (∑ i,f i) := by
  have h := foldAdd_matrixData (List.ofFn f) 0
  simpa only [List.map_ofFn,Function.comp_def,List.sum_ofFn,zero_add] using h

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalSignRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def nonzeroIndices : Realizes vectorCode indicesCode nonzeroIndicesData :=
  let xs := first vectorCode natCode
  let i := second vectorCode natCode
  let val := (i.both xs).then (getD ratCode 0)
  let iszero := val.eq (constant _ ratCode 0)
  let nonzero := iszero.ite (constant _ boolCode false) (constant _ boolCode true)
  (((identity vectorCode).both ((lengthList ratCode).then range)).then nonzero.filterCtx).congr
    (by intro xs;simp only [nonzeroIndicesData];congr 1;funext i;by_cases h : xs.getD i 0=0 <;> simp_all)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ScalarRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 AlgorithmicThinTrees.RationalGram
abbrev squareScanCode := prodCode binaryNatCode (prodCode ratCode vectorCode)
abbrev squarePayload := first binaryNatCode (prodCode ratCode vectorCode)
abbrev squareRest := second binaryNatCode (prodCode ratCode vectorCode)
abbrev squarePower := squareRest.then (first ratCode vectorCode)
abbrev squareAccum := squareRest.then (second ratCode vectorCode)

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
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
def numColumns : Realizes paramsCode natCode Params.m :=
  (columns.then (lengthList vectorCode)).congr (by
    intro p
    exact List.length_ofFn)

def column : Realizes columnCode vectorCode (fun x => List.ofFn (x.1.params.v x.2)) :=
  ((colIndex.both (colParams.then columns)).then (getD vectorCode [])).congr (by
    intro x
    exact getD_ofFn _ _ _)
def scale : Realizes columnCode ratCode (fun x => x.1.scales x.2) :=
  ((colIndex.both (colState.then scales)).then (getD ratCode 0)).congr (by
    intro x
    exact getD_ofFn _ _ _)

def State.next (s : State) : State :=
  ⟨s.params,advance s.params.q s.params.t s.params.v s.scales⟩

lemma next_iterate (s : State) (n : ℕ) :
    State.next^[n] s=⟨s.params,(advance s.params.q s.params.t s.params.v)^[n] s.scales⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change State.mk s.params (advance _ _ _ _) = State.mk s.params _
    rw [Function.iterate_succ_apply']

def initial : Realizes paramsCode stateCode (fun p => ⟨p,fun _ => 1⟩) :=
  ((identity paramsCode).both
    (((constant paramsCode ratCode 1).both numColumns).then (replicateList ratCode))).changeOutput
      stateCode (fun p => ⟨p,fun _ => 1⟩) (by
        intro p
        change prodCode paramsCode vectorCode (p,List.replicate p.m 1)=
          prodCode paramsCode vectorCode (p,List.ofFn (fun _ : Fin p.m => (1:ℚ)))
        rw [List.ofFn_const])

def lengthProgram : Realizes fixedCode natCode
    (fun a => normalizationLength a.1.m a.2) :=
  let c (n : ℕ) := constant fixedCode natCode n
  let m := fixedParams.then numColumns
  ((((((c 2).both m).then natMul).then natSucc).both (c 256)).then natMul).both
    (fixedR.then (unaryPow 4)) |>.then natMul

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_MatrixRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
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

instance poly_matrixView : PolyTime matrixView := by
  unfold matrixView
  apply poly_reindex

abbrev entryCode := prodCode (prodCode matrixObjectCode natCode) natCode
abbrev entryBase := (first (prodCode matrixObjectCode natCode) natCode).then
  (first matrixObjectCode natCode)
abbrev entryI := (first (prodCode matrixObjectCode natCode) natCode).then
  (second matrixObjectCode natCode)
abbrev entryJ := second (prodCode matrixObjectCode natCode) natCode

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_SchurHistory
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
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

def SchurDesc (a b : MatrixObject) : Prop :=
  ∃k, ∃p : Fin k → Fin a.1, ∃r : Fin b.1 → Fin a.1,
    KS.W07.PivotTrace a.2 p r b.2

abbrev schurStackCode := prodCode matrixObjectCode (listCode matrixObjectCode)

abbrev schurCurrent := first matrixObjectCode (listCode matrixObjectCode)
abbrev schurOld := second matrixObjectCode (listCode matrixObjectCode)

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

def stepCore (H : MultiGraph n m) (s κ t : ℝ) (u : Fin m → ℝ) : Set (StepFree n m) :=
  {x | (x.lowerPencil H).PosSemidef ∧ (x.upperPencil H).PosSemidef ∧
    (∀ijk, 0 ≤ x.multiplier ijk) ∧ (∀e, x.y e ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀e, x.z e ∈ Set.Icc 0 (κ+1)) ∧
    (∀e, 0 < u e → (x.edgePencil H s e).PosSemidef ∧
      x.z e ≤ κ+u e+t*(5*x.y e-4))}

def stepFeasible (H : MultiGraph n m) (s κ t q : ℝ) (u : Fin m → ℝ) : Set (StepFree n m) :=
  {x | x ∈ stepCore H s κ t u ∧ ∀p, 0 ≤ slack H.left H.right (x.capacities κ u) q p}

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_FiniteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite continuation. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions Orientations
open scoped Classical MatrixOrder Matrix.Norms.Elementwise
variable {n m : ℕ}

def finiteStep (H : MultiGraph n m) (s κ t qbar ε : ℝ) (u : Fin m → ℝ)
    (x : StepFree n m) (F : FlowPoint n m) : Prop :=
  x ∈ stepCore H s κ t u ∧ F.Feasible H (x.capacities κ u) qbar ε

end
end AlgorithmicThinTrees.MetricTests
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

namespace AlgorithmicThinTrees.MetricTests
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

noncomputable def StepFree.nextCapacity (x : StepFree n m) (κ : ℝ) (u : Fin m → ℝ) (e : Fin m) : ℝ :=
  max 0 (x.capacities κ u e-κ)

end AlgorithmicThinTrees.MetricTests

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Parameters
attribute [-instance] _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
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

instance poly_paramsView : PolyTime paramsView := by
  unfold paramsView
  apply poly_reindex

instance poly_pointView : PolyTime pointView := by
  unfold pointView
  apply poly_reindex

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Realization
attribute [-instance] _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
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

instance poly_loopView : PolyTime loopView := by
  unfold loopView
  apply poly_reindex

abbrev loopMatrix := loopArrays.then (first matrixCode vectorCode)

lemma next_iterate (a : Loop) (i : ℕ) :
    Loop.next^[i] a=⟨a.graph,a.count,(advance a.graph.G a.count)^[i] a.state⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply',ih]
    change Loop.mk a.graph a.count (advance _ _ _) = Loop.mk a.graph a.count _
    rw [Function.iterate_succ_apply']

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_BitBound
attribute [-instance] _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation bit bound. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

structure MeshPoint where
  graph : Graph
  v : Fin (dimension graph.n graph.m) → ℚ

def meshPointCode (a : MeshPoint) : Word := prodCode graphCode vectorCode (a.graph,List.ofFn a.v)
abbrev meshView : Realizes meshPointCode (prodCode graphCode vectorCode)
    (fun a => (a.graph,List.ofFn a.v)) :=
  (identity (prodCode graphCode vectorCode)).reindex meshPointCode
    (fun a => (a.graph,List.ofFn a.v)) (fun _ => rfl)
instance poly_meshView : PolyTime meshView := by
  unfold meshView
  apply poly_reindex

abbrev meshGraph := meshView.then (first graphCode vectorCode)
abbrev meshVector := meshView.then (second graphCode vectorCode)

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_InverseRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
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

abbrev backSolveCode := prodCode matrixCode matrixObjectCode
abbrev solveChild := first matrixCode matrixObjectCode
abbrev solveParent := second matrixCode matrixObjectCode
abbrev solveColumnCode := prodCode backSolveCode natCode
abbrev solveColumnBase := first backSolveCode natCode
abbrev solveColumnIndex := second backSolveCode natCode
abbrev solveColumnA := solveColumnBase.then solveParent
abbrev solveColumnB := solveColumnBase.then solveChild
abbrev solveColumnDim := solveColumnA.then matrixDim
abbrev solveColumnEntries := solveColumnA.then matrixEntries

abbrev rhsCode := prodCode solveColumnCode natCode
abbrev rhsBase := first solveColumnCode natCode
abbrev rhsIndex := second solveColumnCode natCode

def liftColumnData (p : BackSolve×ℕ) : List ℚ :=
  let A := matrixData p.1.2.2
  let r := (List.range p.1.2.1.pred).map (fun i =>
    (if i+1=p.2 then 1 else 0)-(A.getD (i+1) []).getD 0 0*
      ((if 0=p.2 then 1 else 0)/(A.getD 0 []).getD 0 0))
  let y := matVecValue (p.1.1,r)
  let row := (List.range p.1.2.1.pred).map (fun i => (A.getD 0 []).getD (i+1) 0)
  ((if 0=p.2 then 1 else 0)-dotValue (row,y))/(A.getD 0 []).getD 0 0::y

lemma liftColumn_data {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) (j : Fin (n+1)) :
    liftColumnData ((matrixData B,⟨n+1,A⟩),j.val)=
      List.ofFn (RationalInverse.liftSolve A B (Pi.single j (1 : ℚ))) := by
  have rhs : ((List.range n).map (fun i =>
      (if i+1=j.val then 1 else 0)-((matrixData A).getD (i+1) []).getD 0 0*
      ((if 0=j.val then 1 else 0)/((matrixData A).getD 0 []).getD 0 0)))=
      List.ofFn (fun i : Fin n => (Pi.single j (1 : ℚ) : Fin (n+1) → ℚ) i.succ-A i.succ 0*((Pi.single j (1 : ℚ) : Fin (n+1) → ℚ) 0/A 0 0)) := by
    rw [range_map_fin]
    apply congrArg List.ofFn
    funext i
    change (if i.succ.val=j.val then 1 else 0)-
      ((matrixData A).getD i.succ.val []).getD (0 : Fin (n+1)).val 0*
      ((if (0 : Fin (n+1)).val=j.val then 1 else 0)/
      ((matrixData A).getD (0 : Fin (n+1)).val []).getD (0 : Fin (n+1)).val 0)=_
    rw [matrix_entry_data,matrix_entry_data]
    simp only [Pi.single_apply,Fin.val_inj,eq_comm]
  have row : ((List.range n).map (fun i => ((matrixData A).getD 0 []).getD (i+1) 0))=
      List.ofFn (fun i : Fin n => A 0 i.succ) := by
    rw [range_map_fin]
    apply congrArg List.ofFn
    funext i
    exact matrix_entry_data A 0 i.succ
  change ((if 0=j.val then 1 else 0)-dotValue (_,matVecValue (matrixData B,_)))/
    ((matrixData A).getD 0 []).getD 0 0::matVecValue (matrixData B,_)=_
  dsimp only
  simp only [Nat.pred_succ]
  have pivot : ((matrixData A).getD 0 []).getD 0 0=A 0 0 := by
    simpa only [Fin.val_zero] using matrix_entry_data A 0 0
  rw [rhs,row,matVec_data,dot_ofFn,pivot]
  simp only [RationalInverse.liftSolve,List.ofFn_succ,Fin.cons_zero,Fin.cons_succ]
  congr 2
  simp only [Pi.single_apply,←Fin.val_inj,Fin.val_zero,eq_comm]

def inverseLiftData (p : BackSolve) : MatrixData :=
  transposeData ((List.range p.2.1).map (fun j => liftColumnData (p,j)))

lemma inverseLift_data {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) :
    inverseLiftData (matrixData B,⟨n+1,A⟩)=
      matrixData (fun i j => RationalInverse.liftSolve A B (Pi.single j (1 : ℚ)) i) := by
  unfold inverseLiftData
  rw [range_map_fin]
  simp only [liftColumn_data]
  change transposeData (matrixData (fun j i => RationalInverse.liftSolve A B (Pi.single j (1 : ℚ)) i))=_
  exact transpose_data _

lemma inverse_fold_correct (a : MatrixObject) :
    (schurHistoryData a).foldl (fun B A => inverseLiftData (B,A)) []=
      matrixData (RationalInverse.inverse a.1 a.2) := by
  rcases a with ⟨n,A⟩
  induction n with
  | zero => simp [schurHistoryData,RationalInverse.inverse,matrixData]
  | succ n ih =>
    simp only [schurHistoryData,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [ih,inverseLift_data]
    rfl

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix AlgorithmicThinTrees

abbrev gramLiftCode := prodCode matrixCode matrixObjectCode
abbrev gramChild := first matrixCode matrixObjectCode
abbrev gramParent := second matrixCode matrixObjectCode

def firstColumn : Realizes matrixCode vectorCode
    (fun A : MatrixData => A.map (fun row => row.getD 0 0)) :=
  (((constant vectorCode natCode 0).both (identity vectorCode)).then (getD ratCode 0)).map

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

abbrev formDataCode := prodCode matrixObjectCode matrixCode
def formCode (a : FormFrame) : Word := formDataCode a.data
abbrev formView : Realizes formCode formDataCode FormFrame.data :=
  (identity formDataCode).reindex formCode FormFrame.data (fun _ => rfl)
instance poly_formView : PolyTime formView := by
  unfold formView
  apply poly_reindex

abbrev formMatrix := formView.then (first matrixObjectCode matrixCode)
abbrev formRows := formView.then (second matrixObjectCode matrixCode)

def formsCode (p : FormPair) : Word := prodCode formCode formCode (p.left,p.right)
abbrev formsView : Realizes formsCode (prodCode formCode formCode)
    (fun p => (p.left,p.right)) :=
  (identity (prodCode formCode formCode)).reindex formsCode
    (fun p => (p.left,p.right)) (fun _ => rfl)
instance poly_formsView : PolyTime formsView := by
  unfold formsView
  apply poly_reindex

abbrev formsLeft := formsView.then (first formCode formCode)
abbrev formsRight := formsView.then (second formCode formCode)

end AlgorithmicThinTrees.Signing.Stack
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

def halfEdges (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (X : Matrix (Fin (d+1)) (Fin (d+1)) ℚ) (s : Fin m → ℚ) : Finset (Fin m) :=
  FormSigning.selected (positiveForm X) (scaledForm G B s)
    (fullColumns G B) (scaledColumns G B s) ∩ B

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_Step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparsification step. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {d m : ℕ}

def sparsify (G : MultiGraph (d+1) m) (r : ℕ) : Finset (Fin m) :=
  let a := extractState G r
  halfEdges G a.active a.matrix (normalizedScales a.packingTarget r (graphColumns G a.active))

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
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

instance poly_problemView : PolyTime problemView := by
  unfold problemView
  apply poly_reindex

abbrev problemGraph := problemView.then extractionGraph
abbrev problemCount := problemView.then extractionCount
abbrev problemN := problemGraph.then numVertices
abbrev problemM := problemGraph.then numEdges

def problemD : Realizes problemCode natCode Problem.d :=
  (problemN.then natPred).congr (fun _ => rfl)
abbrev number : Realizes edgeCode natCode (fun p : Edge => p.2.val) := familyIndex

def edgeGraphInput : Realizes edgeCode GraphStack.edgeCode (fun p => ⟨p.1.graph,p.2⟩) :=
  ((context.then problemGraph).both number).changeOutput GraphStack.edgeCode
    (fun p => ⟨p.1.graph,p.2⟩) (fun _ => rfl)

lemma graphColumns_drop (p : Problem) (e : Fin p.m) (i : Fin p.d) :
    fullColumns p.G p.active e i.succ=graphColumns p.G p.active e i := by
  simp only [fullColumns,graphColumns,integerColumns,qdiff]
  by_cases h : e ∈ p.active
  · simp only [ite_eq_left h,Pi.sub_apply]
    simp [Pi.single_apply,eq_comm]
  · simp only [ite_eq_right h,Pi.zero_apply,Int.cast_zero]

abbrev maskCode := prodCode problemCode (listCode boolCode)
abbrev maskProblem := first problemCode (listCode boolCode)
abbrev maskSigns := second problemCode (listCode boolCode)
abbrev maskEdgeCode := finFamilyCode maskCode (fun p : MaskInput => p.1.m)
abbrev maskContext : Realizes maskEdgeCode maskCode (fun p : MaskEdge => p.1) := familyFirst
abbrev maskIndex : Realizes maskEdgeCode natCode (fun p : MaskEdge => p.2.val) := familyIndex

def maskEdgeInput : Realizes maskEdgeCode edgeCode (fun p => ⟨p.1.1,p.2⟩) :=
  ((maskContext.then maskProblem).both maskIndex).changeOutput edgeCode
    (fun p => ⟨p.1.1,p.2⟩) (fun _ => rfl)

end AlgorithmicThinTrees.GraphicHalf.Stack
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
abbrev subgraphN : Realizes subgraphCode natCode (fun s => s.graph.n) := subgraphGraph.then numVertices

abbrev subgraphM : Realizes subgraphCode natCode (fun s => s.graph.m) := subgraphGraph.then numEdges

def selected : Realizes sedgeCode boolCode (fun s => decide (s.2 ∈ s.1.A)) :=
  ((sedgeIndex.both (sedgeContext.then subgraphBits)).then (getD boolCode false)).congr
    (fun s => getD_ofFn _ s.2 false)
abbrev reachN : Realizes reachCode natCode (fun s => s.subgraph.graph.n) := reachSubgraph.then subgraphN

abbrev reachM : Realizes reachCode natCode (fun s => s.subgraph.graph.m) := reachSubgraph.then subgraphM

def reached : Realizes vertexCode boolCode (fun v => decide (v.2 ∈ v.1.U)) :=
  ((vertexIndex.both (vertexContext.then reachBits)).then (getD boolCode false)).congr
    (fun v => getD_ofFn _ v.2 false)
abbrev arcLeft := arcEdge.then edgeLeft
abbrev arcRight := arcEdge.then edgeRight

def leftReached : Realizes arcCode boolCode
    (fun a => decide (a.1.1.subgraph.graph.G.left a.2 ∈ a.1.1.U)) :=
  ((arcLeft.both (arcState.then reachBits)).then (getD boolCode false)).congr
    (fun a => getD_ofFn _ (a.1.1.subgraph.graph.G.left a.2) false)
def rightReached : Realizes arcCode boolCode
    (fun a => decide (a.1.1.subgraph.graph.G.right a.2 ∈ a.1.1.U)) :=
  ((arcRight.both (arcState.then reachBits)).then (getD boolCode false)).congr
    (fun a => getD_ofFn _ (a.1.1.subgraph.graph.G.right a.2) false)

def whole : Realizes graphCode subgraphCode (fun g => ⟨g,univ⟩) :=
  ((identity graphCode).both
    (((constant graphCode boolCode true).both numEdges).then (replicateList boolCode))).changeOutput
      subgraphCode (fun g => ⟨g,univ⟩) (by intro g;simp [subgraphCode,Subgraph.bits,List.ofFn_const])

end AlgorithmicThinTrees.GreedyTree.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputArrays
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.copiesEquiv_apply _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input arrays. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

abbrev fieldsCode := listCode binaryNatCode

lemma fieldsCode_flatten (rows : List (List ℕ)) :
    fieldsCode rows.flatten = (rows.map fieldsCode).flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change listCode binaryNatCode (row ++ rows.flatten) =
      fieldsCode row ++ (rows.map fieldsCode).flatten
    rw [listCode_append]
    exact congrArg (List.append (fieldsCode row)) ih

lemma eFields_code (x : ExplicitInput) : fieldsCode (eFields x) = x.encode := by
  simp only [eFields,listCode_append,listCode_cons,listCode_nil,prodCode,PairRoutine.pair,
    fieldsCode_flatten,List.map_ofFn,Function.comp_def]
  simp [binaryNatCode,ExplicitInput.encode,
    CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat,List.append_assoc]
lemma bFields_code (x : BinaryInput) : fieldsCode (bFields x) = x.encode := by
  simp only [bFields,listCode_append,listCode_cons,listCode_nil,prodCode,PairRoutine.pair,
    fieldsCode_flatten,List.map_ofFn,Function.comp_def]
  simp [binaryNatCode,BinaryInput.encode,
    CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat,List.append_assoc]

abbrev eView : Realizes eCode fieldsCode (fun x => eFields x.val) :=
  (identity fieldsCode).reindex eCode (fun x => eFields x.val) (fun x => (eFields_code x.val).symm)
abbrev bView : Realizes bCode fieldsCode (fun x => bFields x.val) :=
  (identity fieldsCode).reindex bCode (fun x => bFields x.val) (fun x => (bFields_code x.val).symm)

def field (i : ℕ) : Realizes fieldsCode binaryNatCode (fun xs => xs.getD i 0) :=
  ((constant fieldsCode natCode i).both (identity fieldsCode)).then (getD binaryNatCode 0)

def eNBinary : Realizes eCode binaryNatCode (fun x => x.val.n) :=
  (eView.then (field 0)).congr (by intro x;rfl)
def eMBinary : Realizes eCode binaryNatCode (fun x => x.val.m) :=
  (eView.then (field 1)).congr (by intro x;rfl)
def eKBinary : Realizes eCode binaryNatCode (fun x => x.val.k) :=
  (eView.then (field 2)).congr (by intro x;rfl)
def bNBinary : Realizes bCode binaryNatCode (fun x => x.val.n) :=
  (bView.then (field 0)).congr (by intro x;rfl)
def bPBinary : Realizes bCode binaryNatCode (fun x => x.val.p) :=
  (bView.then (field 1)).congr (by intro x;rfl)
def bKBinary : Realizes bCode binaryNatCode (fun x => x.val.k) :=
  (bView.then (field 2)).congr (by intro x;rfl)

def eEndpointBinary (right : Bool) : Realizes eEdgeCode binaryNatCode
    (fun x => if right then (x.1.val.graph.right x.2).val else (x.1.val.graph.left x.2).val) :=
  ((((constant eEdgeCode natCode 3).nadd (eeIndex.nmul (constant eEdgeCode natCode 2))).nadd
    (constant eEdgeCode natCode (if right then 1 else 0))).both (eeInput.then eView)).then
      (getD binaryNatCode 0) |>.congr (by
        intro x
        have hh := records_lookup (w:=2) x.1.val.n x.1.val.m x.1.val.k
          (fun i => [(x.1.val.graph.left i).val,(x.1.val.graph.right i).val])
          (fun _ => rfl) x.2 (if right then 1 else 0) (by cases right <;> decide)
        cases right <;> simpa [eFields] using hh)

def bRecordBinary (j : Fin 3) : Realizes bRecCode binaryNatCode
    (fun x => ([(x.1.val.left x.2).val,(x.1.val.right x.2).val,x.1.val.multiplicity x.2]).getD j.val 0) :=
  ((((constant bRecCode natCode 3).nadd (brIndex.nmul (constant bRecCode natCode 3))).nadd
    (constant bRecCode natCode j.val)).both (brInput.then bView)).then (getD binaryNatCode 0)
      |>.congr (fun x => records_lookup (w:=3) x.1.val.n x.1.val.p x.1.val.k
        (fun i => [(x.1.val.left i).val,(x.1.val.right i).val,x.1.val.multiplicity i])
        (fun _ => rfl) x.2 j.val j.isLt)

def bEndpointBinary (right : Bool) : Realizes bRecCode binaryNatCode
    (fun x => if right then (x.1.val.right x.2).val else (x.1.val.left x.2).val) :=
  (bRecordBinary (if right then 1 else 0)).congr (by intro x;cases right <;> rfl)

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input expansion. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack

def makeProblem {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ) : Problem where
  d := n-1
  m := m
  r := k
  G := {
    left e := Fin.cast (Nat.sub_add_cancel hn).symm (G.left e)
    right e := Fin.cast (Nat.sub_add_cancel hn).symm (G.right e)
    loopless e := by
      intro h
      apply G.loopless e
      apply Fin.ext
      exact congrArg (fun v : Fin (n-1+1) => v.val) h }

lemma makeProblem_code {n m : ℕ} (G : MultiGraph n m) (hn : 0<n) (k : ℕ) :
    problemCode (makeProblem G hn k) =
      prodCode graphDataCode natCode ( (n,(List.ofFn (fun e => (G.left e).val),
        List.ofFn (fun e => (G.right e).val))),k) := by
  change prodCode graphDataCode natCode
    ((n-1+1,(List.ofFn (fun e => (G.left e).val), List.ofFn (fun e => (G.right e).val))),k)=_
  rw [Nat.sub_add_cancel hn]

abbrev eProblem (x : E) : Problem := makeProblem x.val.graph (by have h:=x.property.1;omega) x.val.k
abbrev bProblem (x : B) : Problem := makeProblem x.val.reduced.expanded
  (show 0<x.val.n from by have h:=x.property.1;omega) (x.val.n^2)

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_SelectionRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView
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

def maskEntry (ea : α → Word) : Realizes (prodCode boolCode ea) (listCode ea)
    (fun p => if p.1 then [p.2] else []) :=
  (first boolCode ea).ite ((second boolCode ea).then (singleton ea))
    (constant (prodCode boolCode ea) (listCode ea) [])

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_RationalIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational iteration. -/

section

namespace AlgorithmicThinTrees.Iteration
open Finset StrongThinTree StrongThinTree.MultiGraph GraphicHalf
open MetricTests MetricTests.RationalStep

def iterate (R : ℕ) : (fuel r d m : ℕ) →
    MultiGraph (d+1) m → Finset (Fin m)
  | 0,_,_,_,G => GreedyTree.tree G
  | fuel+1,r,d,_,G =>
    if R ≤ r then
      let A := sparsify G r
      OrderedGraph.liftEdges A
        (iterate R fuel (nextCount r) d A.card (OrderedGraph.restrict G A))
    else GreedyTree.tree G

def RoundBound (R : ℕ) : Prop := ∀r : ℕ, R ≤ r →
    ∀(d m : ℕ) (G : MultiGraph (d+1) m), 2 ≤ d+1 → G.TreePackable univ r →
      (r:ℝ)/4 ≤ nextCount r ∧ (nextCount r:ℝ) ≤ (r:ℝ)/2 ∧ 0 < nextCount r ∧
      G.TreePackable (sparsify G r) (nextCount r) ∧
      (∀S : Finset (Fin (d+1)), ((G.cut (sparsify G r) S).card:ℝ) ≤
        (1/2+3*halfError r)*(G.cut univ S).card) ∧
      (1/2+3*halfError r)*(r:ℝ) ≤ (1+80*errorU r)*nextCount r

def tree (R k : ℕ) {d m : ℕ} (G : MultiGraph (d+1) m) : Finset (Fin m) :=
  iterate R (initialCount k) (initialCount k) d m G

end AlgorithmicThinTrees.Iteration
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_IterationRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration realization. -/

section

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep MetricTests.RationalStep.Stack OrderedGraph

structure State where
  problem : Problem
  labels : Fin problem.m → ℕ

def stateCode (s : State) : Word := prodCode problemCode indicesCode
  (s.problem,List.ofFn s.labels)
abbrev stateView : Realizes stateCode (prodCode problemCode indicesCode)
    (fun s => (s.problem,List.ofFn s.labels)) :=
  (identity (prodCode problemCode indicesCode)).reindex stateCode
    (fun s => (s.problem,List.ofFn s.labels)) (fun _ => rfl)
instance poly_stateView : PolyTime stateView := by
  unfold stateView
  apply poly_reindex

abbrev problem := stateView.then (first problemCode indicesCode)

abbrev labels := stateView.then (second problemCode indicesCode)

abbrev graph := problem.then problemGraph

abbrev count := problem.then problemCount

def State.restrict (s : State) (A : Finset (Fin s.problem.m)) : State :=
  ⟨⟨s.problem.d,A.card,nextCount s.problem.r,OrderedGraph.restrict s.problem.G A⟩,
    fun e => s.labels (edgeEmbedding A e)⟩
def halve (s : State) : State := s.restrict (sparsify s.problem.G s.problem.r)
def step (R : ℕ) (s : State) : State := if R ≤ s.problem.r then halve s else s

def finishData (s : State) : List ℕ :=
  List.ofFn (fun e => s.labels (edgeEmbedding (GreedyTree.tree s.problem.G) e))

end AlgorithmicThinTrees.Iteration.Stack

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep OrderedGraph

lemma run_data (R fuel : ℕ) (s : State) :
    finishData ((step R)^[fuel] s)=
      List.ofFn (fun e => s.labels (edgeEmbedding
        (iterate R fuel s.problem.r s.problem.d s.problem.m s.problem.G) e)) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ t ih =>
    by_cases hh : R ≤ s.problem.r
    · rw [Function.iterate_succ_apply,step,ite_eq_left hh,ih,iterate,ite_eq_left hh]
      exact (mapped_sorted_lift (sparsify s.problem.G s.problem.r)
        (iterate R t (nextCount s.problem.r) s.problem.d _
          (OrderedGraph.restrict s.problem.G (sparsify s.problem.G s.problem.r))) s.labels).symm
    · have hfix : step R s=s := by rw [step,ite_eq_right hh]
      have horb : (step R)^[t+1] s=s := Function.iterate_fixed hfix _
      rw [horb,iterate,ite_eq_right hh]
      rfl

abbrev TreeProblem := Problem

def start (p : TreeProblem) : ℕ×State :=
  (initialCount p.r,⟨⟨p.d,p.m,initialCount p.r,p.G⟩,fun e => e.val⟩)

def treeData (R : ℕ) (p : TreeProblem) : List ℕ :=
  List.ofFn (fun e => (edgeEmbedding (Iteration.tree R p.r p.G) e).val)

end AlgorithmicThinTrees.Iteration.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input output. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack OrderedGraph Iteration.Stack
open MetricTests.RationalStep.Stack

def eEdges (R : ℕ) (x : E) : List (Fin x.val.m) :=
  List.ofFn (edgeEmbedding (Iteration.tree R (eProblem x).r (eProblem x).G))
def bEdges (R : ℕ) (x : B) : List x.val.Edge :=
  List.ofFn (fun i => x.val.originalCopy
    (edgeEmbedding (Iteration.tree R (bProblem x).r (bProblem x).G) i))
def eOutput (R : ℕ) (x : E) : Word := x.val.encodeEdges (eEdges R x)
def bOutput (R : ℕ) (x : B) : Word := x.val.encodeEdges (bEdges R x)

lemma bOutput_code (R : ℕ) (x : B) :
    fieldsCode (((treeData R (bProblem x)).map (fun i =>
      [(List.ofFn (fun e : Fin x.val.reduced.copies.length =>
        (x.val.reduced.copies.get e).1.val)).getD i 0,0])).flatten) = bOutput R x := by
  simp only [treeData,List.map_ofFn,Function.comp_def]
  rw [fieldsCode_flatten]
  simp only [List.map_ofFn,Function.comp_def,bOutput,bEdges,BinaryInput.encodeEdges,
    List.flatMap_def,List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext e
  have hget := getD_ofFn (fun i : Fin x.val.reduced.copies.length =>
    (x.val.reduced.copies.get i).1.val)
    (edgeEmbedding (Iteration.tree R (bProblem x).r (bProblem x).G) e) 0
  erw [hget]
  simp [fieldsCode,listCode,FramedMapRoutine.tape,BinaryInput.originalCopy,
    BinaryInput.liftCopy,binaryNatCode,CurrentKS.DenseInputMachine.encodeNat_eq,KS.W01.encodeNat]

end AlgorithmicThinTrees.InputStack
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
open GraphicHalf.Stack

def largeOutput (R : ℕ) (x : Large) : Word :=
  if h : isBinary x.val=true then bOutput R (asBinary ⟨x,h⟩) else eOutput R (asExplicit ⟨x,h⟩)
lemma inputFields_code (x : AlgorithmicThinTrees.Input) :
    fieldsCode (inputFields x) = x.encode.tail := by
  cases x with
  | explicit x => exact eFields_code x
  | binary x => exact bFields_code x

def output (R : ℕ) (x : Good) : Word :=
  if h : x.val.n=1 then [] else largeOutput R (makeLarge ⟨x,h⟩)

end AlgorithmicThinTrees.InputStack
end

end OAI
end


