-- Prove2me | Definitions.Def_OAIQ087A033
-- name    : OAIQ087A033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:58:10.785973+00:00
-- url     : https://prove2.me/theorems/92560a83-c502-4d87-802d-cea407363f3e
-- title:
--   Definitions bundle OAIQ087A033 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 268 declarations of OpenAI's Lean: 104 definitions, 1 inductive type or structure, 3 instances and 160 theorems. The definitions and types are `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.familyInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.levelLoopInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.paddedFamilyInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.resizeInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderRow.rowInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderRow.rowInTimeAt`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.preparedRowInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.suffixInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.suffixRun_aux_inline_MachineExpanderTableRows`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.tableInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.vertexInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.vertexLoopInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyTable.machine`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyTable.machineInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyTable.program`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyTableRuntime.computableInPolyTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyTableRuntime.rawProgram`, `OAI.MaxCutGames.Foundations.Complexity.MachineLazyTableRuntime.terminalRun`, `OAI.MaxCutGames.Foundations.Complexity.MachineOverlayTable.loopBase`, `OAI.MaxCutGames.Foundations.Complexity.MachineOverlayTable.program`, `OAI.MaxCutGames.Foundations.Complexity.MachineOverlayTable.splitTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineOverlayTable.tableInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily.materializeInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily.paddedInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.execution`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.familyInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.familyTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.finalTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.machine`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.overlayInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.overlaySource`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.paddedTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.paddingInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlay.program`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlayRuntime.computableInPolyTime`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlayRuntime.rawProgram`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddedOverlayRuntime.terminalRun`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddingBounds.inputSize`, `OAI.MaxCutGames.Foundations.Complexity.MachinePaddingTable.execution`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularFamily.familyCleanInTime` and 65 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_InputData`, `MaxCut_Estimates_Basic`, `MaxCut_Games_PoweringPolynomialBudget`, `MaxCut_Machines_MachineExpanderFamilyCycle`, `MaxCut_Machines_MachineExpanderRowFrames`, `MaxCut_Machines_MachineExpanderTableRows`, `MaxCut_Machines_MachineLazyTable`, `MaxCut_Machines_MachineLazyTableRuntime`, `MaxCut_Machines_MachineOverlayTable`, `MaxCut_Machines_MachinePaddedExpanderFamilyBounds`, `MaxCut_Machines_MachinePaddedOverlay`, `MaxCut_Machines_MachineRegularOriginalBody`, `MaxCut_Machines_MachineRegularOwnerProgram`, `MaxCut_Machines_MachineRegularTableRuntime`, `MaxCut_Machines_MachineRegularTableTrace`, `MaxCut_Machines_MachineRegularVertexBlock`, `MaxCut_Machines_MachineTableIteration`, `MaxCut_Machines_PoweringMachineRuntime`, `MaxCut_Machines_PoweringMachineVertex`, `MaxCut_PCP_PreprocessingPaddingWords`, `MaxCut_PCP_PreprocessingRegularBounds`, `MaxCut_PCP_RawInitialTables`.
--
--   **Imports.** It imports the bundles `OAIQ087A029`, `OAIQ087A030`, `OAIQ087A031` and `OAIQ087A032` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ087A035`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A029
import Definitions.Def_OAIQ087A030
import Definitions.Def_OAIQ087A031
import Definitions.Def_OAIQ087A032

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderRowFrames
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete data and tape frames for an actual expander-row computation

Only the five actual row inputs are stored. Every address, table return and
finite control value below is computed from those inputs. The thirteen tape
frames use the existing phase-output functions. These are data identities and
size bounds, not assumed machine executions.
-/

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

/-- The actual row program has a linear transition bound, with all temporary
tapes empty at return. The bound holds for every valid finite input table. -/
def rowInTimeAt {v d : Nat} {ρ Λ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive r.smallTable id labels exit l) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .initialize_), divisionState positive ambient r.control0 none,
        frame0 r output⟩
      (some ⟨exit, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩)
      (80 * (r.tableLength + 1)) where
  steps := rowSteps r output
  evals_in_steps := rowTraceAt positive r output ambient labels exit target code
  steps_le_m := rowSteps_le r output

/-- Specialization to the standalone finite row program. -/
def rowInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ) :
    StateTransition.EvalsToInTime (TM2.step (program positive r.smallTable))
      ⟨some .initialize_, divisionState positive ambient r.control0 none, frame0 r output⟩
      (some ⟨none, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩)
      (80 * (r.tableLength + 1)) :=
  rowInTimeAt positive r output ambient id none (program positive r.smallTable) (fun _ => rfl)

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Concrete boundary steps of the expander-table machine

Every execution theorem below reduces the actual common program statement.
States and dependent tape frames are arbitrary; only the relevant unary word
or finite-position branch is specified. No phase execution is a premise.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderTableRows
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem tableRowData_finalFrame {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.emittedWord .output
      (MachineExpanderRow.frame0 (tableRowData G H vertex position) output)
      (tableRowData G H vertex position).finalValue =
      rowTapes vertex.val (encodeWords (rotationWords G))
        ((encodeWord (rowValue G H vertex position)).reverse ++ output) := by
  rw [tableRowData_frame0, tableRowData_finalValue]
  funext tape
  cases tape <;> simp [MachineExpanderRow.emittedWord, rowTapes]

variable {ρ : Type} [Fintype ρ] {v d : Nat}

/-- Preparation and one actual embedded row call, with the two extra tapes
retained. The row value is computed from the actual old and small tables. -/
def preparedRowInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .prepareRow), state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
      (some ⟨some (.inr .afterRow), rowAfterState positive G H vertex state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
          ((encodeWord (rowValue G H vertex state.2)).reverse ++ output) countSuffix result⟩)
      (1 + 80 * ((encodeWords (rotationWords G)).length + 1)) := by
  have raw := rowExecution positive H state.2 (extraTapes remaining countSuffix result)
    (MachineExpanderRow.rowInTime positive (tableRowData G H vertex state.2) output (caller state))
  have run : StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inl .initialize_), prepareState positive H state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
      (some ⟨some (.inr .afterRow), rowAfterState positive G H vertex state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
          ((encodeWord (rowValue G H vertex state.2)).reverse ++ output) countSuffix result⟩)
      (80 * ((encodeWords (rotationWords G)).length + 1)) := by
    rw [tableRowData_finalFrame, tableRowData_frame0] at raw
    simpa only [MachineEmbedding.configuration, MachineEmbedding.label, rowReturn,
      prepareState, boundaryState, rowAfterState, boundaryTapes,
      MachineExpanderRow.RowData.tableLength, MachineExpanderRow.RowData.control0,
      tableRowData, MachineExpanderRow.rowData] using raw
  exact sequence_inline_MachineExpanderTableRows
    (singleStep_inline_MachineExpanderTableRows _ _ _ (prepareRowStep positive H
      (boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result)
      state)) run

def suffixRun_aux_inline_MachineExpanderTableRows (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (remaining : Nat)
    (countSuffix result : List Bool) (n : Nat) :
    (state : State ρ d) → state.2.val + n = rowFactor d → (output : List Bool) →
      VertexSuffixRun positive G H vertex state remaining output countSuffix result := by
  induction n with
  | zero =>
      intro state count output
      have hp := state.2.isLt
      exact False.elim (by omega)
  | succ n ih =>
      intro state count output
      let after := rowAfterState positive G H vertex state
      let nextOutput := (encodeWord (rowValue G H vertex state.2)).reverse ++ output
      have row := preparedRowInTime positive G H vertex state remaining output countSuffix result
      by_cases last : n = 0
      · have hp : state.2.val + 1 = rowFactor d := by omega
        have finish := singleStep_inline_MachineExpanderTableRows _ _ _ (afterRow_last_boundaryStep positive H vertex.val remaining
          (encodeWords (rotationWords G)) nextOutput countSuffix result after (by
            change ¬ state.2.val + 1 < rowFactor d
            omega))
        refine ⟨resetPositionState positive after, ?_, rfl, ?_⟩
        · rfl
        · have all := sequence_inline_MachineExpanderTableRows row finish
          have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              nextOutput := by
            rw [vertexWords_drop_last G H vertex state.2 hp]
            rfl
          have budget : rowFactor d - state.2.val = 1 := by omega
          rw [words, budget, Nat.one_mul]
          exact widen_inline_MachineExpanderTableRows all (by omega)
      · have more : state.2.val + 1 < rowFactor d := by omega
        let next := advancePositionState positive after
        have nextPositionValue : next.2.val = state.2.val + 1 :=
          nextPosition_val_of_lt positive state.2 more
        have nextCount : next.2.val + n = rowFactor d := by omega
        let tail := ih next nextCount nextOutput
        have advance := singleStep_inline_MachineExpanderTableRows _ _ _ (afterRow_moreStep positive H
          (boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
            nextOutput countSuffix result) after more)
        have all := sequence_inline_MachineExpanderTableRows (sequence_inline_MachineExpanderTableRows row advance) tail.execution
        refine ⟨tail.finalState, ?_, tail.position_zero, ?_⟩
        · exact tail.caller_preserved
        · have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              accumulate ((vertexWords G H vertex).drop next.2.val) nextOutput := by
            rw [vertexWords_drop_succ G H vertex state.2, nextPositionValue]
            rfl
          rw [words]
          apply widen_inline_MachineExpanderTableRows all
          have hcount : rowFactor d - state.2.val = n + 1 := by omega
          have hnext : rowFactor d - next.2.val = n := by omega
          rw [hcount, hnext, Nat.add_mul, Nat.one_mul]
          omega

def suffixInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) :
    VertexSuffixRun positive G H vertex state remaining output countSuffix result :=
  suffixRun_aux_inline_MachineExpanderTableRows positive G H vertex remaining countSuffix result
    (rowFactor d - state.2.val) state (by have h := state.2.isLt; omega) output

def vertexInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (position : state.2 = zeroPosition positive)
    (remaining : Nat) (output countSuffix result : List Bool) :
    VertexRun positive G H vertex state remaining output countSuffix result := by
  let run := suffixInTime positive G H vertex state remaining output countSuffix result
  refine ⟨run.finalState, run.caller_preserved, run.position_zero, ?_⟩
  have zero : state.2.val = 0 := congrArg Fin.val position
  simpa only [zero, List.drop_zero, Nat.sub_zero] using run.execution

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

/-- Execute every remaining vertex in the common finite table program. -/
def vertexLoopInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (current remaining : Nat) (state : State ρ d) (suffix : List Bool)
    (count : current + remaining = v) (position : state.2 = zeroPosition positive) :
    VertexLoopRun positive G H current remaining state suffix := by
  induction remaining generalizing current state with
  | zero =>
      have hc : current = v := by omega
      subst current
      refine ⟨clearRegister state, caller_clearRegister state, ?_, ?_⟩
      · simpa only [clearRegister] using position
      · simpa only [vertexLoopBudget, Nat.zero_mul, Nat.zero_add, vertexLoopTapes] using
          boundarySingleStep_inline_MachineExpanderTableLoop _ _ _ (vertexGuard_boundary_zeroStep positive H v (oldTableWord G)
            (accumulatedVertices G H v) suffix [] state)
  | succ remaining ih =>
      have valid : current < v := by omega
      let vertex : Fin v := ⟨current, valid⟩
      let body := vertexInTime positive G H vertex (clearRegister state)
        (by simpa only [clearRegister] using position) remaining
        (accumulatedVertices G H current) suffix []
      have nextCount : current + 1 + remaining = v := by omega
      let rest := ih (current + 1) body.finalState nextCount body.position_zero
      have output_eq : accumulate (vertexWords G H vertex)
          (accumulatedVertices G H current) = accumulatedVertices G H (current + 1) :=
        (accumulatedVertices_succ G H current valid).symm
      let guard := boundarySingleStep_inline_MachineExpanderTableLoop _ _ _
        (vertexGuard_boundary_succStep positive H current remaining (oldTableWord G)
          (accumulatedVertices G H current) suffix [] state)
      have bodyRun : StateTransition.EvalsToInTime (TM2.step (program positive H))
          ⟨some (.inr .prepareRow), clearRegister state,
            boundaryTapes current remaining (oldTableWord G)
              (accumulatedVertices G H current) suffix []⟩
          (some ⟨some (.inr .vertexGuard), body.finalState,
            vertexLoopTapes G H (current + 1) remaining suffix⟩)
          (vertexBodyBudget G) := by
        simpa only [vertexLoopTapes, vertexBodyBudget, oldTableWord, output_eq] using body.execution
      let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
        _ _ _ _ _ guard bodyRun
      let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
        _ _ _ _ _ first rest.execution
      refine ⟨rest.finalState, ?_, rest.position_zero, ?_⟩
      · exact rest.caller_preserved.trans
          (body.caller_preserved.trans (caller_clearRegister state))
      · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
        have bound := all.steps_le_m
        simp only [vertexLoopBudget, Nat.succ_mul] at bound ⊢
        omega

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Complete finite machine execution for the next expander table

The initialized old table and unary vertex count are consumed by one actual
finite program. The machine writes precisely the complete square/zigzag
rotation table, preserving its old table and all promised framing. The bound
is quadratic in the unary old-table length for each fixed small graph.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

/-- Construct the entire table execution from its actual initialized inputs.
No row trace, loop trace, or abstract computational witness is a hypothesis. -/
def tableInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (state : State ρ d) (suffix : List Bool) : TableRun positive G H state suffix := by
  let loop := vertexLoopInTime positive G H 0 v
    (initialState positive H (caller state)) suffix (by omega) rfl
  let initialRun := initializeInTime_inline_MachineExpanderTable positive G H state suffix
  have finish : StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), loop.finalState, vertexLoopTapes G H v 0 suffix⟩
      (some ⟨none, clearRegister loop.finalState,
        finalTapes v (oldTableWord G) (encodeWords (rotationWords (step G H))) suffix⟩)
      ((encodeWords (rotationWords (step G H))).length + 2) := by
    simpa only [vertexLoopTapes, finalTapes, accumulatedVertices_full, List.reverse_reverse,
      List.append_nil, List.length_reverse] using
      reverseOutputHaltInTime positive H v 0 (oldTableWord G)
        (accumulatedVertices G H v) suffix [] loop.finalState
  let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
    _ _ _ _ _ initialRun loop.execution
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H))
    _ _ _ _ _ first finish
  refine ⟨clearRegister loop.finalState, ?_, ?_, ?_⟩
  · exact (caller_clearRegister loop.finalState).trans loop.caller_preserved
  · simpa only [clearRegister] using loop.position_zero
  · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
    have bound := all.steps_le_m
    have polynomialBound := completeBudget_le positive G H
    unfold completeBudget at polynomialBound
    omega

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Bounds for materializing the actual expander family

The costs use the encoded old and new rotation tables, and the already checked
table-machine polynomial. The finite sum follows the actual recursive table
family. These arithmetic lemmas introduce no execution assumptions and make no
claim that the output is polynomial in an isolated binary level parameter.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderFamilyCycle
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

/-- The resize certificate is built from actual primitive and table executions;
its caller supplies no phase trace or computational hypothesis. -/
noncomputable def resizeInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (G : Table v (degree d)) (remaining : Nat) (state : State ρ d) (suffix : List Bool) :
    ResizeRun positive H growth G remaining state suffix := by
  let oldWord := MachineExpanderTable.oldTableWord G
  let newWord := encodeWords (rotationWords (step G H))
  have copy := copyCountInTime positive H growth
    (boundaryTapes remaining v oldWord suffix) v rfl rfl rfl state
  rw [copyFrame_eq_update] at copy
  let called := MachineExpanderTable.tableInTime positive G H (clearRegister state).1 []
  let returned : State ρ d := (called.finalState, ())
  have eta : ((clearRegister state).1, ()) = clearRegister state := by
    rcases state with ⟨state, extra⟩
    cases extra
    rfl
  have call : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inl (.inr .initialize_)), clearRegister state,
        copyFrame remaining v oldWord suffix⟩
      (some ⟨some (.inr .clearOldTable), returned,
        returnFrame remaining v oldWord newWord suffix⟩)
      ((MachineExpanderTable.timePolynomial d).eval oldWord.length) := by
    simpa only [MachineEmbedding.configuration, MachineEmbedding.label, tableReturn, eta,
      copyFrame, returnFrame, oldWord, newWord, returned] using
      tableExecution positive H growth (extraFrame remaining v suffix) called.execution
  have install := installTableInTime positive H growth
    (returnFrame remaining v oldWord newWord suffix) newWord
    (by rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]; rfl)
    (by rw [returnFrame_eq_cycleTapes, toBool_cycleTapes]; rfl) returned
  rw [installed_returnFrame] at install
  have installRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .clearOldTable), returned, returnFrame remaining v oldWord newWord suffix⟩
      (some ⟨some (.inr (.affine .multiplySize .seed)), clearRegister returned,
        installedFrame remaining v newWord suffix⟩)
      (oldWord.length + 2 * newWord.length + (v + 1) + 4) := by
    simpa only [returnFrame_eq_cycleTapes, toBool_cycleTapes, cycleWords, tableTape,
      encodeWord_length] using install
  have multiply := multiplySizeInTime positive H growth
    (installedFrame remaining v newWord suffix) v rfl rfl rfl (clearRegister returned)
  rw [clearRegister_idempotent, multipliedFrame_eq_update] at multiply
  have clean := cleanupCountersInTime positive H growth
    (multipliedFrame d remaining v newWord suffix) (clearRegister returned)
  rw [clearRegister_idempotent, cleaned_multipliedFrame] at clean
  have cleanRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .drainInputVertex), clearRegister returned,
        multipliedFrame d remaining v newWord suffix⟩
      (some ⟨some (.inr .levelGuard), clearRegister returned,
        boundaryTapes remaining (v * cloudSize d) newWord suffix⟩) (v + 4) := by
    simpa only [multipliedFrame, toBool_cycleTapes, cycleWords, inputVertexTape,
      vertexCountTape, encodeWord_length, Nat.zero_add, Nat.add_assoc] using clean
  let a := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ copy call
  let b := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ a installRun
  let c := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ b multiply
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ c cleanRun
  refine ⟨clearRegister returned, ?_, ?_⟩
  · exact (caller_clearRegister returned).trans
      (called.caller_preserved.trans (caller_clearRegister state))
  · refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
    have bound := all.steps_le_m
    unfold resizeCost
    change _ ≤ (MachineExpanderTable.timePolynomial d).eval oldWord.length +
      6 * v + oldWord.length + 2 * newWord.length + 15
    omega

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

/-- Every body is the already constructed actual resize run. There is no
whole-loop, body-trace, or computational-correctness premise. -/
noncomputable def levelLoopInTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (completed remaining : Nat) (state : State ρ d) (suffix : List Bool) :
    LevelLoopRun positive H growth completed remaining state suffix := by
  induction remaining generalizing completed state with
  | zero =>
      refine ⟨clearRegister state, caller_clearRegister state, ?_⟩
      simpa only [levelLoopCost, levelLoopTapes, familyTapes, Nat.add_zero] using
        familySingleStep_inline_MachineExpanderFamilyLoop _ _ _ (levelGuard_boundary_zeroStep positive H growth
          (vertexCount (degree d) completed) (encodeWords (rotationWords (family H completed)))
          suffix state)
  | succ remaining ih =>
      let cycle := resizeInTime positive H growth (family H completed) remaining
        (clearRegister state) suffix
      let rest := ih (completed + 1) cycle.finalState
      let guard := familySingleStep_inline_MachineExpanderFamilyLoop _ _ _ (levelGuard_boundary_succStep positive H growth
        remaining (vertexCount (degree d) completed)
        (encodeWords (rotationWords (family H completed))) suffix state)
      have cycleRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
          ⟨some (.inr (.affine .copyCount .seed)), clearRegister state,
            levelLoopTapes H completed remaining suffix⟩
          (some ⟨some (.inr .levelGuard), cycle.finalState,
            levelLoopTapes H (completed + 1) remaining suffix⟩)
          (resizeCost (family H completed) H) := cycle.execution
      let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
        _ _ _ _ _ guard cycleRun
      let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
        _ _ _ _ _ first rest.execution
      have index : completed + 1 + remaining = completed + (remaining + 1) := by omega
      refine ⟨rest.finalState, ?_, ?_⟩
      · exact rest.caller_preserved.trans
          (cycle.caller_preserved.trans (caller_clearRegister state))
      · rw [index] at all
        refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
        have bound := all.steps_le_m
        simp only [levelLoopCost]
        omega

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

/-- Complete initialization, actual counted loop, and normalized halt. -/
noncomputable def familyInTime {d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (level : Nat) (state : State ρ d) (suffix : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩)
      (familyBudget H level) := by
  let loop := levelLoopInTime positive H growth 0 level
    (initialState positive H (caller state)) suffix
  have initialRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .initialize_), state, initialTapes level suffix⟩
      (some ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩) 1 :=
    singleFamilyStep_inline_MachineExpanderFamily _ _ _ (initialize_boundaryStep positive H growth level suffix state)
  have finalCaller : caller loop.finalState = caller state := loop.caller_preserved
  have done : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩
      (some ⟨none, initialState positive H (caller state), familyTapes H level suffix⟩) 1 := by
    simpa only [normalizeState, finalCaller] using
      singleFamilyStep_inline_MachineExpanderFamily _ _ _ (doneStep positive H growth (familyTapes H level suffix)
        loop.finalState)
  have loopRun : StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      ⟨some (.inr .levelGuard), initialState positive H (caller state),
        levelLoopTapes H 0 level suffix⟩
      (some ⟨some (.inr .done), loop.finalState, familyTapes H level suffix⟩)
      (levelLoopCost H 0 level) := by simpa only [Nat.zero_add] using loop.execution
  let first := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ initialRun loopRun
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program positive H growth))
    _ _ _ _ _ first done
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
  have bound := all.steps_le_m
  have costEquality := levelLoopCost_zero_start H level
  unfold familyBudget
  omega

/-- At the physically computable padding level, the actual family run has a
fixed polynomial bound in requested unary size. The separate ceiling-power
machine supplies this exact level and preserves the requested size. -/
noncomputable def paddedFamilyInTime {ρ : Type} [Fintype ρ]
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree)
    (requested : Nat) (state : State ρ PCP.Expanders.baseDegree) (suffix : List Bool) :
    StateTransition.EvalsToInTime
      (TM2.step (program baseDegree_positive H baseDegree_cloud_gt_one))
      ⟨some (.inr .initialize_), state,
        initialTapes (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩
      (some ⟨none, initialState baseDegree_positive H (caller state),
        familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) suffix⟩)
      (inputCoefficient * (requested + 1)^5) where
  toEvalsTo := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).toEvalsTo
  steps_le_m := (familyInTime baseDegree_positive H baseDegree_cloud_gt_one
    (PCP.PreprocessingLevels.boundedLevel requested) state suffix).steps_le_m.trans
      (familyBudget_at_boundedLevel_le H requested)

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePaddedExpanderFamilyBounds
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual requested-size to expander-table computation

One finite program physically computes the padding level and then constructs
the complete corresponding rotation table. The level output of the first
phase is the input tape of the second phase. The actual execution preserves
the request, retains the padded size, and has a fixed polynomial time bound
in the unary request length.
-/

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open MachineCloudPadding
open MachineComposition

variable {ρ : Type} [Fintype ρ]

/-- Actual table materialization consumes the level produced by the preceding
phase while retaining the original request and its computed padded size. -/
noncomputable def materializeInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (requested + 1)^5) := by
  let original := MachineExpanderFamily.paddedFamilyInTime H requested state []
  let boolean := MachineAlphabetTransport.executionInTime MachineExpanderFamily.alphabet_eq
    (MachineExpanderFamily.program MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) original
  let framed := MachineStateFrame.frameExecution
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) (false, (none : Option Bool)) boolean
  let placed := liftExecutionInTime (TM2.step (familySource H)) (TM2.step (program H))
    (Placement.configuration familyView familyLabel none (retainedFrame requested))
    (Placement.step_simulation familyTape familyView familyView_left familyView_right
      familyLabel none (retainedFrame requested) (familySource H) (program H)
      (program_family H)) framed
  simpa only [family_initial_configuration, family_final_configuration] using placed

/-- A single concrete finite program takes the original unary request all the
way to the exact forward family table. Both phase executions are supplied by
proved machines; there is no construction or runtime hypothesis. -/
noncomputable def paddedInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨none, finalState H state, finalTapes H requested⟩)
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord requested).length) := by
  let first := ceilingInTime H requested state register
  let second := materializeInTime H requested state
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H))
    _ _ _ _ _ first second
  exact
    { toEvalsTo := all.toEvalsTo
      steps_le_m := all.steps_le_m.trans
        (by simpa only [Nat.add_comm] using
          MachinePaddedExpanderFamilyBounds.combinedCost_le requested) }

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

/-!
# Materializing a cloud rotor inside the regularization machine

Core tape 4 contains the unary cloud size and core tape 7 receives the complete
forward rotor table. The actual family computation runs on private tapes;
three retained unary words are then physically drained. All other core tapes
are preserved and all private tapes are empty on return.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

/-- The actual native family run, including geometric-level computation. -/
noncomputable def familyInTime (H : SmallTable) (k : Nat) (core : CoreTape → List Bool)
    (hinput : core 4 = encodeWord k) (houtput : core 7 = []) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some (.family MachinePaddedExpanderFamily.main), readyState H, frame core⟩
      (some ⟨some .drainPower, readyState H,
        working (resultCore H k core)
          (encodeWord (PCP.PreprocessingLevels.paddedSize k))
          (encodeWord (PCP.PreprocessingLevels.paddedSize k)) (encodeWord 0)⟩)
      (MachinePaddedExpanderFamilyBounds.timePolynomial.eval (encodeWord k).length) := by
  let raw := MachinePaddedExpanderFamily.paddedInTime H k (seedState H) none
  let renamed := MachineStateEquiv.execution stateEquiv
    (MachinePaddedExpanderFamily.program (ρ := Unit) H) raw
  let placed := liftExecutionInTime (TM2.step (sourceProgram H)) (TM2.step (program H))
    (Placement.configuration familyView Label.family (some .drainPower) (frame core))
    (Placement.step_simulation familyTape familyView familyView_left familyView_right
      Label.family (some .drainPower) (frame core) (sourceProgram H) (program H)
      (fun _ => rfl)) renamed
  simpa only [MachineStateEquiv.configuration, Placement.configuration, Placement.label,
    source_initial_state, source_final_state, initial_placement k core hinput houtput,
    final_placement H k core hinput] using placed

/-- Complete clean-frame execution, from the caller's actual unary request.
No callback, table-construction premise, or caller-supplied runtime is assumed. -/
noncomputable def familyCleanInTime (H : SmallTable) (k : Nat)
    (core : CoreTape → List Bool) (hinput : core 4 = encodeWord k)
    (houtput : core 7 = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some .start, state, frame core⟩
      (some ⟨none, readyState H, frame (resultCore H k core)⟩)
      (timePolynomial.eval (encodeWord k).length) := by
  let first := startInTime H core state
  let second := familyInTime H k core hinput houtput
  let third := cleanupInTime H (PCP.PreprocessingLevels.paddedSize k) (resultCore H k core)
  let pair := StateTransition.EvalsToInTime.trans (TM2.step (program H)) _ _ _ _ _ first second
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H)) _ _ _ _ _ pair third
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := ?_ }
  exact all.steps_le_m.trans
    (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using totalBudget_le k)

end MaxCutGames.Foundations.Complexity.MachineRegularFamily

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingWords
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- Per-row serialization agrees with the generic table codec. -/
theorem actualRow_bits (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    encodeWords (GraphTables.rowWords (actualRow t padding tables x p)) =
      PreprocessingPaddingWords.rowBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) (portOrder q p) := by
  simpa only [actualRow, Equiv.symm_apply_apply] using
    PreprocessingPaddingWords.rowBits_flat (ofCloudTables t padding tables)
      (PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p))

/-- Each block uses exactly the port order of the actual stored table. -/
theorem vertexBits_eq (x : Vertex t padding) :
    vertexBits t padding tables x =
      PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) := by
  unfold vertexBits vertexRows
  rw [List.flatMap_append, encodeWords_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeWords_flatMap_inline_PreprocessingRegularWords, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun p : Fin q =>
    encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inl p))))).flatten ++
      encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inr ()))) = _
  simp_rw [actualRow_bits]
  unfold PreprocessingPaddingWords.vertexBits
  rw [List.ofFn_succ_last, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

/-- The whole actual row stream, split into the two executable outer loops. -/
theorem rowsBits_ofCloudTables :
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) =
      (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  rw [PreprocessingPaddingWords.rowsBits_eq_vertices]
  have hblocks :
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables) i) =
      List.ofFn (fun i : Fin (vertexCount t padding) =>
        vertexBits t padding tables ((vertexOrder t padding).symm i)) := by
    apply congrArg List.ofFn
    funext i
    rw [vertexBits_eq, Equiv.apply_symm_apply]
  rw [hblocks, vertexOrder_ofFn, List.flatten_append]
  change (List.ofFn (originalVertexBits t padding tables)).flatten ++
      ((paddingList padding).map (fun z => dummyVertexBits t padding tables z.1 z.2)).flatten = _
  rw [← List.flatMap_def, paddingList_flatMap]

/-- Exact complete codec identity: new headers, original blocks, then dummy blocks. -/
theorem tableBits_ofCloudTables :
    PortTables.tableBits (ofCloudTables t padding tables) =
      encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
        (List.ofFn (originalVertexBits t padding tables)).flatten ++
        (List.ofFn (fun v : Fin t.vertices =>
          (List.ofFn (dummyVertexBits t padding tables v)).flatten)).flatten := by
  change encodeWords (PortTables.tableWords (ofCloudTables t padding tables)) = _
  rw [PortTables.tableWords_eq, encodeWords_append]
  change encodeWords [vertexCount t padding, vertexCount t padding * (q + 1)] ++
    PreprocessingPaddingWords.rowsBits (ofCloudTables t padding tables) = _
  rw [rowsBits_ofCloudTables, List.append_assoc]

end MaxCutGames.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regularized vertex-block execution

The finite internal-port loop invokes the checked row machine for every port in
order. Each invocation restores the shared 27-tape frame. Inherited-row stages
use fixed tape placements and finite state permutations.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

theorem dummyCoreTrace (q : Nat) (positive : 0 < q)
    (labels : MachineRegularDummyRow.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = dummyCoreInstruction q labels exit l)
    (graph : List Bool) (x v i k o m : Nat) (rotor output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[MachineRegularDummyRow.timeBound q x output.length]
      (some ⟨some (labels (.affine .seed)), coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor output [] [] [] [] [] []⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreMemory graph x v i k o m rotor
          (output ++ MachineRegularDummyRow.emittedBits q x) [] [] [] [] [] []⟩ := by
  let state := (ambient, (MachineFixedBlockMap.emptyBuffer 4096,
    (MachineFixedDivMod.residue q positive 0, (false, MachineCloudSelect.Phase.checking))))
  have run := MachineRegularDummyRow.traceAt q id none
    (MachineRegularDummyRow.instruction q id none) (fun _ => rfl) x
    (MachineRegularDummyRow.memory x output) (MachineRegularDummyRow.memory_input x output) state none
  rw [dummyMemory_update] at run
  have placed := MachineCloudPadding.Placement.trace dummyTapes dummyView
    dummyView_left dummyView_right labels exit
    (coreMemory graph x v i k o m rotor output [] [] [] [] [] [])
    (MachineRegularDummyRow.instruction q id none) program code _ _ _ run
  simp only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    dummyFrame] at placed
  have hs : MachineRegularDummyRow.steps q x output =
      MachineRegularDummyRow.timeBound q x output.length := MachineRegularDummyRow.steps_eq q x output
  change (advance (TM2.step program))^[MachineRegularDummyRow.steps q x output] _ = _ at placed
  rw [hs] at placed
  exact placed

theorem dummyTraceAt (q : Nat) (positive : 0 < q)
    (labels : Label q → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : CoreTape => Bool) Λ (CoreState σ q))
    (code : ∀ l, program (labels l) = instruction q positive labels exit l)
    (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (output : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[dummySteps t padding tables v j output.length]
      (some ⟨some (labels (dummyEntry q positive)), coreInitialState q positive ambient,
        coreInputTapes t padding tables v (paddedNew t padding v j) output⟩) =
      some ⟨exit, coreInitialState q positive ambient,
        coreInputTapes t padding tables v (paddedNew t padding v j)
          (output ++ PreprocessingRegularWords.dummyVertexBits t padding tables v j)⟩ := by
  let x := paddedNew t padding v j
  let bits := (List.ofFn (rowBits t padding tables v x)).flatten
  have ports := portTrace q positive (fun l => labels (.dummyPort l))
    (some (labels (.dummy (.affine .seed)))) program
    (fun l => code (.dummyPort l)) t padding tables v x output ambient
  have inherited := dummyCoreTrace q positive (fun l => labels (.dummy l)) exit program
    (fun l => code (.dummy l)) (GraphTables.tableBits t) (vertexOrder t padding x.val).val v.val
    (paddedCloudRank t padding v x).val (cloudSize t v)
    (PreprocessingPaddingOffsets.offset padding v.val) t.darts
    (encodeWords (ExpanderTableWords.rotationWords (tables v))) (output ++ bits) ambient
  have total := joinTrace_inline_MachineRegularVertexBlock ports inherited
  have hbits : PreprocessingRegularWords.dummyVertexBits t padding tables v j =
      bits ++ MachineRegularDummyRow.emittedBits q (vertexOrder t padding x.val).val := by
    have h := vertexBits_split t padding tables v x
    change PreprocessingRegularWords.dummyVertexBits t padding tables v j =
      bits ++ encodeWords (GraphTables.rowWords
        (PreprocessingRegularWords.actualRow t padding tables (.inr ⟨v, j⟩) (.inr ()))) at h
    rw [PreprocessingRegularWords.inherited_dummy_words] at h
    rw [encodeWords_pair_inline_MachineRegularVertexBlock] at h
    rw [show (vertexOrder t padding x.val).val =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val from
      PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v j]
    simpa only [MachineRegularDummyRow.emittedBits, MachineRegularDummyRow.reverseIndex,
      MachineDummyRows.rowBits, MachineDummyRows.trueBits, List.append_assoc] using h
  rw [hbits]
  simp only [dummySteps, portEntry, dite_eq_left positive, dummyEntry,
    List.length_append, List.append_assoc, x, bits] at total ⊢
  convert total using 1 <;> rfl

theorem dummySteps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (j : Fin (padding v)) (outputLength : Nat) :
    dummySteps t padding tables v j outputLength ≤
      dummyTimeBound q (GraphTables.tableBits t).length
        (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
        (vertexOrder t padding (.inr ⟨v, j⟩)).val v.val
        (paddedCloudRank t padding v (paddedNew t padding v j)).val
        (cloudSize t v) (PreprocessingPaddingOffsets.offset padding v.val)
        t.darts outputLength (vertexCount t padding) := by
  have hp := portSteps_le q positive t padding tables v (paddedNew t padding v j) outputLength q le_rfl
  have hl := allRowBits_length_le t padding tables v (paddedNew t padding v j)
  unfold dummySteps dummyTimeBound portTimeBound MachineRegularDummyRow.timeBound
  have hx : (paddedNew t padding v j).val = Sum.inr ⟨v, j⟩ := rfl
  rw [hx] at hp
  omega

end MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOriginalBody
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One actual original-vertex body of regularization

The finite code composes physical metadata preparation, expander-family
materialization, all vertex rows, and seven metadata drain loops. The outer
loop owns the global vertex counter and keeps it unchanged during this body.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

def clearSource (source : Tape) : Unit → TM2.Stmt Alphabet Unit MetaState :=
  fun _ => MachineDrain.drain source () none

def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .metadata l => Lift.statement metadataTape Label.metadata (some (.family .start))
      metadataStates (MachineRegularMetadata.program l)
  | .family l => Lift.statement familyTape Label.family
      (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
      familyStates (MachineRegularFamily.program H l)
  | .vertex l => Lift.statement Sum.inl Label.vertex (clearEntry 0)
      vertexStates (vertexSource l)
  | .clear i => Lift.statement id (fun _ : Unit => .clear i) (clearEntry (i.val + 1))
      metadataStates (clearSource (clearTape i) ())

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

/-- Genuine metadata trace transported with all other finite registers and
private family tapes preserved. -/
theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularMetadata.totalTime t e]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H (some (.family .start)) (metadataData t e output)) := by
  have raw := MachineRegularMetadata.originalTrace t e (initialData t e output)
    rfl rfl rfl rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.family .start)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) (frame (initialData t e output))
    MachineRegularMetadata.program (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    metadataStates, Equiv.coe_fn_mk, entry] using placed

noncomputable def familyExecution (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) :=
  MachineRegularFamily.familyCleanInTime H (cloudSize t t.rows[e].tail)
    (coreFrame (metadataData t e output)) rfl rfl (MachineRegularFamily.readyState H)

noncomputable def familySteps (H : BaseTable) (t : GraphTables.Table)
    (e : Fin t.darts) (output : List Bool) : Nat :=
  (familyExecution H t e output).steps

/-- Family work is performed on its physical tapes and produces the rotor
from the previously computed unary cloud size. -/
theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t e output]
      (some (cfg H (some (.family .start)) (metadataData t e output))) =
      some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output)) := by
  have raw := (familyExecution H t e output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some (.vertex (MachineRegularVertexBlock.originalEntry internalDegree degree_positive)))
    familyStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      ((((), false), none) : MetaState)) (frame (metadataData t e output))
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familyData, familySteps, cfg, readyState,
    familyStates, Equiv.prodComm_apply, Prod.swap_prod_mk] using placed

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length + 1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val + 1), readyState H, Function.update base (clearTape i) []⟩ := by
  have raw := MachineDrain.drainTrace (clearTape i) () none (clearSource (clearTape i)) rfl
    base (base (clearTape i)) ((), false) none
  simp only [Function.update_eq_self] at raw
  have placed := Lift.trace id some (fun _ => rfl)
    (fun j k h => (Option.some.inj h).symm)
    (fun _ : Unit => Label.clear i) (clearEntry (i.val + 1)) metadataStates
    (MachineRegularInternalRow.coreInitialState internalDegree degree_positive (),
      MachineRegularFamily.readyState H) base (clearSource (clearTape i)) (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    identityPlacement_inline_MachineRegularOriginalBody, metadataStates, Equiv.coe_fn_mk, readyState] using placed

theorem clearPrefixTrace (H : BaseTable) (base : Tape → List Bool)
    (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[clearSteps base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, clearMemory base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k, h⟩ (clearMemory base k)
    have atEntry : clearEntry k = some (.clear ⟨k, h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [clearSteps, clearMemory, dite_eq_left h] using joinTrace_inline_MachineRegularOriginalBody first second

theorem clearTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[clearSteps base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, clearMemory base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using clearPrefixTrace H base 7 le_rfl

/-- Every internal port and the inherited original row are emitted by their
actual checked row machines, using the rotor just materialized on tape 7. -/
theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[vertexSteps H t e output]
      (some (cfg H (some (.vertex (MachineRegularVertexBlock.originalEntry
        internalDegree degree_positive))) (familyData H t e output))) =
      some (cfg H (clearEntry 0) (emittedData H t e output)) := by
  have raw := MachineRegularVertexBlock.originalTraceAt internalDegree degree_positive id none
    vertexSource (fun _ => rfl) t (padding t) (familyCloudTable H t) e output ()
  have finished := coreFrame_eq H t e (output ++ emittedBits H t e)
  simp only [emittedBits] at finished
  rw [← coreFrame_eq H t e output, ← finished] at raw
  have placed := Lift.trace Sum.inl vertexView vertexView_left vertexView_right
    Label.vertex (clearEntry 0) vertexStates
    (((((), false), none) : MetaState), MachineRegularFamily.readyState H)
    (frame (familyData H t e output)) vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    emittedData_eq, cfg, readyState, vertexStates, Equiv.prodAssoc_symm_apply,
    vertexSteps, emittedBits, id_eq] using placed

noncomputable def totalSteps (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : Nat :=
  MachineRegularMetadata.totalTime t e + familySteps H t e output + vertexSteps H t e output +
    clearSteps (frame (emittedData H t e output)) 7

/-- Complete execution of one original-vertex iteration, including physical
cleanup of all seven retained metadata fields. The global index is preserved. -/
theorem originalTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t e output]
      (some (cfg H (some entry) (initialData t e output))) =
      some (cfg H none (initialData t e (output ++ emittedBits H t e))) := by
  have metadata := metadataTrace H t e output
  have family := familyTrace H t e output
  have vertex := vertexTrace H t e output
  have cleanup := clearTrace H (frame (emittedData H t e output))
  have final : clearMemory (frame (emittedData H t e output)) 7 =
      frame (initialData t e (output ++ emittedBits H t e)) := by
    rw [clearFrame]
    rfl
  rw [final] at cleanup
  exact joinTrace_inline_MachineRegularOriginalBody (joinTrace_inline_MachineRegularOriginalBody (joinTrace_inline_MachineRegularOriginalBody metadata family) vertex) cleanup

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOwnerProgram
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

/-- Actual cloud metadata, with every outer register and tape preserved. -/
theorem metadataTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[MachineCloudPadding.totalTime t v]
      (some (cfg H (some entry) (initialData t v output))) =
      some (cfg H (some (.copyCount .seed)) (metadataData t v output)) := by
  have raw := MachineRegularMetadata.cloudTrace t v (initialData t v output)
    rfl rfl rfl rfl rfl () none
  have placed := Lift.trace metadataTape metadataView metadataView_left metadataView_right
    Label.metadata (some (.copyCount .seed)) metadataStates
    ((MachineRegularInternalRow.coreInitialState internalDegree
      MachineRegularOriginalBody.degree_positive (), MachineRegularFamily.readyState H), none)
    (frame (initialData t v output)) MachineRegularMetadata.program (program H)
    (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    metadataPlacement, MachineRegularMetadata.cfg, metadataData, cfg, readyState,
    MachineRegularOriginalBody.readyState, metadataStates, Equiv.coe_fn_mk, entry] using placed

noncomputable def ownerTime (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : Nat :=
  preSteps t v + 1 + (if padding t v = 0 then 0 else
    MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length +
      loopSteps H t v output (padding t v) le_rfl + 1) + cleanupCost H t v output

noncomputable def familyExecution (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) :=
  MachineRegularFamily.familyCleanInTime H (cloudSize t v)
    (MachineRegularOriginalBody.coreFrame (seededData t v output)) rfl rfl
    (MachineRegularFamily.readyState H)

noncomputable def familySteps (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) : Nat :=
  (familyExecution H t v output).steps

theorem familyTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[familySteps H t v output]
      (some ⟨some (.family .start), readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩) =
      some ⟨some .loop, readyState H, loopFrame H t v output 0⟩ := by
  have raw := (familyExecution H t v output).evals_in_steps
  have placed := Lift.trace familyTape familyView familyView_left familyView_right
    Label.family (some .loop) familyStates
    ((MachineRegularInternalRow.coreInitialState internalDegree
      MachineRegularOriginalBody.degree_positive (), ((((), false), none) : MetaState)), none)
    (working (seededData t v output) (encodeWord (padding t v)) [])
    (MachineRegularFamily.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label,
    familyPlacement, familyResultPlacement, familySteps, readyState,
    MachineRegularOriginalBody.readyState, familyStates, Equiv.coe_fn_mk,
    loopFrame, loopData, vertexData, blocksPrefix_zero, List.append_nil, Nat.sub_zero,
    Nat.add_zero, seededData, metadataData, MachineRegularMetadata.cloudData,
    initialData] using placed

/-- A complete actual dummy vertex block, with the owner's fuel left untouched. -/
theorem vertexTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (output fuel : List Bool) :
    (advance (TM2.step (program H)))^[
        MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v j output.length]
      (some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
        MachineRegularOriginalBody.degree_positive)), readyState H,
        working (vertexData H t v j.val output) fuel []⟩) =
      some ⟨some .bump, readyState H,
        working (vertexData H t v j.val (output ++ dummyBits H t v j)) fuel []⟩ := by
  have raw := MachineRegularVertexBlock.dummyTraceAt internalDegree
    MachineRegularOriginalBody.degree_positive id none MachineRegularOriginalBody.vertexSource
    (fun _ => rfl) t (padding t) (familyCloudTable H t) v j output ()
  have finished := coreFrame_eq H t v j (output ++ dummyBits H t v j)
  simp only [dummyBits] at finished
  rw [← coreFrame_eq H t v j output, ← finished] at raw
  have placed := Lift.trace core vertexView vertexView_left vertexView_right
    Label.vertex (some .bump) vertexStates
    ((((((), false), none) : MetaState), MachineRegularFamily.readyState H), none)
    (working (vertexData H t v j.val output) fuel [])
    MachineRegularOriginalBody.vertexSource (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, vertexPlacement,
    readyState, MachineRegularOriginalBody.readyState, vertexStates, Equiv.coe_fn_mk,
    dummyBits, id_eq] using placed

theorem loopPrefixTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) (hn : n ≤ padding t v) :
    (advance (TM2.step (program H)))^[loopSteps H t v output n hn]
      (some ⟨some .loop, readyState H, loopFrame H t v output 0⟩) =
      some ⟨some .loop, readyState H, loopFrame H t v output n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : n < padding t v := by omega
      have first := ih (by omega)
      have hremaining : padding t v - n = (padding t v - (n + 1)) + 1 := by omega
      have guard := loopPositiveStep H (loopData H t v output n) (padding t v - (n + 1))
      rw [← hremaining] at guard
      have guardRun : (advance (TM2.step (program H)))^[1]
          (some ⟨some .loop, readyState H, loopFrame H t v output n⟩) =
          some ⟨some (.vertex (MachineRegularVertexBlock.dummyEntry internalDegree
            MachineRegularOriginalBody.degree_positive)), readyState H,
            working (loopData H t v output n) (encodeWord (padding t v - (n + 1))) []⟩ := oneStep_inline_MachineRegularOwnerBody guard
      have vertex := vertexTrace H t v ⟨n, h⟩
        (output ++ blocksPrefix (dummyBits H t v) n) (encodeWord (padding t v - (n + 1)))
      have bump := bumpStep H t v n
        ((output ++ blocksPrefix (dummyBits H t v) n) ++ dummyBits H t v ⟨n, h⟩)
        (encodeWord (padding t v - (n + 1)))
      have bumpRun := oneStep_inline_MachineRegularOwnerBody bump
      have all := joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody first guardRun) vertex) bumpRun
      simpa only [loopSteps, loopFrame, loopData, blocksPrefix_succ _ n h,
        List.append_assoc, Nat.add_assoc] using all

theorem preparationTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[preSteps t v]
      (some (cfg H (some entry) (initialData t v output))) =
      some ⟨some .guard, readyState H,
        working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
  joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody (metadataTrace H t v output) (copyCountTrace H t v output))
    (copyFuelTrace H t v output)

theorem loopTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[loopSteps H t v output (padding t v) le_rfl + 1]
      (some ⟨some .loop, readyState H, loopFrame H t v output 0⟩) =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩ := by
  have first := loopPrefixTrace H t v output (padding t v) le_rfl
  have last : (advance (TM2.step (program H)))^[1]
      (some ⟨some .loop, readyState H, loopFrame H t v output (padding t v)⟩) =
      some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
        loopFrame H t v output (padding t v)⟩ := by
    simpa only [loopFrame, Nat.sub_self] using
      oneStep_inline_MachineRegularOwnerBody (loopZeroStep H (loopData H t v output (padding t v)))
  exact joinTrace_inline_MachineRegularOwnerBody first last

/-- Actual complete owner execution, including the genuinely empty padding case.
The bound is assembled from proven component bounds; its family term is not
used as an exact number of transitions. -/
noncomputable def ownerInTime (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (cfg H (some entry) (initialData t v output))
      (some (cfg H none (finalData H t v output))) (ownerTime H t v output) := by
  have prepared := preparationTrace H t v output
  by_cases hp : padding t v = 0
  · have gate : (advance (TM2.step (program H)))^[1]
        (some ⟨some .guard, readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩) =
        some ⟨some (.cleanup MachineRegularOwnerCleanup.entry), readyState H,
          working (seededData t v output) (encodeWord 0) []⟩ := by
      simpa only [hp] using oneStep_inline_MachineRegularOwnerBody (guardZeroStep H (seededData t v output))
    have all := joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody prepared gate) (cleanupZeroTrace H t v output hp)
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    simp only [ownerTime, cleanupCost, ite_eq_left hp, Nat.add_zero, le_refl]
  · have gate : (advance (TM2.step (program H)))^[1]
        (some ⟨some .guard, readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩) =
        some ⟨some (.family .start), readyState H,
          working (seededData t v output) (encodeWord (padding t v)) []⟩ :=
      oneStep_inline_MachineRegularOwnerBody (guardPositiveStep H (seededData t v output) (padding t v) (Nat.pos_of_ne_zero hp))
    have all := joinTrace_inline_MachineRegularOwnerBody
      (joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody (joinTrace_inline_MachineRegularOwnerBody prepared gate) (familyTrace H t v output))
        (loopTrace H t v output)) (cleanupLoopTrace H t v output)
    refine { steps := _, evals_in_steps := all, steps_le_m := ?_ }
    have hb : familySteps H t v output ≤
        MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length :=
      (familyExecution H t v output).steps_le_m
    simp only [ownerTime, cleanupCost, ite_eq_right hp]
    omega

noncomputable def totalSteps (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (output : List Bool) : Nat := (ownerInTime H t v output).steps

theorem ownerTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    (advance (TM2.step (program H)))^[totalSteps H t v output]
      (some (cfg H (some entry) (initialData t v output))) =
      some (cfg H none (finalData H t v output)) := (ownerInTime H t v output).evals_in_steps

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) : totalSteps H t v output ≤ ownerTime H t v output :=
  (ownerInTime H t v output).steps_le_m

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open MaxCutGames.Foundations.Complexity
open scoped BigOperators

theorem regularBits_le (H : BaseTable) (t : GraphTables.Table) :
    (PortTables.tableBits (regularize H t)).length ≤
      regularPolynomial.eval (inputLength t) := by
  have hv : (PortTables.graphTable (regularize H t)).vertices ≤
      ExpanderFamily.growth * inputLength t := regularVertices_le_input t
  have he : (PortTables.graphTable (regularize H t)).darts ≤
      (ExpanderFamily.growth * (internalDegree + 1)) * inputLength t := by
    change vertexCount t (padding t) * (internalDegree + 1) ≤ _
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * (internalDegree + 1) :=
        Nat.mul_le_mul_right _ hv
      _ = _ := by ac_rfl
  exact tableBits_le_of_counts (PortTables.graphTable (regularize H t)) _ _ _ hv he

end MaxCutGames.Foundations.PCP.PreprocessingMachineBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Basic
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

namespace Header

variable {σ : Type}

/-- Both original header numbers are produced by physical preserving lookups. -/
theorem readTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[readTime t]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ := by
  have hi : (advance (TM2.step (program q)))^[1]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ :=
    initStep q _ _ ambient register
  have hn := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .vertices)
    (lookupSlots_injective .vertices) (Label.lookup .vertices) (some Label.seedM)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 0 t.vertices (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) register
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hn
  have hs : (advance (TM2.step (program q)))^[1]
      (some ⟨some .seedM, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
          (encodeWord 1) [] [] [] [] [] output⟩ :=
    seedMStep q _ _ _ ambient none
  have hm := MachinePreservingLookupClean.traceAt_fromTapes (lookupSlots .darts)
    (lookupSlots_injective .darts) (Label.lookup .darts) (some Label.clearIndex)
    (program q) (fun _ => rfl)
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] []
      (encodeWord 1) [] [] [] [] [] output)
    (GraphTables.tableWords t) rfl rfl 1 t.darts (by simp [GraphTables.tableWords]) []
    (by simp [lookupSlots]) (by simp [lookupSlots]) (ambient, false) none
  simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, lookupSlots, fieldTape] at hm
  have hc : (advance (TM2.step (program q)))^[1]
      (some ⟨some .clearIndex, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) (encodeWord 0) [] [] [] [] [] output⟩) =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩ :=
    clearIndexStep q _ _ _ _ ambient none
  exact appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ hi hn) hs) hm) hc

theorem trace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[totalTime q t output]
      (some ⟨some .init, ((ambient, false), register),
        frame (GraphTables.tableBits t) [] [] [] [] [] [] [] [] [] [] [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ :=
  appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (readTrace q t output ambient register)
    (prefixTrace q t output ambient none)) (computeTrace q t output ambient none))
      (emitTrace q t output ambient none)

theorem totalTime_le (q : Nat) (t : GraphTables.Table) (output : List Bool) :
    totalTime q t output ≤ (timePolynomial q).eval ((GraphTables.tableBits t).length + output.length) := by
  let L := (GraphTables.tableBits t).length + output.length
  have hT : (GraphTables.tableBits t).length ≤ L := by unfold L; omega
  have hO : output.length ≤ L := by unfold L; omega
  have hn := (GraphTables.vertices_le_tableBits_length t).trans hT
  have hm := (GraphTables.darts_le_tableBits_length t).trans hT
  have hN : vertexTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.regularVertices_le_input t).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hS : paddingTotal t ≤ ExpanderFamily.growth * L :=
    (PreprocessingMachineBounds.prefix_le_input t t.vertices).trans
      (Nat.mul_le_mul_left ExpanderFamily.growth hT)
  have hR : dartTotal q t ≤ (ExpanderFamily.growth * (q + 1)) * L := by
    calc
      _ ≤ (ExpanderFamily.growth * L) * (q + 1) := Nat.mul_le_mul_right (q + 1) hN
      _ = _ := by ac_rfl
  have hr0 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 0 t.vertices
    (by simp [GraphTables.tableWords])
  have hr1 := MachinePreservingLookupClean.steps_le (GraphTables.tableWords t) 1 t.darts
    (by simp [GraphTables.tableWords])
  have hread : readTime t ≤ 12 * L + 11 := by
    change _ ≤ 6 * (GraphTables.tableBits t).length + 4 at hr0 hr1
    unfold readTime
    omega
  have hprefixInput : MachineCloudPrefix.inputLength t t.vertices [] ≤ 2 * L + 1 := by
    simp only [MachineCloudPrefix.inputLength, List.append_nil, encodeWord_length]
    omega
  have hp := (MachineCloudPrefix.totalTime_le t t.vertices (Nat.le_refl _) []).trans
    (natPolynomial_eval_mono MachineCloudPrefix.timePolynomial hprefixInput)
  have harith : readTime t + computeTime t + emitTime q t output ≤
      (arithmeticPolynomial q).eval L := by
    simp only [arithmeticPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
    unfold computeTime emitTime
    rw [headerBits_length]
    omega
  have htotal := Nat.add_le_add hp harith
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one,
    L, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htotal

end Header

namespace Top

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕
      ((MachineCloudPrefix.Tape ⊕ Header.Extra) ⊕ Fin 4))
  infer_instance

def headerView : Tape → Option Header.Tape
  | .inl (.inl i) => match i.val with
    | 0 => some Header.tableTape
    | 6 => some Header.mTape
    | 8 => some Header.outputTape
    | _ => none
  | .inl (.inr _) => none
  | .inr (.inl k) =>
      if k = Header.tableTape ∨ k = Header.mTape ∨ k = Header.outputTape then none else some k
  | .inr (.inr _) => none

theorem headerView_left (k : Header.Tape) : headerView (headerTape k) = some k := by
  by_cases ht : k = Header.tableTape
  · subst k; rfl
  by_cases hm : k = Header.mTape
  · subst k; rfl
  by_cases ho : k = Header.outputTape
  · subst k; rfl
  simp [headerTape, headerView, ht, hm, ho]

theorem headerView_right (j : Tape) (k : Header.Tape)
    (h : headerView j = some k) : headerTape k = j := by
  cases j with
  | inl j =>
    cases j with
    | inl i =>
      fin_cases i <;> simp_all [headerView] <;> subst k <;> rfl
    | inr e => cases h
  | inr j =>
    cases j with
    | inl i =>
      by_cases hi : i = Header.tableTape ∨ i = Header.mTape ∨ i = Header.outputTape
      · simp [headerView, hi] at h
      · have hik : i = k := by simpa [headerView, hi] using h
        subst k
        simp only [not_or] at hi
        simp [headerTape, hi.1, hi.2.1, hi.2.2]
    | inr i => cases h

def bodyView : Tape → Option Body
  | .inl k => some k
  | .inr _ => none

theorem bodyView_left (k : Body) : bodyView (.inl k) = some k := rfl
theorem bodyView_right (j : Tape) (k : Body)
    (h : bodyView j = some k) : Sum.inl k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j => cases h

def ownerTape : MachineRegularOwnerBody.Tape → Tape
  | .inl k => .inl k
  | .inr i => if i.val = 0 then dummyFuel else scratch

theorem ownerView_left (k : MachineRegularOwnerBody.Tape) :
    ownerView (ownerTape k) = some k := by
  cases k with
  | inl k => rfl
  | inr i => fin_cases i <;> rfl

theorem ownerView_right (j : Tape) (k : MachineRegularOwnerBody.Tape)
    (h : ownerView j = some k) : ownerTape k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j =>
    cases j with
    | inl j => cases h
    | inr i => fin_cases i <;> simp_all [ownerView] <;> subst k <;> rfl

def copySource : CopyPhase → Tape
  | .old => coreTape 6
  | .owner => headerTape Header.nTape
def copyTarget : CopyPhase → Tape
  | .old => oldFuel
  | .owner => ownerFuel

inductive Label
  | header (l : Header.Label)
  | oldSeed
  | copyFirst (phase : CopyPhase)
  | copySecond (phase : CopyPhase)
  | oldGuard
  | oldBody (l : MachineRegularOriginalBody.Label)
  | oldIncrement
  | ownerSeed
  | ownerGuard
  | ownerBody (l : MachineRegularOwnerBody.Label)
  | ownerIncrement
  | clear (i : Fin 7)
  deriving DecidableEq, Fintype

def copyExit : CopyPhase → Label
  | .old => .oldGuard
  | .owner => .ownerGuard

def clearTape : Fin 7 → Tape :=
  ![coreTape 1, coreTape 2, coreTape 5, coreTape 6,
    headerTape Header.nTape, headerTape Header.verticesTape, headerTape Header.dartsTape]

def clearEntry (k : Nat) : Option Label :=
  if h : k < 7 then some (.clear ⟨k, h⟩) else none

/-- All graph-dependent loop counts remain on tapes. The code contains only
the fixed expander base and the finite subprogram labels. -/
def program (H : BaseTable) : Label → TM2.Stmt Alphabet Label State
  | .header l => Lift.statement headerTape Label.header (some .oldSeed) headerStates
      (Header.program PreprocessingRegularTables.internalDegree l)
  | .oldSeed => .push (coreTape 1) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.old)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratch id false
      (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratch (copySource phase) (copyTarget phase) false
      (.copySecond phase) (some (copyExit phase))
  | .oldGuard => Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry) (some Label.ownerSeed)
  | .oldBody l => Lift.statement Sum.inl Label.oldBody (some .oldIncrement) (Equiv.refl _)
      (MachineRegularOriginalBody.program H l)
  | .oldIncrement => Fuel.increment (coreTape 1) Label.oldGuard
  | .ownerSeed => .push (coreTape 2) (fun _ => false)
      (.push (coreTape 5) (fun _ => false) (.goto fun _ => Label.copyFirst CopyPhase.owner))
  | .ownerGuard => Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry) (clearEntry 0)
  | .ownerBody l => MachineCloudPadding.Placement.statement ownerTape Label.ownerBody
      (some .ownerIncrement) (MachineRegularOwnerBody.program H l)
  | .ownerIncrement => Fuel.increment (coreTape 2) Label.ownerGuard
  | .clear i => MachineDrain.drain (clearTape i) (.clear i) (clearEntry (i.val + 1))

def machine (H : BaseTable) : FinTM2 where
  K := Tape
  k₀ := coreTape 0
  k₁ := coreTape 8
  Γ _ := Bool
  Λ := Label
  main := .header .init
  σ := State
  initialState := readyState H
  m := program H

def cfg (H : BaseTable) (label : Option Label) (data : Data)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data header counters⟩

theorem bodyPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes bodyView (MachineRegularOriginalBody.frame data)
      (frame extra header counters) = frame data header counters := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j <;> rfl

theorem headerPlacement (data : Data) (t n m N R output : List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes headerView
      (Header.frame t n [] [] [] m [] [] [] N R [] output)
      (frame data (fun _ => []) counters) =
      frame { data with table := t, darts := m, output := output } (headerAux n N R) counters := by
  funext j
  cases j with
  | inl j =>
    cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j =>
    cases j with
    | inl k =>
      cases k with
      | inl k =>
        cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => rfl

end Top
end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularBounds
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual output prefixes used by the regularization loops.
The bounds include the stored headers and all earlier original/owner blocks.
They concern actual serialized words; machine executions are proved separately. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open MaxCutGames.Foundations.Complexity
open scoped BigOperators

def ownerBits (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) : List Bool :=
  (List.ofFn (dummyVertexBits t p tables v)).flatten

def originalPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ blocksPrefix (originalVertexBits t p tables) k

def ownerPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ (List.ofFn (originalVertexBits t p tables)).flatten ++
    blocksPrefix (ownerBits t p tables) k

def dummyPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (v : Fin t.vertices) (k : Nat) : List Bool :=
  ownerPrefix t p tables v.val ++ blocksPrefix (dummyVertexBits t p tables v) k

variable (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)

theorem originalPrefix_length_le (k : Nat) :
    (originalPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (originalVertexBits t p tables) k
  rw [tableBits_ofCloudTables]
  simp only [originalPrefix, header, List.length_append]
  omega

theorem ownerPrefix_length_le (k : Nat) :
    (ownerPrefix t p tables k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have h := blocksPrefix_length_le (ownerBits t p tables) k
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  rw [tableBits_ofCloudTables]
  simp only [ownerPrefix, header, List.length_append] at *
  simp only [he] at *
  omega

theorem dummyPrefix_length_le (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t p tables v k).length ≤
      (PortTables.tableBits (ofCloudTables t p tables)).length := by
  have hi := blocksPrefix_length_le (dummyVertexBits t p tables v) k
  have ho := blocksPrefix_length_le (ownerBits t p tables) (v.val + 1)
  rw [blocksPrefix_succ _ _ v.isLt] at ho
  have he : ownerBits t p tables =
      (fun v => (List.ofFn (dummyVertexBits t p tables v)).flatten) := rfl
  simp only [Fin.eta] at ho
  rw [tableBits_ofCloudTables]
  simp only [dummyPrefix, ownerPrefix, header, ownerBits, List.length_append] at *
  simp only [he] at *
  omega

theorem regular_originalPrefix_le (H : BaseTable) (k : Nat) :
    (originalPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (originalPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_ownerPrefix_le (H : BaseTable) (k : Nat) :
    (ownerPrefix t (padding t) (familyCloudTable H t) k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (ownerPrefix_length_le t (padding t) (familyCloudTable H t) k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

theorem regular_dummyPrefix_le (H : BaseTable) (v : Fin t.vertices) (k : Nat) :
    (dummyPrefix t (padding t) (familyCloudTable H t) v k).length ≤
      PreprocessingMachineBounds.regularPolynomial.eval
        (PreprocessingMachineBounds.inputLength t) :=
  (dummyPrefix_length_le t (padding t) (familyCloudTable H t) v k).trans
    (PreprocessingMachineBounds.regularBits_le H t)

end MaxCutGames.Foundations.PCP.PreprocessingRegularBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_InputData
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable
open Turing MachineComposition
open MaxCutGames.Foundations.PCP

namespace Top

def inputData (t : GraphTables.Table) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := []
  owner := []
  localRank := []
  count := []
  offset := []
  darts := []
  rotor := []
  output := output
  padding := []
  level := []

def headerData (t : GraphTables.Table) (output : List Bool) : Data :=
  { inputData t output with darts := encodeWord t.darts }

def headerStacks (t : GraphTables.Table) : Header.Tape → List Bool :=
  headerAux (encodeWord t.vertices) (encodeWord (Header.vertexTotal t))
    (encodeWord (Header.dartTotal PreprocessingRegularTables.internalDegree t))

theorem headerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t output]
      (some (cfg H (some (.header .init)) (inputData t output) (fun _ => []) counters)) =
      some (cfg H (some .oldSeed)
        (headerData t (output ++ Header.headerBits PreprocessingRegularTables.internalDegree t))
        (headerStacks t) counters) := by
  have raw := Header.trace PreprocessingRegularTables.internalDegree t output () none
  have placed := Lift.trace headerTape headerView headerView_left headerView_right
    Label.header (some .oldSeed) headerStates
    (MachineRegularInternalRow.coreInitialState PreprocessingRegularTables.internalDegree
      MachineRegularOriginalBody.degree_positive (), (MachineRegularFamily.readyState H, none))
    (frame (inputData t output) (fun _ => []) counters)
    (Header.program PreprocessingRegularTables.internalDegree) (program H) (fun _ => rfl)
    _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, headerPlacement,
    headerAux_empty, cfg, readyState, MachineRegularOriginalBody.readyState, headerStates,
    Equiv.coe_fn_mk, headerData, inputData, headerStacks] using placed

def oldData (t : GraphTables.Table) (index : Nat) (output : List Bool) : Data :=
  { headerData t output with globalIndex := encodeWord index }

theorem originalData_eq (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) :
    MachineRegularOriginalBody.initialData t e output = oldData t e.val output := rfl

/-- The actual old-vertex body is transported with all outer counters and
header words untouched. No body-execution hypothesis occurs in this lemma. -/
theorem oldBodyTrace (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOriginalBody.totalSteps H t e output]
      (some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry))
        (oldData t e.val output) header counters)) =
      some (cfg H (some .oldIncrement)
        (oldData t e.val (output ++ MachineRegularOriginalBody.emittedBits H t e)) header counters) := by
  have raw := MachineRegularOriginalBody.originalTrace H t e output
  have placed := Lift.trace Sum.inl bodyView bodyView_left bodyView_right Label.oldBody
    (some .oldIncrement) (Equiv.refl _) none
    (frame (oldData t e.val output) header counters)
    (MachineRegularOriginalBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [Lift.configuration, MachineCloudPadding.Placement.label, bodyPlacement,
    MachineRegularOriginalBody.cfg, originalData_eq, cfg, readyState, Equiv.refl_apply] using placed

theorem oldGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header
        (counterStacks (encodeWord (remaining + 1)) [] [] []))) =
      some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry)) data header
        (counterStacks (encodeWord remaining) [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_oldFuel]
  rfl

theorem oldGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header (counterStacks (encodeWord 0) [] [] []))) =
      some (cfg H (some Label.ownerSeed) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_oldFuel]
  rfl

theorem oldIncrementStep (H : BaseTable) (t : GraphTables.Table) (index : Nat)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldIncrement) (oldData t index output) header counters)) =
      some (cfg H (some .oldGuard) (oldData t (index + 1) output) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 1) Label.oldGuard)
    (readyState H) (frame (oldData t index output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.oldGuard, readyState H,
    Function.update (frame (oldData t index output) header counters) (coreTape 1)
      (true :: encodeWord index)⟩ : TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  simp only [cfg, oldData, encodeWord, List.replicate_succ, List.cons_append]

def oldPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) : List Bool :=
  PreprocessingRegularLoopWords.blocksPrefix (MachineRegularOriginalBody.emittedBits H t) k

noncomputable def oldElapsed (H : BaseTable) (t : GraphTables.Table) (output : List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => oldElapsed H t output k +
      if h : k < t.darts then
        1 + MachineRegularOriginalBody.totalSteps H t ⟨k,h⟩ (output ++ oldPrefix H t k) + 1
      else 0

/-- Each actual fuel/body/increment segment appends exactly the next original
vertex block. This induction is over a specification index, not a register. -/
theorem oldPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.darts →
    (advance (TM2.step (program H)))^[oldElapsed H t output k]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t k (output ++ oldPrefix H t k)) header
        (counterStacks (encodeWord (t.darts-k)) [] [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [oldElapsed, oldPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.darts := by omega
    have hremaining : t.darts-k = (t.darts-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := oldGuardStep H (oldData t k (output ++ oldPrefix H t k)) header
      (t.darts-(k+1))
    rw [← hremaining] at guard
    have body := oldBodyTrace H t ⟨k,hlt⟩ (output ++ oldPrefix H t k) header
      (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have increment := oldIncrementStep H t k
      ((output ++ oldPrefix H t k) ++ MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩)
      header (counterStacks (encodeWord (t.darts-(k+1))) [] [] [])
    have combined := joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOriginalBody.emittedBits H t) k hlt
    change oldPrefix H t (k+1) = oldPrefix H t k ++
      MachineRegularOriginalBody.emittedBits H t ⟨k,hlt⟩ at bits
    simpa only [oldElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem oldLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[oldElapsed H t output t.darts + 1]
      (some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := oldPrefixTrace H t output header t.darts (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_inline_MachineRegularTable prefixRun (oldGuardExit H _ header)

theorem oldSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldSeed) (headerData t output) header counters)) =
      some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header counters) := by
  change some (TM2.stepAux (.push (coreTape 1) (fun _ => false)
    (.goto fun _ => Label.copyFirst CopyPhase.old)) (readyState H) (frame (headerData t output) header counters)) = _
  change some (⟨some (Label.copyFirst CopyPhase.old), readyState H,
    Function.update (frame (headerData t output) header counters) (coreTape 1) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_global]
  rfl

theorem copyOldTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[2*(t.darts+2)]
      (some (cfg H (some (.copyFirst .old)) (oldData t 0 output) header
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldGuard) (oldData t 0 output) header
        (counterStacks (encodeWord t.darts) [] [] [])) := by
  have h := MachineCopy.copyTrace (coreTape 6) oldFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .old) (.copySecond .old)
    (some .oldGuard) (program H) rfl rfl
    (frame (oldData t 0 output) header (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [frame_darts, oldData, headerData, inputData, encodeWord_length,
    frame_oldFuel, List.append_nil, update_frame_oldFuel, cfg, readyState, Nat.add_assoc] using h

theorem oldStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.darts+2)+(oldElapsed H t output t.darts+1)]
      (some (cfg H (some .oldSeed) (headerData t output) header (counterStacks [] [] [] []))) =
      some (cfg H (some Label.ownerSeed)
        (oldData t t.darts (output ++ oldPrefix H t t.darts)) header
        (counterStacks [] [] [] [])) :=
  joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable (oldSeedStep H t output header _) (copyOldTrace H t output header))
    (oldLoopTrace H t output header)

def ownerData (t : GraphTables.Table) (index : Nat) (output : List Bool) : Data :=
  { headerData t output with
    globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) index)
    owner := encodeWord index
    offset := encodeWord (PreprocessingPaddingOffsets.offset
      (PreprocessingRegularTables.padding t) index) }

theorem ownerSeedStep (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) header counters)) =
      some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) header counters) := by
  change some (TM2.stepAux
    (.push (coreTape 2) (fun _ => false) (.push (coreTape 5) (fun _ => false)
      (.goto fun _ => Label.copyFirst CopyPhase.owner))) (readyState H)
      (frame (oldData t t.darts output) header counters)) = _
  simp only [TM2.stepAux, frame_core]
  change some (⟨some (Label.copyFirst CopyPhase.owner), readyState H,
    Function.update (Function.update (frame (oldData t t.darts output) header counters)
      (coreTape 2) [false]) (coreTape 5) [false]⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner, update_frame_offset]
  simp only [cfg, ownerData, oldData, PreprocessingPaddingOffsets.offset_zero, Nat.add_zero,
    encodeWord, List.replicate_zero, List.nil_append]

theorem copyOwnerTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[2*(t.vertices+2)]
      (some (cfg H (some (.copyFirst .owner)) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t 0 output) (headerStacks t)
        (counterStacks [] (encodeWord t.vertices) [] [])) := by
  have h := MachineCopy.copyTrace (headerTape Header.nTape) ownerFuel scratch
    (by decide) (by decide) (by decide) false (.copyFirst .owner) (.copySecond .owner)
    (some .ownerGuard) (program H) rfl rfl
    (frame (ownerData t 0 output) (headerStacks t) (counterStacks [] [] [] [])) rfl
    (MachineRegularOriginalBody.readyState H) none
  simpa only [headerStacks, frame_header_n, encodeWord_length, frame_ownerFuel,
    List.append_nil, update_frame_ownerFuel, cfg, readyState, Nat.add_assoc] using h

theorem ownerPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (old owners : List Bool) :
    MachineCloudPadding.Placement.tapes ownerView (MachineRegularOwnerBody.frame data)
      (frame extra header (counterStacks old owners [] [])) =
      frame data header (counterStacks old owners [] []) := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j with
    | inl j => rfl
    | inr i => fin_cases i <;> rfl

theorem ownerInitialData_eq (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.initialData t v output = ownerData t v.val output := rfl

theorem ownerBodyTrace (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (owners : List Bool) :
    (advance (TM2.step (program H)))^[MachineRegularOwnerBody.totalSteps H t v output]
      (some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry))
        (ownerData t v.val output) header (counterStacks [] owners [] []))) =
      some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header (counterStacks [] owners [] [])) := by
  have raw := MachineRegularOwnerBody.ownerTrace H t v output
  have placed := MachineCloudPadding.Placement.trace ownerTape ownerView ownerView_left ownerView_right
    Label.ownerBody (some .ownerIncrement)
    (frame (ownerData t v.val output) header (counterStacks [] owners [] []))
    (MachineRegularOwnerBody.program H) (program H) (fun _ => rfl) _ _ _ raw
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    ownerPlacement, MachineRegularOwnerBody.cfg, MachineRegularOwnerBody.readyState,
    ownerInitialData_eq, cfg, readyState] using placed

theorem ownerGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header
        (counterStacks [] (encodeWord (remaining+1)) [] []))) =
      some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry)) data header
        (counterStacks [] (encodeWord remaining) [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_ownerFuel]
  rfl

theorem ownerGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header (counterStacks [] (encodeWord 0) [] []))) =
      some (cfg H (clearEntry 0) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_ownerFuel]
  rfl

theorem ownerIncrementStep (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerIncrement) (MachineRegularOwnerBody.finalData H t v output)
        header counters)) =
      some (cfg H (some .ownerGuard)
        (ownerData t (v.val+1) (output ++ MachineRegularOwnerBody.ownerBits H t v)) header counters) := by
  change some (TM2.stepAux (Fuel.increment (coreTape 2) Label.ownerGuard) (readyState H)
    (frame (MachineRegularOwnerBody.finalData H t v output) header counters)) = _
  simp only [Fuel.increment, TM2.stepAux, frame_core]
  change some (⟨some Label.ownerGuard, readyState H,
    Function.update (frame (MachineRegularOwnerBody.finalData H t v output) header counters)
      (coreTape 2) (true :: encodeWord v.val)⟩ :
      TM2.Cfg (fun _ : Tape => Bool) Label State) = _
  rw [update_frame_owner]
  have offset := PreprocessingRegularBounds.offset_succ (PreprocessingRegularTables.padding t) v.val v.isLt
  simp only [cfg, ownerData, headerData, inputData, MachineRegularOwnerBody.finalData,
    MachineRegularOwnerBody.initialData, offset, encodeWord, List.replicate_succ,
    List.cons_append, Nat.add_assoc]

def ownerPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) : List Bool :=
  PreprocessingRegularLoopWords.blocksPrefix (MachineRegularOwnerBody.ownerBits H t) k

noncomputable def ownerElapsed (H : BaseTable) (t : GraphTables.Table) (output : List Bool) : Nat → Nat
  | 0 => 0
  | k+1 => ownerElapsed H t output k +
      if h : k < t.vertices then
        1 + MachineRegularOwnerBody.totalSteps H t ⟨k,h⟩ (output ++ ownerPrefix H t k) + 1
      else 0

theorem ownerPrefixTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) (k : Nat) : k ≤ t.vertices →
    (advance (TM2.step (program H)))^[ownerElapsed H t output k]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (some .ownerGuard) (ownerData t k (output ++ ownerPrefix H t k)) header
        (counterStacks [] (encodeWord (t.vertices-k)) [] [])) := by
  induction k with
  | zero =>
    intro _
    simp [ownerElapsed, ownerPrefix]
  | succ k ih =>
    intro hk
    have hlt : k < t.vertices := by omega
    have hremaining : t.vertices-k = (t.vertices-(k+1))+1 := by omega
    have previous := ih (by omega)
    have guard := ownerGuardStep H (ownerData t k (output ++ ownerPrefix H t k)) header
      (t.vertices-(k+1))
    rw [← hremaining] at guard
    have body := ownerBodyTrace H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (encodeWord (t.vertices-(k+1)))
    have increment := ownerIncrementStep H t ⟨k,hlt⟩ (output ++ ownerPrefix H t k) header
      (counterStacks [] (encodeWord (t.vertices-(k+1))) [] [])
    have combined := joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable previous guard) body) increment
    have bits := PreprocessingRegularLoopWords.blocksPrefix_succ
      (MachineRegularOwnerBody.ownerBits H t) k hlt
    change ownerPrefix H t (k+1) = ownerPrefix H t k ++
      MachineRegularOwnerBody.ownerBits H t ⟨k,hlt⟩ at bits
    simpa only [ownerElapsed, dite_eq_left hlt, bits, List.append_assoc, Nat.add_assoc] using combined

theorem ownerLoopTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool)
    (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[ownerElapsed H t output t.vertices+1]
      (some (cfg H (some .ownerGuard) (ownerData t 0 output) header
        (counterStacks [] (encodeWord t.vertices) [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) header
        (counterStacks [] [] [] [])) := by
  have prefixRun := ownerPrefixTrace H t output header t.vertices (Nat.le_refl _)
  simp only [Nat.sub_self] at prefixRun
  exact joinTrace_inline_MachineRegularTable prefixRun (ownerGuardExit H _ header)

theorem ownerStageTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[1+2*(t.vertices+2)+(ownerElapsed H t output t.vertices+1)]
      (some (cfg H (some Label.ownerSeed) (oldData t t.darts output) (headerStacks t)
        (counterStacks [] [] [] []))) =
      some (cfg H (clearEntry 0)
        (ownerData t t.vertices (output ++ ownerPrefix H t t.vertices)) (headerStacks t)
        (counterStacks [] [] [] [])) :=
  joinTrace_inline_MachineRegularTable (joinTrace_inline_MachineRegularTable (ownerSeedStep H t output (headerStacks t) _) (copyOwnerTrace H t output))
    (ownerLoopTrace H t output (headerStacks t))

theorem owner_output_eq_ownerPrefix (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    (Header.headerBits PreprocessingRegularTables.internalDegree t ++ oldPrefix H t t.darts) ++
        ownerPrefix H t k =
      PreprocessingRegularBounds.ownerPrefix t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) k := by
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      PreprocessingRegularBounds.ownerBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  simp only [Header.headerBits, Header.vertexTotal, Header.dartTotal, oldPrefix,
    ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    PreprocessingRegularBounds.ownerPrefix, PreprocessingRegularBounds.header]
  rw [oldBits, ownerBits]

def cleaned (base : Tape → List Bool) : Nat → Tape → List Bool
  | 0 => base
  | k+1 => if h : k < 7 then Function.update (cleaned base k) (clearTape ⟨k,h⟩) []
      else cleaned base k

def cleanupTime (base : Tape → List Bool) : Nat → Nat
  | 0 => 0
  | k+1 => cleanupTime base k + if h : k < 7 then
      ((cleaned base k) (clearTape ⟨k,h⟩)).length+1 else 0

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length+1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val+1), readyState H, Function.update base (clearTape i) []⟩ := by
  have h := MachineDrain.drainTrace (clearTape i) (.clear i) (clearEntry (i.val+1))
    (program H) rfl base (base (clearTape i)) (MachineRegularOriginalBody.readyState H) none
  simpa only [Function.update_eq_self, readyState] using h

theorem cleanupPrefixTrace (H : BaseTable) (base : Tape → List Bool) (k : Nat) (hk : k ≤ 7) :
    (advance (TM2.step (program H)))^[cleanupTime base k]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨clearEntry k, readyState H, cleaned base k⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < 7 := by omega
    have first := ih (by omega)
    have second := drainTrace H ⟨k,h⟩ (cleaned base k)
    have atEntry : clearEntry k = some (.clear ⟨k,h⟩) := by simp only [clearEntry, dite_eq_left h]
    rw [atEntry] at first
    simpa only [cleanupTime, cleaned, dite_eq_left h] using joinTrace_inline_MachineRegularTable first second

theorem cleanupTrace (H : BaseTable) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime base 7]
      (some ⟨clearEntry 0, readyState H, base⟩) =
      some ⟨none, readyState H, cleaned base 7⟩ := by
  simpa only [clearEntry, lt_self_iff_false, dite_false] using cleanupPrefixTrace H base 7 le_rfl

def finalStacks (t : GraphTables.Table) (output : List Bool) : Tape → List Bool :=
  frame (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] [])

theorem cleaned_finalStacks (t : GraphTables.Table) (output : List Bool) :
    cleaned (finalStacks t output) 7 =
      frame (inputData t output) (fun _ => []) (counterStacks [] [] [] []) := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j => cases j with
    | inl k => cases k with
      | inl k => cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => fin_cases i <;> rfl

theorem cleaned_length_le (base : Tape → List Bool) (k : Nat) :
    ∀ j, (cleaned base k j).length ≤ (base j).length := by
  induction k with
  | zero => intro j; exact Nat.le_refl _
  | succ k ih =>
    intro j
    simp only [cleaned]
    split
    · rename_i hk
      by_cases hj : j = clearTape ⟨k,hk⟩
      · simp [hj]
      · simpa only [Function.update_of_ne hj] using ih j
    · exact ih j

theorem cleanupTime_le (base : Tape → List Bool) (cap : Nat)
    (bounded : ∀ i : Fin 7, (base (clearTape i)).length ≤ cap) (k : Nat) :
    cleanupTime base k ≤ k*(cap+1) := by
  induction k with
  | zero => simp [cleanupTime]
  | succ k ih =>
    simp only [cleanupTime]
    split
    · rename_i hk
      have hword := (cleaned_length_le base k (clearTape ⟨k,hk⟩)).trans (bounded ⟨k,hk⟩)
      calc
        cleanupTime base k + ((cleaned base k (clearTape ⟨k,hk⟩)).length+1) ≤
            k*(cap+1)+(cap+1) := by omega
        _ = (k+1)*(cap+1) := by simp only [Nat.add_mul, one_mul]
    · exact ih.trans (Nat.mul_le_mul_right _ (by omega))

theorem cleanupTime_final_le (t : GraphTables.Table) (output : List Bool) :
    cleanupTime (finalStacks t output) 7 ≤
      (7*(ExpanderFamily.growth*(PreprocessingRegularTables.internalDegree+4)+4)) *
        (PreprocessingMachineBounds.inputLength t+1) := by
  let L := PreprocessingMachineBounds.inputLength t
  let g := ExpanderFamily.growth
  let q := PreprocessingRegularTables.internalDegree
  let C := g*(q+4)+4
  have hm : t.darts ≤ L := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ L := GraphTables.vertices_le_tableBits_length t
  have hs : PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ g*L :=
    PreprocessingMachineBounds.prefix_le_input t t.vertices
  have hN : Header.vertexTotal t ≤ g*L := PreprocessingMachineBounds.regularVertices_le_input t
  have hone : 1 ≤ C := by dsimp [C]; omega
  have hg : g ≤ C := by
    have h := Nat.mul_le_mul_left g (show 1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hgp : g+1 ≤ C := by
    have h := Nat.mul_le_mul_left g (show 1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hgq : g*(q+1) ≤ C := by
    have h := Nat.mul_le_mul_left g (show q+1 ≤ q+4 by omega)
    dsimp [C]
    omega
  have hmC : t.darts ≤ C*L := hm.trans (by simpa using Nat.mul_le_mul_right L hone)
  have hnC : t.vertices ≤ C*L := hn.trans (by simpa using Nat.mul_le_mul_right L hone)
  have hsC : PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ C*L :=
    hs.trans (Nat.mul_le_mul_right L hg)
  have hNC : Header.vertexTotal t ≤ C*L := hN.trans (Nat.mul_le_mul_right L hg)
  have hxC : t.darts +
      PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices ≤ C*L := by
    calc
      _ ≤ L+g*L := Nat.add_le_add hm hs
      _ = (g+1)*L := by simp only [Nat.add_mul, one_mul, Nat.add_comm]
      _ ≤ C*L := Nat.mul_le_mul_right L hgp
  have hRC : Header.dartTotal q t ≤ C*L := by
    calc
      _ ≤ (g*L)*(q+1) := Nat.mul_le_mul_right _ hN
      _ = (g*(q+1))*L := by ac_rfl
      _ ≤ C*L := Nat.mul_le_mul_right L hgq
  have bounds : ∀ i : Fin 7, (finalStacks t output (clearTape i)).length ≤ C*L+1 := by
    intro i
    fin_cases i
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hxC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hnC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hsC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hmC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hnC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hNC 1
    · change (encodeWord _).length ≤ _
      simpa only [encodeWord_length] using Nat.add_le_add_right hRC 1
  have actual := cleanupTime_le (finalStacks t output) (C*L+1) bounds 7
  have hC : 2 ≤ C := by dsimp [C]; omega
  change cleanupTime (finalStacks t output) 7 ≤ (7*C)*(L+1)
  nlinarith

def oldOutput (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  headerOutput t ++ oldPrefix H t t.darts

def finalOutput (H : BaseTable) (t : GraphTables.Table) : List Bool :=
  oldOutput H t ++ ownerPrefix H t t.vertices

noncomputable def totalTime (H : BaseTable) (t : GraphTables.Table) : Nat :=
  Header.totalTime PreprocessingRegularTables.internalDegree t [] +
    (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
    (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1)) +
    cleanupTime (finalStacks t (finalOutput H t)) 7

theorem finalOutput_eq (H : BaseTable) (t : GraphTables.Table) :
    finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.regularize H t) := by
  change finalOutput H t = PortTables.tableBits (PreprocessingRegularTables.ofCloudTables t
    (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t))
  rw [PreprocessingRegularWords.tableBits_ofCloudTables]
  have oldBits : MachineRegularOriginalBody.emittedBits H t =
      PreprocessingRegularWords.originalVertexBits t (PreprocessingRegularTables.padding t)
        (PreprocessingRegularTables.familyCloudTable H t) := rfl
  have ownerBits : MachineRegularOwnerBody.ownerBits H t =
      (fun v => (List.ofFn (PreprocessingRegularWords.dummyVertexBits t
        (PreprocessingRegularTables.padding t) (PreprocessingRegularTables.familyCloudTable H t) v)).flatten) := rfl
  simp only [finalOutput, oldOutput, headerOutput, Header.headerBits, Header.vertexTotal,
    Header.dartTotal, oldPrefix, ownerPrefix, PreprocessingRegularLoopWords.blocksPrefix_all,
    List.append_assoc]
  rw [oldBits, ownerBits]

end Top

end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineVertex
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variable-size vertex enumeration. The finite guard decrements the
live unary counter, a one-step bridge enters the fixed vertex producer, and the
producer returns to the guard. Work tapes may change after every vertex. -/

/-!
# Physical output headers followed by complete work-tape cleanup

The finite program first copies the dart-count word onto the existing row
output, then copies the vertex-count word, and finally drains every tape except
the output. Both unary header values are read from physical tapes; they do not
parameterize the program. Header sources and their unread suffixes are restored
by the two copies before cleanup. The final configuration contains the full
encoded header and rows on the output tape and empty words on every other tape.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

/-- Exact execution inside any ambient program containing these instructions.
The only data premises describe physical header words and an empty scratch tape. -/
theorem traceAt (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (labels : Label enumeration output → Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, target (labels l) =
      instruction enumeration headerV headerD output scratch labels l)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps enumeration output base n m]
      (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩ := by
  have hd := MachineUnaryAffineAt.seededAffineTrace headerD scratch output hds hdo hso 1 0
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (.inr (.inl .seed)))) target
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base m suffixD wordD scratchEmpty ambient register
  simp only [Nat.one_mul, Nat.add_zero] at hd
  change (advance (TM2.step target))^[2 * (m + 1) + 1]
    (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
    some ⟨some (labels (.inr (.inl .seed))), (ambient, none), afterD output base m⟩ at hd
  have wordV' : afterD output base m headerV = encodeWord n ++ suffixV := by
    simpa only [afterD, Function.update_of_ne hvo] using wordV
  have scratchEmpty' : afterD output base m scratch = [] := by
    simpa only [afterD, Function.update_of_ne hso] using scratchEmpty
  have hv := MachineUnaryAffineAt.seededAffineTrace headerV scratch output hvs hvo hso 1 0
    (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
    (labels (.inr (.inl .restore)))
    (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
      (fun q => labels (.inr (.inr q))) none)
    target (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
    (atLabels (.inr (.inl .restore))) (afterD output base m) n suffixV
    wordV' scratchEmpty' ambient none
  simp only [Nat.one_mul, Nat.add_zero] at hv
  have copied : Function.update (afterD output base m) output
      (encodeWord n ++ afterD output base m output) = afterHeaders output base n m := by
    simp only [afterD, afterHeaders, Function.update_self, Function.update_idem,
      encodeWords, List.append_nil, List.append_assoc]
  rw [copied] at hv
  have cleaned := MachineDrainMany.cleanupTrace enumeration output
    (fun q => labels (.inr (.inr q))) target (fun l => atLabels (.inr (.inr l)))
    (afterHeaders output base n m) ambient
  rw [afterHeaders_output] at cleaned
  have total := trace_trans_inline_PoweringMachineFinish _ (trace_trans_inline_PoweringMachineFinish _ hd hv) cleaned
  simpa only [steps, copySteps] using total

end MaxCutGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PoweringPolynomialBudget
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget

open PCP

@[simp] theorem vertexTime_eval (d n inputLength : Nat) :
    (vertexTime d n).eval inputLength = PoweringMachineVertex.budget d n inputLength := by
  simp only [vertexTime, Polynomial.eval_mul, Polynomial.eval_C, rowTime_eval,
    PoweringMachineVertex.budget]

end MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularTableTrace
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

theorem headerStartTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[Header.totalTime PreprocessingRegularTables.internalDegree t []]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .oldSeed) (headerData t (headerOutput t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have run := headerTrace H t [] (counterStacks [] [] [] [])
  exact run.trans (normalizeEmptyAppend_inline_MachineRegularTableTrace
    (fun output : List Bool => some (cfg H (some Label.oldSeed)
      (headerData t output) (headerStacks t) (counterStacks [] [] [] [])))
    (Header.headerBits PreprocessingRegularTables.internalDegree t))

theorem headerOldTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H (some .ownerSeed) (oldData t t.darts (oldOutput H t)) (headerStacks t)
        (counterStacks [] [] [] [])) := by
  have first := headerStartTrace H t
  have second := oldStageTrace H t (headerOutput t) (headerStacks t)
  have joined := joinTraceRegularTableTrace_inline_MachineRegularTableTrace (f := advance (TM2.step (program H))) first second
  have output_eq : headerOutput t ++ oldPrefix H t t.darts = oldOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (some Label.ownerSeed)
      (oldData t t.darts output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem beforeCleanupTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[
      Header.totalTime PreprocessingRegularTables.internalDegree t [] +
        (1+2*(t.darts+2)+(oldElapsed H t (headerOutput t) t.darts+1)) +
        (1+2*(t.vertices+2)+(ownerElapsed H t (oldOutput H t) t.vertices+1))]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some ⟨clearEntry 0, readyState H, finalStacks t (finalOutput H t)⟩ := by
  have first := headerOldTrace H t
  have second := ownerStageTrace H t (oldOutput H t)
  have joined := joinTraceRegularTableTrace_inline_MachineRegularTableTrace (f := advance (TM2.step (program H))) first second
  have output_eq : oldOutput H t ++ ownerPrefix H t t.vertices = finalOutput H t := rfl
  exact joined.trans (congrArg
    (fun output : List Bool => some (cfg H (clearEntry 0)
      (ownerData t t.vertices output) (headerStacks t) (counterStacks [] [] [] []))) output_eq)

theorem cleanupFinalTrace (H : BaseTable) (t : GraphTables.Table) (output : List Bool) :
    (advance (TM2.step (program H)))^[cleanupTime (finalStacks t output) 7]
      (some ⟨clearEntry 0, readyState H, finalStacks t output⟩) =
      some (cfg H none (inputData t output) (fun _ => []) (counterStacks [] [] [] [])) :=
  (cleanupTrace H (finalStacks t output)).trans
    (congrArg (fun terminalStacks => some (⟨none, readyState H, terminalStacks⟩ : TM2.Cfg Alphabet Label State))
      (cleaned_finalStacks t output))

theorem fullTrace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (cfg H (some (.header .init)) (inputData t []) (fun _ => [])
        (counterStacks [] [] [] []))) =
      some (cfg H none (inputData t (finalOutput H t)) (fun _ => [])
        (counterStacks [] [] [] [])) :=
  joinTraceRegularTableTrace_inline_MachineRegularTableTrace (f := advance (TM2.step (program H))) (beforeCleanupTrace H t) (cleanupFinalTrace H t (finalOutput H t))

theorem input_stacks_eq (H : BaseTable) (t : GraphTables.Table) :
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      (Turing.initList (machine H) (GraphTables.tableBits t)).stk := by
  funext j
  cases j with
  | inl j => cases j with
    | inl i =>
      fin_cases i <;>
        simp [Turing.initList, machine, coreTape, frame, inputData,
          MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      rfl
    | inr e => cases e with
      | inl e => cases e <;>
          simp [Turing.initList, machine, coreTape, frame, inputData,
            MachineRegularOriginalBody.frame, MachineRegularMetadata.frame]
      | inr e =>
          simp [Turing.initList, machine, coreTape, frame,
            MachineRegularOriginalBody.frame]
  | inr j => cases j with
    | inl j => simp [Turing.initList, machine, coreTape, frame]
    | inr j => fin_cases j <;> simp [Turing.initList, machine, coreTape, frame, counterStacks]

theorem initial_cfg_eq (H : BaseTable) (t : GraphTables.Table) :
    cfg H (some (.header .init)) (inputData t []) (fun _ => []) (counterStacks [] [] [] []) =
      Turing.initList (machine H) (GraphTables.tableBits t) := by
  change (⟨some (.header .init), readyState H,
    frame (inputData t []) (fun _ => []) (counterStacks [] [] [] [])⟩ : TM2.Cfg Alphabet Label State) =
    ⟨some (.header .init), readyState H, (Turing.initList (machine H) (GraphTables.tableBits t)).stk⟩
  rw [input_stacks_eq]

/-- Complete execution from the actual serialized input. All header reads,
metadata, geometric rotors, rows, counters and cleanup are run by this one
finite machine. No body trace or target-table computation is supplied as a premise. -/
theorem trace (H : BaseTable) (t : GraphTables.Table) :
    (advance (TM2.step (program H)))^[totalTime H t]
      (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
      some ⟨none, readyState H,
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (PreprocessingRegularTables.regularize H t))⟩ := by
  have full := fullTrace H t
  rw [initial_cfg_eq, finalOutput_eq] at full
  have final_stacks :
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
          (fun _ => []) (counterStacks [] [] [] []) =
        Function.update (Turing.initList (machine H) (GraphTables.tableBits t)).stk (coreTape 8)
          (PortTables.tableBits (PreprocessingRegularTables.regularize H t)) := by
    rw [← input_stacks_eq]
    erw [update_frame_output]
    rfl
  change (advance (TM2.step (program H)))^[totalTime H t]
    (some (Turing.initList (machine H) (GraphTables.tableBits t))) =
    some ⟨none, readyState H,
      frame (inputData t (PortTables.tableBits (PreprocessingRegularTables.regularize H t)))
        (fun _ => []) (counterStacks [] [] [] [])⟩ at full
  rw [final_stacks] at full
  exact full

end MaxCutGames.Foundations.Complexity.MachineRegularTable.Top

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/
namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

theorem totalSteps_le (H : PreprocessingRegularTables.BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) :
    totalSteps H t e output ≤ timePolynomial.eval (bodySize t output) := by
  have hsize : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hm := (MachineRegularMetadata.totalTime_le t e).trans
    (natPolynomial_eval_mono MachineRegularMetadata.timePolynomial hsize)
  have hf := (familyExecution H t e output).steps_le_m
  have hfb := MachineRegularExecutionBounds.family_budget_le t t.rows[e].tail
  simp only [MachineRegularFamily.timePolynomial, encodeWord_length,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat] at hf
  have hf' := (hf.trans hfb).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial hsize)
  have hv := vertexSteps_le H t e output
  have hc := cleanupSteps_le H t e output
  simp only [totalSteps, familySteps, timePolynomial, Polynomial.eval_add]
  omega

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Any finite prefix inside this owner is a part of the actual output table,
including when the supplied prefix length is larger than the number of blocks. -/
theorem ownerPrefix_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) :
    (blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤ regularPolynomial.eval (inputLength t) := by
  have h := PreprocessingRegularBounds.regular_dummyPrefix_le t H v n
  simp only [PreprocessingRegularBounds.dummyPrefix, List.length_append] at h
  omega

theorem growingOutput_length_le (H : BaseTable) (t : GraphTables.Table)
    (v : Fin t.vertices) (n : Nat) (output : List Bool) :
    (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
      (familyCloudTable H t) v) n).length ≤
      (ExpanderFamily.growth+1)*bodySize t output + regularPolynomial.eval (bodySize t output) := by
  have h := (ownerPrefix_length_le H t v n).trans
    (natPolynomial_eval_mono regularPolynomial (Nat.le_add_right (inputLength t) output.length))
  have hO := (wide_le t output).2.2
  rw [List.length_append]
  exact Nat.add_le_add hO h

/-- One actual dummy block has a uniform polynomial cost at every prefix of
the owner loop. The only inputs are the real table, indices, and old output. -/
theorem dummySteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (j : Fin (padding t v)) (n : Nat) (output : List Bool) :
    MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length ≤
      (blockPolynomial internalDegree).eval (bodySize t output) := by
  let x := paddedNew t (padding t) v j
  let W := (ExpanderFamily.growth+1)*bodySize t output
  have bounds := wide_le t output
  have hx := (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hi := (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hk := cloudSize_le_input t v
  have hm := GraphTables.darts_le_tableBits_length t
  have ho := prefix_le_input t v.val
  have hV := regularVertices_le_input t
  have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
    (natPolynomial_eval_mono (rotorPolynomial internalDegree)
      (Nat.le_add_right (inputLength t) output.length))
  have hO := growingOutput_length_le H t v n output
  have raw := MachineRegularVertexBlock.dummySteps_le internalDegree
    MachineRegularOriginalBody.degree_positive t (padding t) (familyCloudTable H t) v j
      (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
        (familyCloudTable H t) v) n).length
  have bound := dummyTimeBound_le internalDegree _ _ _ _ _ _ _ _ _ _ W _ _
    bounds.1 hR (hx.trans bounds.2.1) (hv.trans bounds.1) (hi.trans bounds.2.1)
    (hk.trans bounds.1) (ho.trans bounds.2.1) (hm.trans bounds.1) hO
    (hV.trans bounds.2.1)
  rw [blockPolynomial_eval]
  exact raw.trans bound

theorem preSteps_le (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.preSteps t v ≤ prePolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := cloudSize_le_input t v
  have hd := cloudTotal_le_input t v
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  change v.val ≤ inputLength t at hv
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2*bodySize t output+1 := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    change inputLength t + (v.val+1) ≤ _
    omega
  have hm := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineRegularOwnerBody.preSteps, prePolynomial, wide, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

theorem loopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) (n : Nat) (hn : n ≤ padding t v) :
    MachineRegularOwnerBody.loopSteps H t v output n hn ≤
      n * ((blockPolynomial internalDegree).eval (bodySize t output) + 2) := by
  induction n with
  | zero => simp only [MachineRegularOwnerBody.loopSteps, Nat.zero_mul, le_refl]
  | succ n ih =>
    have h : n < padding t v := by omega
    have first := ih (by omega)
    have second := dummySteps_le H t v ⟨n, h⟩ n output
    rw [MachineRegularOwnerBody.loopSteps, Nat.succ_mul]
    change MachineRegularOwnerBody.loopSteps H t v output n _ +
      (1 + MachineRegularVertexBlock.dummySteps t (padding t) (familyCloudTable H t) v ⟨n, h⟩
        (output ++ blocksPrefix (PreprocessingRegularWords.dummyVertexBits t (padding t)
          (familyCloudTable H t) v) n).length + 1) ≤ _
    omega

theorem allLoopSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.loopSteps H t v output (padding t v) le_rfl ≤
      loopPolynomial.eval (bodySize t output) := by
  have hd := (cloudTotal_le_input t v).trans (wide_le t output).2.1
  have hp : padding t v ≤ (ExpanderFamily.growth+1)*bodySize t output := by omega
  have h := (loopSteps_le H t v output (padding t v) le_rfl).trans
    (Nat.mul_le_mul_right _ hp)
  simpa only [loopPolynomial, wide, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

/-- Exact cost of the six physical drain loops and the prefix addition,
expressed through the actual entry stack lengths. -/
theorem cleanupSteps_working (data : MachineRegularOwnerBody.Data)
    (fuel saved : List Bool) (d : Nat) :
    MachineRegularOwnerCleanup.steps (MachineRegularOwnerBody.working data fuel saved) d =
      2*(d+1) + data.localRank.length + data.count.length + data.rotor.length +
        data.padding.length + data.level.length + fuel.length + 6 := by
  change 2*(d+1) + ((data.localRank.length+1) + ((data.count.length+1) +
    ((data.rotor.length+1) + ((data.padding.length+1) + ((data.level.length+1) +
      ((fuel.length+1)+0)))))) = _
  omega

theorem cleanupCost_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.cleanupCost H t v output ≤
      cleanupPolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := (cloudSize_le_input t v).trans bounds.1
  have htotal := (cloudTotal_le_input t v).trans bounds.2.1
  have hl := (level_le_input t v).trans bounds.1
  have hp : MachineCloudPadding.padding (cloudSize t v) = padding t v := rfl
  by_cases hd : padding t v = 0
  · rw [MachineRegularOwnerBody.cleanupCost, ite_eq_left hd, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, List.length_nil, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega
  · have hpositive : 0 < padding t v := by omega
    have hkpos := PreprocessingFamilyBridge.cloudSize_pos_of_dummy t v ⟨0, hpositive⟩
    have hrotor := PreprocessingFamilyBridge.familyRotor_eq_familyCloudTable H t v hkpos
    change MachineRegularFamily.rotor H (cloudSize t v) = _ at hrotor
    have hR := (cloudRotorBits_le t v (familyCloudTable H t v)).trans
      (natPolynomial_eval_mono (rotorPolynomial internalDegree)
        (Nat.le_add_right (inputLength t) output.length))
    rw [← hrotor] at hR
    change (MachineRegularFamily.rotor H (cloudSize t v)).length ≤
      (rotorPolynomial internalDegree).eval (bodySize t output) at hR
    rw [MachineRegularOwnerBody.cleanupCost, ite_eq_right hd,
      MachineRegularOwnerBody.loopFrame, cleanupSteps_working]
    simp only [MachineRegularOwnerBody.loopData, MachineRegularOwnerBody.vertexData,
      MachineRegularOwnerBody.seededData, MachineRegularOwnerBody.metadataData,
      MachineRegularMetadata.cloudData, MachineRegularOwnerBody.initialData,
      hp, encodeWord_length, Nat.sub_self, cleanupPolynomial, wide,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    omega

/-- The whole owner budget follows from the real recurrence and its separately
proved stage bounds. The zero-padding branch performs no family or vertex work. -/
theorem ownerTime_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.ownerTime H t v output ≤ timePolynomial.eval (bodySize t output) := by
  have hp := preSteps_le t v output
  have hc := cleanupCost_le H t v output
  have hl := allLoopSteps_le H t v output
  have hf := (MachineRegularExecutionBounds.family_budget_le t v).trans
    (natPolynomial_eval_mono MachineRegularExecutionBounds.familyPolynomial
      (Nat.le_add_right (inputLength t) output.length))
  have hfamily : MachineRegularFamily.timePolynomial.eval (encodeWord (cloudSize t v)).length ≤
      MachineRegularExecutionBounds.familyPolynomial.eval (bodySize t output) := by
    simpa only [bodySize, MachineRegularFamily.timePolynomial, encodeWord_length, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using hf
  simp only [MachineRegularOwnerBody.ownerTime, timePolynomial, Polynomial.eval_add,
    Polynomial.eval_ofNat]
  split_ifs <;> omega

theorem totalSteps_le (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices)
    (output : List Bool) :
    MachineRegularOwnerBody.totalSteps H t v output ≤ timePolynomial.eval (bodySize t output) :=
  (MachineRegularOwnerBody.totalSteps_le H t v output).trans (ownerTime_le H t v output)

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

/-! A polynomial cap for the actual two regularization loops, their header,
and all seven final drain loops. Per-call sizes include the complete stored
output prefix. -/
namespace MaxCutGames.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition PCP PreprocessingRegularTables
open PreprocessingRegularBounds PreprocessingMachineBounds

noncomputable def oldLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOriginalBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

noncomputable def timePolynomial : Polynomial Nat :=
  Header.timePolynomial internalDegree + oldLoopPolynomial + ownerLoopPolynomial +
    4 * Polynomial.X + 12 +
    Polynomial.C (7 * (ExpanderFamily.growth * (internalDegree + 4) + 4)) *
      (Polynomial.X + 1)

theorem oldElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    oldElapsed H t (Header.headerBits internalDegree t) k ≤
      k * (MachineRegularOriginalBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [oldElapsed]
  | succ k ih =>
    simp only [oldElapsed]
    split_ifs with hk
    · have raw := MachineRegularOriginalBodyBounds.totalSteps_le H t ⟨k, hk⟩
        (Header.headerBits internalDegree t ++ oldPrefix H t k)
      have hprefix :
          (Header.headerBits internalDegree t ++ oldPrefix H t k).length ≤
            regularPolynomial.eval (inputLength t) := by
        exact regular_originalPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOriginalBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem oldElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    oldElapsed H t (Header.headerBits internalDegree t) t.darts ≤
      oldLoopPolynomial.eval (inputLength t) := by
  have bound := (oldElapsed_prefix_le H t t.darts).trans
    (Nat.mul_le_mul_right _ (GraphTables.darts_le_tableBits_length t))
  simpa only [oldLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem ownerElapsed_prefix_le (H : BaseTable) (t : GraphTables.Table) (k : Nat) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) k ≤
      k * (MachineRegularOwnerBodyBounds.timePolynomial.eval
        (inputLength t + regularPolynomial.eval (inputLength t)) + 2) := by
  induction k with
  | zero => simp [ownerElapsed]
  | succ k ih =>
    simp only [ownerElapsed]
    split_ifs with hk
    · have raw := MachineRegularOwnerBodyBounds.totalSteps_le H t ⟨k, hk⟩
        ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++ ownerPrefix H t k)
      have hprefix :
          ((Header.headerBits internalDegree t ++ oldPrefix H t t.darts) ++
            ownerPrefix H t k).length ≤ regularPolynomial.eval (inputLength t) := by
        rw [owner_output_eq_ownerPrefix]
        exact regular_ownerPrefix_le t H k
      have hcall := raw.trans (natPolynomial_eval_mono
        MachineRegularOwnerBodyBounds.timePolynomial (Nat.add_le_add_left hprefix _))
      rw [Nat.succ_mul]
      omega
    · rw [Nat.succ_mul]
      omega

theorem ownerElapsed_le (H : BaseTable) (t : GraphTables.Table) :
    ownerElapsed H t
      (Header.headerBits internalDegree t ++ oldPrefix H t t.darts) t.vertices ≤
      ownerLoopPolynomial.eval (inputLength t) := by
  have bound := (ownerElapsed_prefix_le H t t.vertices).trans
    (Nat.mul_le_mul_right _ (GraphTables.vertices_le_tableBits_length t))
  simpa only [ownerLoopPolynomial, inputLength, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_ofNat] using bound

theorem totalTime_le (H : BaseTable) (t : GraphTables.Table) :
    totalTime H t ≤ timePolynomial.eval (inputLength t) := by
  have header := Header.totalTime_le internalDegree t []
  simp only [List.length_nil, Nat.add_zero] at header
  change Header.totalTime internalDegree t [] ≤
    (Header.timePolynomial internalDegree).eval (inputLength t) at header
  have old := oldElapsed_le H t
  have owners := ownerElapsed_le H t
  have cleanup := cleanupTime_final_le t (finalOutput H t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hn : t.vertices ≤ inputLength t := GraphTables.vertices_le_tableBits_length t
  simp only [totalTime, headerOutput, oldOutput, timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

noncomputable def machineInTime (H : BaseTable) (t : GraphTables.Table) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      (initList (machine H) (GraphTables.tableBits t))
      (some ⟨none, readyState H,
        Function.update (initList (machine H) (GraphTables.tableBits t)).stk
          (coreTape 8) (PortTables.tableBits (regularize H t))⟩)
      (timePolynomial.eval (inputLength t)) where
  steps := totalTime H t
  evals_in_steps := trace H t
  steps_le_m := totalTime_le H t

end MaxCutGames.Foundations.Complexity.MachineRegularTable.Top

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularTableRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularTableRuntime

open Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)

def rawProgram (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.Program Tape Label State where
  input := coreTape 0
  output := coreTape 8
  main := .header .init
  initial := readyState H
  code := MachineRegularTable.Top.program H

theorem sourceMachine_eq (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.sourceMachine (rawProgram H) =
      MachineRegularTable.Top.machine H := rfl

noncomputable def cleanupTapes : List Tape :=
  (Finset.univ : Finset Tape).toList.filter (fun k => decide (k ≠ coreTape 8))

theorem cleanup_complete (H : PreprocessingRegularTables.BaseTable) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H).output := by
  simp [cleanupTapes, rawProgram]

noncomputable def terminalRun (H : PreprocessingRegularTables.BaseTable)
    (t : GraphTables.Table) :
    MachineCanonicalOutput.TerminalRun (rawProgram H) (GraphTables.tableBits t)
      (PortTables.inputBits (PreprocessingStageMaps.regular H t))
      (MachineRegularTable.Top.timePolynomial.eval (GraphTables.tableBits t).length) where
  state := readyState H
  tapes := Function.update
    (initList (MachineRegularTable.Top.machine H) (GraphTables.tableBits t)).stk
    (coreTape 8) (PortTables.inputBits (PreprocessingStageMaps.regular H t))
  execution := by
    simpa only [sourceMachine_eq, FinTM2.Cfg, FinTM2.step, MachineRegularTable.Top.machine,
      PreprocessingMachineBounds.inputLength, PreprocessingStageMaps.regular,
      PortTables.inputBits] using!
      MachineRegularTable.Top.machineInTime H t
  output_eq := by
    simp only [rawProgram]
    erw [Function.update_self]

/-- The literal canonical output configuration computes the shared regular
preprocessing map, with the actual complete raw execution as its witness. -/
noncomputable def computableInPolyTime (H : PreprocessingRegularTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingRegularTables.internalDegree + 1))
      (PreprocessingStageMaps.regular H) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

/-- Finiteness refers to the exact machine in the preceding certificate. -/
theorem finite_alphabet (H : PreprocessingRegularTables.BaseTable) :
    ∀ k, Finite ((computableInPolyTime H).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H) cleanupTapes
    (cleanup_complete H) GraphTables.tableBits PortTables.inputBits
    (PreprocessingStageMaps.regular H) MachineRegularTable.Top.timePolynomial (terminalRun H)

end MaxCutGames.Foundations.Complexity.MachineRegularTableRuntime

/-!
A fixed five-tape machine physically copies a graph table, preserves the
original input, and splits its two unary header fields from the copied rows.
The exact trace is ambient-state polymorphic for static machine placement.
-/

namespace MaxCutGames.Foundations.Complexity.MachineTableSplit

open Turing MachineComposition

/-- Six finite control labels, independent of all input sizes and contents. -/
def program {σ : Type} : Label → TM2.Stmt (fun _ : Tape => Bool) Label (State σ)
  | .copyFirst => Reduction.MachineTransfer.loopAt 0 2 id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop 2 0 1 false .copySecond (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart 3 .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop 1 3 .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart 4 .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop 1 4 .readDarts none

theorem splitTrace {σ : Type} (n m : Nat) (rowsBits : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps n m rowsBits]
      (some ⟨some .copyFirst, (ambient, register),
        initialTapes (encodeWords [n, m] ++ rowsBits)⟩) =
      some ⟨none, (ambient, none), resultTapes n m rowsBits⟩ := by
  let word := encodeWords [n, m] ++ rowsBits
  let b₀ := initialTapes word
  let b₁ := tapes word word [] []
  let b₂ := tapes word (encodeWord m ++ rowsBits) (encodeWord n) []
  let b₃ := resultTapes n m rowsBits
  have h₀ : Function.update b₀ (1 : Tape) (b₀ 0 ++ b₀ 1) = b₁ := by
    funext k; fin_cases k <;> simp [b₀, b₁, initialTapes, tapes]
  have h₁ : Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ 3) = b₂ := by
    funext k; fin_cases k <;> simp [b₁, b₂, tapes, Hastad.SourceMachine.fieldTapes]
  have h₂ : Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂
      rowsBits (encodeWord m ++ b₂ 4) = b₃ := by
    funext k; fin_cases k <;>
      simp [b₂, b₃, resultTapes, tapes, word, Hastad.SourceMachine.fieldTapes]
  have copy := MachineCopy.copyTrace (0 : Tape) 1 2
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program (σ := σ)) rfl rfl b₀ (by simp [b₀, initialTapes, tapes]) ambient register
  rw [h₀] at copy
  have c₀ : (advance (TM2.step (program (σ := σ))))^[2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startVertices, (ambient, none), b₁⟩ := by
    simpa only [show b₀ 0 = word by simp [b₀, initialTapes, tapes]] using copy
  have scan₁ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 3 (by decide)
    .startVertices .readVertices (some .startDarts) (program (σ := σ)) rfl rfl
    b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, tapes, word, encodeWords, List.append_assoc]) ambient none).evals_in_steps
  have c₁ : (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₁
    change (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
      some ⟨some .startDarts, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁ (encodeWord m ++ rowsBits)
          (encodeWord n ++ b₁ 3)⟩ at scan₁
    simpa only [h₁] using scan₁
  have scan₂ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 4 (by decide)
    .startDarts .readDarts none (program (σ := σ)) rfl rfl
    b₂ m rowsBits (by simp [b₂, tapes]) ambient none).evals_in_steps
  have c₂ : (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₂
    change (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
      some ⟨none, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂ rowsBits
          (encodeWord m ++ b₂ 4)⟩ at scan₂
    simpa only [h₂] using scan₂
  have c₀₁ : (advance (TM2.step (program (σ := σ))))^[(n + 2) + 2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    rw [Function.iterate_add_apply, c₀, c₁]
  have c₀₁₂ : (advance (TM2.step (program (σ := σ))))^[(m + 2) +
      ((n + 2) + 2 * (word.length + 1))]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    rw [Function.iterate_add_apply, c₀₁, c₂]
  have count : exactSteps n m rowsBits = (m + 2) + ((n + 2) + 2 * (word.length + 1)) := by
    dsimp [exactSteps, word]
    omega
  rw [count]
  exact c₀₁₂

theorem tableTrace {σ : Type} (table : PCP.GraphTables.Table) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps table.vertices table.darts (rowsBits table)]
      (some ⟨some .copyFirst, (ambient, register), initialTapes (PCP.GraphTables.tableBits table)⟩) =
      some ⟨none, (ambient, none), resultTapes table.vertices table.darts (rowsBits table)⟩ := by
  rw [tableBits_header_rows]
  exact splitTrace table.vertices table.darts (rowsBits table) ambient register

end MaxCutGames.Foundations.Complexity.MachineTableSplit

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

namespace MaxCutGames.Foundations.Complexity.MachinePaddingBounds

/-- Exact variable-size input: two unary fields, unary fuel, and old output. -/
def inputSize (v e count : Nat) (output : List Bool) : Nat :=
  (encodeWord v).length + (encodeWord e).length + (encodeWord count).length + output.length

theorem rowBound_le_cap (d v e count : Nat) (output : List Bool) :
    rowBound d v e count ≤ rowCap d (inputSize v e count output) := by
  have hbase : v + e + count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hcount : count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hmul := Nat.mul_le_mul_right d (Nat.succ_le_succ hcount)
  have h := Nat.add_le_add_right (Nat.add_le_add hbase hmul) 8194
  simpa only [rowBound, rowCap, Nat.succ_eq_add_one, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

theorem timePolynomial_bounds (d v e count : Nat) (output : List Bool) :
    MachinePaddingRows.steps d v e output count ≤
      (timePolynomial d).eval (inputSize v e count output) := by
  have hc : count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have ho : output.length ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hb := rowBound_le_cap d v e count output
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_right d hc) hb
  have hout := Nat.add_le_add ho hp
  have hinner := Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left 4 hb) (Nat.mul_le_mul_left 2 hout)) 10
  have hbody := Nat.add_le_add_right (Nat.mul_le_mul_left d hinner) 2
  have h := (steps_le_bound d v e output count).trans
    (Nat.add_le_add_right (Nat.mul_le_mul hc hbody) 1)
  simpa only [timePolynomial, rowPolynomial, rowCap, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end MaxCutGames.Foundations.Complexity.MachinePaddingBounds

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

/-! Exact table-codec endpoint of the polynomial padding-row routine.
The caller supplies the physical unary counters and copied old-row buffer
with the updated headers. This theorem executes every added row and proves
that the resulting output is exactly the existing full table encoding. -/

namespace MaxCutGames.Foundations.Complexity.MachinePaddingTable

open PCP MachinePaddingRows

def execution {n d m : Nat} (table : PortTables.Table n d) (h : n ≤ m) (hd : 0 < d) :
    StateTransition.EvalsToInTime (machine d hd).step
      ⟨some (.inr .initialize_), (((), none), ()),
        initialTapes n (n * d) (m - n) (initialOutput (m := m) table)⟩
      (some (cfg d none m (m * d) 0
        (PortTables.tableBits (PreprocessingPaddingTables.pad table h))))
      ((MachinePaddingCertificate.timePolynomial d).eval
        (MachinePaddingBounds.inputSize n (n * d) (m - n) (initialOutput (m := m) table))) where
  steps := steps d n (n * d) (initialOutput (m := m) table) (m - n) + 1
  evals_in_steps := by
    have run := paddingTrace d hd (m - n) n (n * d) (initialOutput (m := m) table)
    have hv : n + (m - n) = m := Nat.add_sub_of_le h
    have he : n * d + (m - n) * d = m * d := by rw [← Nat.add_mul, hv]
    have hout : initialOutput (m := m) table ++ paddingBits d n (n * d) (m - n) =
        PortTables.tableBits (PreprocessingPaddingTables.pad table h) := by
      rw [PreprocessingPaddingWords.tableBits_pad]
      rfl
    rw [hv, he, hout] at run
    convert run using 1 ; rfl
  steps_le_m := by
    simp only [MachinePaddingCertificate.timePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.add_le_add_right
      (MachinePaddingBounds.timePolynomial_bounds d n (n * d) (m - n) (initialOutput (m := m) table)) 1

end MaxCutGames.Foundations.Complexity.MachinePaddingTable

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open MaxCutGames.Foundations.PCP
open MachineCloudPadding

def splitTape : MachineTableSplit.Tape → Tape := ![.original, .output, .scratch, .vertex, .edge]
def splitView : Tape → Option MachineTableSplit.Tape
  | .original => some 0
  | .output => some 1
  | .scratch => some 2
  | .vertex => some 3
  | .edge => some 4
  | _ => none

theorem splitView_left (k : MachineTableSplit.Tape) : splitView (splitTape k) = some k := by
  fin_cases k <;> rfl
theorem splitView_right (j : Tape) (k : MachineTableSplit.Tape)
    (h : splitView j = some k) : splitTape k = j := by
  cases j <;> fin_cases k <;> simp_all [splitView, splitTape]

def program {σ : Type} (d : Nat) (hd : 0 < d) : Label d → TM2.Stmt Alphabet (Label d) (State σ)
  | .splitCode l => Placement.statement splitTape Label.splitCode (some (.powerCode .init))
      (MachineTableSplit.program l)
  | .powerCode l => Placement.statement powerTape Label.powerCode (some .dartSeed)
      (MachineCeilingPower.program ExpanderFamily.growth l)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .power .scratch .output d .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .power .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .vertexRestore (some .copyFirst)
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .power .scratch id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .scratch .power .fuel false .copySecond (some (.subtractCode .subtract))
  | .subtractCode l => Placement.statement subtractTape Label.subtractCode
      (some (.rowsCode (.inr .initialize_))) (MachineCloudPadding.program l)
  | .rowsCode l => Placement.statement rowTape Label.rowsCode (some .cleanVertex) (rowProgram d hd l)
  | .cleanVertex => MachineDrain.drain .vertex .cleanVertex (some .cleanEdge)
  | .cleanEdge => MachineDrain.drain .edge .cleanEdge (some .cleanPower)
  | .cleanPower => MachineDrain.drain .power .cleanPower (some .cleanRelation)
  | .cleanRelation => MachineDrain.drain .relation .cleanRelation (some .cleanFuel)
  | .cleanFuel => MachineDrain.drain .fuel .cleanFuel none

theorem splitInitialTapes (word : List Bool) :
    Placement.tapes splitView (MachineTableSplit.initialTapes word) (fun _ => []) =
      memory word [] [] [] [] [] [] [] := by
  funext k; cases k <;> simp [Placement.tapes, splitView, MachineTableSplit.initialTapes,
    MachineTableSplit.tapes, memory]

theorem splitResultTapes (n e : Nat) (rows : List Bool) :
    Placement.tapes splitView (MachineTableSplit.resultTapes n e rows) (fun _ => []) =
      memory (encodeWords [n, e] ++ rows) rows (encodeWord n) (encodeWord e) [] [] [] [] := by
  funext k; cases k <;> simp [Placement.tapes, splitView, MachineTableSplit.resultTapes,
    MachineTableSplit.tapes, memory]

theorem splitTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineTableSplit.exactSteps n (n * d)
      (PreprocessingPaddingWords.rowsBits t)]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨some (.powerCode .init), ((ambient, false), none),
        memory (PortTables.tableBits t) (PreprocessingPaddingWords.rowsBits t)
          (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ := by
  have h := Placement.trace splitTape splitView splitView_left splitView_right
    (Label.splitCode (d := d)) (some (.powerCode .init)) (fun _ => [])
    (MachineTableSplit.program (σ := σ × Bool)) (program d hd) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n (n * d) (PreprocessingPaddingWords.rowsBits t)
      (ambient, false) register)
  simpa only [Placement.configuration, Placement.label, splitInitialTapes, splitResultTapes,
    ← tableBits_split] using h

theorem powerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge : List Bool) (n : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineCeilingPower.totalTime ExpanderFamily.growth n]
      (some ⟨some (.powerCode .init), ((ambient, false), register),
        memory input output (encodeWord n) edge [] [] [] []⟩) =
      some ⟨some .dartSeed, ((ambient, false), none),
        memory input output (encodeWord n) edge (encodeWord (PreprocessingLevels.paddedSize n))
          (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  have h := Placement.trace powerTape powerView powerView_left powerView_right
    (Label.powerCode (d := d)) (some .dartSeed) (memory input output [] edge [] [] [] [])
    (MachineCeilingPower.program ExpanderFamily.growth (σ := σ)) (program d hd)
    (fun _ => rfl) _ _ _ (MachineCeilingPower.paddingTrace n ambient register)
  simpa only [Placement.configuration, Placement.label, powerTapes] using h

theorem affineOutputTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (coefficient : Nat) (seed scan restore : Label d) (exit : Option (Label d))
    (atSeed : program (σ := σ) d hd seed = MachineUnaryAffineAt.seed (σ := σ × Bool) .output 0 scan)
    (atScan : program (σ := σ) d hd scan = MachineUnaryAffineAt.scan (σ := σ × Bool) .power .scratch .output
      coefficient scan restore)
    (atRestore : program (σ := σ) d hd restore = Reduction.MachineTransfer.loopAt (σ := σ × Bool)
      .scratch .power id false restore exit)
    (input output vertex edge level fuel relation : List Bool) (m : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[1 + 2 * (m + 1)]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨exit, ((ambient, false), none),
        memory input (encodeWord (coefficient * m) ++ output) vertex edge
          (encodeWord m) level fuel relation⟩ := by
  have hs : (advance (TM2.step (program d hd)))^[1]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨some scan, ((ambient, false), register),
        memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation⟩ := by
    change some (TM2.stepAux (program d hd seed) _ _) = _
    rw [atSeed]
    simp [MachineUnaryAffineAt.seed, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, encodeWord, memory]
  let base := memory input output vertex edge (encodeWord m) level fuel relation
  have ht := MachineUnaryAffineAt.affineTrace Tape.power Tape.scratch Tape.output
    (by decide) (by decide) (by decide) coefficient scan restore exit (program d hd)
    atScan atRestore base m 0 [] output (ambient, false) register
  have hstart : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord 0 ++ output) =
      memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  have hfinish : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord (coefficient * m + 0) ++ output) =
      memory input (encodeWord (coefficient * m) ++ output) vertex edge
        (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  rw [hstart, hfinish] at ht
  exact appendTrace_inline_MachineVertexPadding _ hs ht

theorem headersTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[4 * (m + 1) + 2]
      (some ⟨some .dartSeed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory input (encodeWords [m, m * d] ++ output) vertex edge (encodeWord m) level [] []⟩ := by
  have h₁ := affineOutputTrace d hd d .dartSeed .dartScan .dartRestore (some .vertexSeed)
    rfl rfl rfl input output vertex edge level [] [] m ambient register
  have h₂ := affineOutputTrace d hd 1 .vertexSeed .vertexScan .vertexRestore (some .copyFirst)
    rfl rfl rfl input (encodeWord (d * m) ++ output) vertex edge level [] [] m ambient none
  have h := appendTrace_inline_MachineVertexPadding _ h₁ h₂
  simpa only [Nat.one_mul, Nat.mul_comm d m, encodeWords, List.append_nil, List.append_assoc,
    show (1 + 2 * (m + 1)) + (1 + 2 * (m + 1)) = 4 * (m + 1) + 2 by omega] using h

theorem copyPowerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * (m + 2)]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some (.subtractCode .subtract), ((ambient, false), none),
        memory input output vertex edge (encodeWord m) level (encodeWord m) []⟩ := by
  have h := MachineCopy.copyTrace Tape.power Tape.fuel Tape.scratch
    (by decide) (by decide) (by decide) false (Label.copyFirst (d := d)) .copySecond
    (some (.subtractCode .subtract)) (program d hd) rfl rfl
    (memory input output vertex edge (encodeWord m) level [] []) rfl (ambient, false) register
  simpa only [memory, encodeWord_length, List.append_nil, update_fuel] using h

theorem subtractTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge power level : List Bool) (n m : Nat) (hnm : n ≤ m)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * n + 2]
      (some ⟨some (.subtractCode .subtract), ((ambient, false), register),
        memory input output (encodeWord n) edge power level (encodeWord m) []⟩) =
      some ⟨some (.rowsCode (.inr .initialize_)), ((ambient, false), none),
        memory input output (encodeWord n) edge power level (encodeWord (m - n)) []⟩ := by
  have h := Placement.trace subtractTape subtractView subtractView_left subtractView_right
    (Label.subtractCode (d := d)) (some (.rowsCode (.inr .initialize_)))
    (memory [] [] [] edge power [] [] [])
    (MachineCloudPadding.program (σ := σ)) (program d hd) (fun _ => rfl) _ _ _
    (MachineCloudPadding.subtractTrace input output level n m hnm ambient register)
  simpa only [Placement.configuration, Placement.label, subtractTapes] using h

theorem rowInitialTapes (input power level output : List Bool) (v e fuel : Nat) :
    Placement.tapes rowView (rowBoolTapes (MachinePaddingRows.initialTapes v e fuel output))
      (memory input [] [] [] power level [] []) =
      memory input output (encodeWord v) (encodeWord e) power level (encodeWord fuel) [] := by
  funext k
  cases k <;> rfl

theorem rowFinalTapes (input power level output : List Bool) (v e fuel : Nat) :
    Placement.tapes rowView (rowBoolTapes (MachinePaddingRows.tapes v e fuel output))
      (memory input [] [] [] power level [] []) =
      memory input output (encodeWord v) (encodeWord e) power level (encodeWord fuel)
        MachineDummyRows.trueBits := by
  funext k
  cases k <;> rfl

/-- The checked padding-row machine is transported through alphabet/state
equalities and a static tape placement. No row execution is assumed. -/
theorem rowsTrace {σ : Type} {n d m : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (hnm : n ≤ m) (input power level : List Bool) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[rowTime (m := m) t]
      (some ⟨some (.rowsCode (.inr .initialize_)), ((ambient, false), none),
        memory input (MachinePaddingTable.initialOutput (m := m) t)
          (encodeWord n) (encodeWord (n * d)) power level (encodeWord (m - n)) []⟩) =
      some ⟨some .cleanVertex, ((ambient, false), none),
        memory input (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))
          (encodeWord m) (encodeWord (m * d)) power level (encodeWord 0)
          MachineDummyRows.trueBits⟩ := by
  have hraw := (MachinePaddingTable.execution t hnm hd).evals_in_steps
  change (advance (TM2.step (MachinePaddingRows.program d hd)))^[rowTime (m := m) t]
    (some ⟨some (.inr .initialize_), (((), none), ()),
      MachinePaddingRows.initialTapes n (n * d) (m - n)
        (MachinePaddingTable.initialOutput (m := m) t)⟩) =
    some (MachinePaddingRows.cfg d none m (m * d) 0
      (PortTables.tableBits (PreprocessingPaddingTables.pad t hnm))) at hraw
  have hb := MachineAlphabetTransport.successfulTrace rowAlphabet_eq
    (MachinePaddingRows.program d hd) _ _ _ hraw
  have hf := frameTrace_inline_MachineVertexPadding
    (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd))
    (ambient, false) _ _ _ hb
  have hs := MachineStateEquiv.trace (rowStateEquiv σ)
    (MachineStateFrame.frameProgram
      (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd)))
    _ _ _ hf
  have hp := Placement.trace rowTape rowView rowView_left rowView_right
    (Label.rowsCode (d := d)) (some .cleanVertex) (memory input [] [] [] power level [] [])
    (rowProgram d hd (σ := σ)) (program d hd) (fun _ => rfl) _ _ _ hs
  simpa only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    MachineStateFrame.frameConfiguration, MachineAlphabetTransport.configuration_mk,
    rowCastTapes, MachinePaddingRows.cfg, rowStateEquiv, Equiv.coe_fn_mk,
    rowInitialTapes, rowFinalTapes] using hp

theorem cleanupTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output level : List Bool) (m : Nat) (ambient : σ) :
    (advance (TM2.step (program d hd)))^[cleanupTime d m]
      (some ⟨some .cleanVertex, ((ambient, false), none),
        memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
          (encodeWord 0) MachineDummyRows.trueBits⟩) =
      some ⟨none, ((ambient, false), none), memory input output [] [] [] level [] []⟩ := by
  have h₁ := (MachineDrain.drainInTime Tape.vertex (Label.cleanVertex (d := d)) (some .cleanEdge)
    (program d hd) rfl
    (memory input output (encodeWord m) (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₂ := (MachineDrain.drainInTime Tape.edge (Label.cleanEdge (d := d)) (some .cleanPower)
    (program d hd) rfl
    (memory input output [] (encodeWord (m * d)) (encodeWord m) level
      (encodeWord 0) MachineDummyRows.trueBits) (ambient, false) none).evals_in_steps
  have h₃ := (MachineDrain.drainInTime Tape.power (Label.cleanPower (d := d)) (some .cleanRelation)
    (program d hd) rfl
    (memory input output [] [] (encodeWord m) level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₄ := (MachineDrain.drainInTime Tape.relation (Label.cleanRelation (d := d)) (some .cleanFuel)
    (program d hd) rfl
    (memory input output [] [] [] level (encodeWord 0) MachineDummyRows.trueBits)
    (ambient, false) none).evals_in_steps
  have h₅ := (MachineDrain.drainInTime Tape.fuel (Label.cleanFuel (d := d)) none
    (program d hd) rfl (memory input output [] [] [] level (encodeWord 0) [])
    (ambient, false) none).evals_in_steps
  simp only [MachineDrain.drainInTime, memory, encodeWord_length, MachineDummyRows.trueBits_length,
    update_vertex, update_edge, update_power, update_relation, update_fuel] at h₁ h₂ h₃ h₄ h₅
  have h := appendTrace_inline_MachineVertexPadding _ (appendTrace_inline_MachineVertexPadding _ (appendTrace_inline_MachineVertexPadding _ (appendTrace_inline_MachineVertexPadding _ h₁ h₂) h₃) h₄) h₅
  have ht : cleanupTime d m = (((m + 2 + (m * d + 2)) + (m + 2)) + 8193) + 2 := by
    unfold cleanupTime
    omega
  rw [ht]
  exact h

/-- The whole table transformation begins with only its original encoding.
Every row-emitter counter and the updated prefix are produced by this run. -/
theorem vertexPaddingTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[totalTime t]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  let m := PreprocessingLevels.paddedSize n
  let level := encodeWord (PreprocessingLevels.boundedLevel n)
  let input := PortTables.tableBits t
  let rows := PreprocessingPaddingWords.rowsBits t
  let initialOutput := MachinePaddingTable.initialOutput (m := m) t
  have h₁ := splitTrace hd t ambient register
  have h₂ := powerTrace d hd input rows (encodeWord (n * d)) n ambient none
  have h₃ := headersTrace d hd input rows (encodeWord n) (encodeWord (n * d)) level m ambient none
  have h₄ := copyPowerTrace d hd input initialOutput (encodeWord n) (encodeWord (n * d))
    level m ambient none
  have h₅ := subtractTrace d hd input initialOutput (encodeWord (n * d)) (encodeWord m)
    level n m (PreprocessingLevels.le_paddedSize n) ambient none
  have h₆ := rowsTrace hd t (PreprocessingLevels.le_paddedSize n) input (encodeWord m) level ambient
  have h₇ := cleanupTrace d hd input
    (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
    level m ambient
  have h := appendTrace_inline_MachineVertexPadding _ (appendTrace_inline_MachineVertexPadding _ (appendTrace_inline_MachineVertexPadding _ (appendTrace_inline_MachineVertexPadding _
    (appendTrace_inline_MachineVertexPadding _ (appendTrace_inline_MachineVertexPadding _ h₁ h₂) h₃) h₄) h₅) h₆) h₇
  have ht : totalTime t =
      (((((MachineTableSplit.exactSteps n (n * d) rows +
        MachineCeilingPower.totalTime ExpanderFamily.growth n) + (4 * (m + 1) + 2)) +
        (2 * (m + 2))) + (2 * n + 2)) + rowTime (m := m) t) + cleanupTime d m := by
    dsimp only [totalTime, otherTime, m, rows]
    omega
  rw [ht]
  exact h

theorem intermediate_bound {n d : Nat} (t : PortTables.Table n d) :
    MachinePaddingBounds.inputSize n (n * d) (PreprocessingLevels.paddedSize n - n)
      (MachinePaddingTable.initialOutput (m := PreprocessingLevels.paddedSize n) t) ≤
      (intermediatePolynomial d).eval (PortTables.tableBits t).length := by
  have hn := PortTables.vertices_le_tableBits_length t
  have he := darts_length_le t
  have hr := rows_length_le t
  have hm := power_length_bound t
  have hs := Nat.sub_le (PreprocessingLevels.paddedSize n) n
  have hmul := Nat.mul_le_mul_left (d + 2) hm
  simp only [MachinePaddingBounds.inputSize, encodeWord_length, initialOutput_length,
    intermediatePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, intermediateCoefficient]
  nlinarith

theorem totalTime_le {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d) :
    totalTime t ≤ (timePolynomial d).eval (PortTables.tableBits t).length := by
  have hrow := (MachinePaddingTable.execution t (PreprocessingLevels.le_paddedSize n) hd).steps_le_m
  change rowTime (m := PreprocessingLevels.paddedSize n) t ≤
    (MachinePaddingCertificate.timePolynomial d).eval
      (MachinePaddingBounds.inputSize n (n * d) (PreprocessingLevels.paddedSize n - n)
        (MachinePaddingTable.initialOutput (m := PreprocessingLevels.paddedSize n) t)) at hrow
  have hmono := natPolynomial_eval_mono (MachinePaddingCertificate.timePolynomial d) (intermediate_bound t)
  have h := Nat.add_le_add (otherTime_le t) (hrow.trans hmono)
  simpa only [totalTime, timePolynomial, Polynomial.eval_add, Polynomial.eval_comp] using h

/-- Complete runtime certificate from the original input alone, with an
explicit clean final frame and an actual polynomial in its encoded length. -/
def vertexPaddingInTime {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program d hd))
      ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩
      (some ⟨none, ((ambient, false), none),
        memory (PortTables.tableBits t)
          (PortTables.tableBits (PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)))
          [] [] [] (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩)
      ((timePolynomial d).eval (PortTables.tableBits t).length) where
  steps := totalTime t
  evals_in_steps := vertexPaddingTrace hd t ambient register
  steps_le_m := totalTime_le hd t

end MaxCutGames.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineOverlayTable
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineOverlayTable

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

variable {A : Type} {d e : Nat}

/-- The checked splitter is placed directly in five homogeneous Boolean
stacks, with its actual halt replaced by the next preparation label. -/
def program (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    Label d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State A d e)
  | .inl l => Placement.statement Sum.inl Sum.inl (next .copyHFirst)
      (MachineTableSplit.program l)
  | .inr l => mainInstruction d e hd he l

def splitTapes (n m : Nat) (rows rawH : List Bool) : Tape → List Bool :=
  combine (MachineTableSplit.resultTapes n m rows) rawH

/-- The complete existing splitter is executed, retaining both archives. -/
theorem splitTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (table : GraphTables.Table) (rawH : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps
      table.vertices table.darts (MachineTableSplit.rowsBits table)]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (GraphTables.tableBits table) rawH⟩) =
      some ⟨next .copyHFirst, clean d e hd he a,
        splitTapes table.vertices table.darts (MachineTableSplit.rowsBits table) rawH⟩ := by
  let ambient := (clean d e hd he a).1
  have source := MachineTableSplit.tableTrace table ambient none
  have placed := Placement.trace (Sum.inl : Fin 5 → Tape) splitView (fun _ => rfl)
    (by intro j k h; cases j <;> simp_all [splitView])
    (Sum.inl : MachineTableSplit.Label → Label d e) (next .copyHFirst)
    (initialTapes [] rawH) MachineTableSplit.program (program d e hd he) (fun _ => rfl)
    _ _ _ source
  simp only [Placement.configuration, Placement.label] at placed
  rw [placedTapes, placedTapes] at placed
  simpa only [initialTapes,
    splitTapes, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using placed

theorem initialTapes_memory (g h : List Bool) :
    initialTapes g h = memory g h [] [] [] [] [] [] [] [] := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [initialTapes, combine, extraTapes, MachineTableSplit.initialTapes,
      MachineTableSplit.tapes, memory]

theorem splitTapes_memory (n m : Nat) (rows rawH : List Bool) :
    splitTapes n m rows rawH = memory (encodeWords [n, m] ++ rows) rawH rows []
      (encodeWord n) (encodeWord m) [] [] [] [] := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [splitTapes, combine, extraTapes, MachineTableSplit.resultTapes,
      MachineTableSplit.tapes, memory]

/-- Preserve and copy raw H, emit both output headers from the parsed unary
vertex count, copy the actual fuel field, and initialize_ the physical counter. -/
theorem preparationTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs : List Bool) (n m : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[preparationSteps n h]
      (some ⟨next .copyHFirst, clean d e hd he a,
        memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
  let b0 := memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []
  let b1 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] []
  let b2 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] (encodeWord ((d + e) * n))
  let b3 := memory g h gs h (encodeWord n) (encodeWord m) [] [] []
    (encodeWords [n, n * (d + e)])
  let b4 := memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) [] []
    (encodeWords [n, n * (d + e)])
  let ambient := (clean d e hd he a).1
  have hcopy := MachineCopy.copyTrace expanderArchive expanderStream scratch
    (by decide) (by decide) (by decide) false (.inr .copyHFirst) (.inr .copyHSecond)
    (next .countSeed) (program d e hd he) rfl rfl b0 rfl ambient none
  have copyRun : (advance (TM2.step (program d e hd he)))^[2 * (h.length + 1)]
      (some ⟨next .copyHFirst, clean d e hd he a, b0⟩) =
      some ⟨next .countSeed, clean d e hd he a, b1⟩ := by
    simpa only [b0, b1, memory_expanderArchive, memory_expanderStream, next, List.append_nil,
      update_expanderStream, ambient, clean, MachineLazyRows.streamClean,
      MachinePortReindex.clean] using hcopy
  have hcount := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) (d + e) 0
    (.inr .countSeed) (.inr .countScan) (.inr .countRestore) (next .headerSeed)
    (program d e hd he) rfl rfl rfl b1 n [] (by simp [b1, memory, vertexCount]) rfl ambient none
  have countRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .countSeed, clean d e hd he a, b1⟩) =
      some ⟨next .headerSeed, clean d e hd he a, b2⟩ := by
    simpa only [b1, b2, memory_output, next, List.append_nil, Nat.add_zero, update_output,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hcount
  have hheader := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) 1 0
    (.inr .headerSeed) (.inr .headerScan) (.inr .headerRestore) (next .fuelSeed)
    (program d e hd he) rfl rfl rfl b2 n [] (by simp [b2, memory, vertexCount]) rfl ambient none
  have headerRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .headerSeed, clean d e hd he a, b2⟩) =
      some ⟨next .fuelSeed, clean d e hd he a, b3⟩ := by
    simpa only [b2, b3, memory_output, next, Nat.one_mul, Nat.add_zero, update_output,
      Nat.mul_comm (d + e) n, encodeWords, List.append_nil,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hheader
  have hfuel := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch fuel
    (by decide) (by decide) (by decide) 1 0
    (.inr .fuelSeed) (.inr .fuelScan) (.inr .fuelRestore) (next .vertexSeed)
    (program d e hd he) rfl rfl rfl b3 n [] (by simp [b3, memory, vertexCount]) rfl ambient none
  have fuelRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .fuelSeed, clean d e hd he a, b3⟩) =
      some ⟨next .vertexSeed, clean d e hd he a, b4⟩ := by
    simpa only [b3, b4, memory_fuel, next, List.append_nil, Nat.one_mul, Nat.add_zero,
      update_fuel, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hfuel
  have seedRun : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .vertexSeed, clean d e hd he a, b4⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .vertexSeed)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, b4, memory_vertex,
      update_vertex, next, encodeWord, List.replicate_zero, List.nil_append]
  have all := joinTrace_inline_MachineOverlayTable (joinTrace_inline_MachineOverlayTable (joinTrace_inline_MachineOverlayTable (joinTrace_inline_MachineOverlayTable copyRun countRun) headerRun) fuelRun) seedRun
  have count : preparationSteps n h =
      (((2 * (h.length + 1) + (2 * (n + 1) + 1)) + (2 * (n + 1) + 1)) +
        (2 * (n + 1) + 1)) + 1 := by unfold preparationSteps; omega
  rw [count]
  exact all

theorem oldOutput_eq {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) :
    oldOutput G e v = encodeWords ((List.ofFn (oldRow G e v)).flatMap rowWords) := by
  rw [encodeWords_flatMap_inline_MachineOverlayTable]
  simp only [oldOutput, oldRows, MachineLazyRows.recordsOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  change MachineLazyRows.reindexRowBits d (d + e) 0 (row G v p).tail.val
    (row G v p).reverseIndex.val (row G v p).relation = encodeWords (rowWords (oldRow G e v p))
  rw [oldRow_words]
  simp only [MachineLazyRows.reindexRowBits, MachinePortReindex.value, Nat.add_zero,
    oldReverseMap, row, PreprocessingLazyWords.row, List.cons_append, List.nil_append,
    encodeWords, List.append_assoc]

theorem outputBlock_eq {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    outputBlock G H v = encodeWords ((vertexRows G H v).flatMap rowWords) := by
  rw [outputBlock, oldOutput_eq, expanderOutput_eq]
  simp only [vertexRows, List.flatMap_append, encodeWords_append]

theorem tableBits_blocks {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.tableBits (PreprocessingOverlayTables.overlay G H) =
      encodeWords [n, n * (d + e)] ++ (List.ofFn (outputBlock G H)).flatten := by
  rw [tableBits_overlay, encodeWords_append, encodeWords_flatten_flatMap_inline_MachineOverlayTable, List.map_ofFn]
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (outputBlock_eq G H v).symm

theorem oldVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (v : Fin n) (g h gs hs nv mv f current out : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineLazyRows.vertexSteps d (d + e) 0 (oldRows G v) out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) hs nv mv f current [] out⟩) =
      some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f current [] (out ++ oldOutput G e v)⟩ := by
  have hrun := MachineLazyRows.vertexTrace d hd (d + e) 0 oldTapes oldTapes_injective
    (fun stage => .inr (.old stage)) (next .tailSeed) (program d e hd he) (fun _ => rfl)
    (memory g h gs hs nv mv f current [] []) (row G v)
    (by
      intro i hi7 hi9
      fin_cases i <;> simp_all [oldTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, graphStream])
    (a, MachineFixedDivMod.residue e he 0) out
  simpa only [next, oldFrame, MachineLazyRows.recordsInput, List.flatMap_nil, List.nil_append,
    clean, oldBlock, oldRows, oldOutput] using hrun

theorem expanderVertexTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (H : ExpanderTables.Table n e) (v : Fin n) (g h gs hs nv mv f current out : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineOverlayRows.vertexSteps d e v.val
      (List.ofFn (expanderValues H v)) out]
      (some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs (expanderBlock H v ++ hs) nv mv f current (encodeWord v.val) out⟩) =
      some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f current (encodeWord v.val) (out ++ expanderOutput d H v)⟩ := by
  let source := MachineStateEquiv.program (expanderState A d e).symm (program d e hd he)
  have code (stage : MachineOverlayRows.VertexLabel e) : source (.inr (.expander stage)) =
      MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage := by
    change MachineStateEquiv.statement (expanderState A d e).symm
      (MachineStateEquiv.statement (expanderState A d e) _) = _
    exact MachineStateEquiv.statement_symm_statement _ _
  have native := MachineOverlayRows.vertexTrace d e he expanderTapes expanderTapes_injective
    (fun stage => .inr (.expander stage)) (next .drainTail) source code
    (memory g h gs hs nv mv f current (encodeWord v.val) []) v.val (expanderValues H v)
    rfl
    (by
      intro i hi0 hi7 hi9
      fin_cases i <;> simp_all [expanderTapes, memory, tail, oldReverse, relation, scratch,
        dividedCopy, quotient, newReverse, output, rowBuffer, expanderStream])
    ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0) out
  have transported := MachineStateEquiv.trace (expanderState A d e) source _ _ _ native
  have back : MachineStateEquiv.program (expanderState A d e) source = program d e hd he :=
    MachineStateEquiv.program_symm_program (expanderState A d e).symm _
  rw [back] at transported
  simpa only [next, MachineStateEquiv.configuration, expanderState_clean, expanderFrame,
    encodeWords, List.nil_append, expanderBlock, expanderOutput] using transported

theorem tailCopyTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[2 * (k + 1) + 1]
      (some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩ := by
  let ambient := (clean d e hd he a).1
  have hrun := MachineUnaryAffineAt.seededAffineTrace vertex scratch tail
    (by decide) (by decide) (by decide) 1 0
    (.inr .tailSeed) (.inr .tailScan) (.inr .tailRestore) (next (.expander (0, none)))
    (program d e hd he) rfl rfl rfl
    (memory g h gs hs nv mv f (encodeWord k) [] out) k []
    (by simp [memory, vertex]) rfl ambient none
  simpa only [memory_tail, next, List.append_nil, Nat.one_mul, Nat.add_zero, update_tail,
    ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hrun

theorem tailFinishTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[k + 3]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have hd₀ := MachineDrain.drainTrace tail (.inr .drainTail) (next .increment)
    (program d e hd he) rfl (memory g h gs hs nv mv f (encodeWord k) [] out)
    (encodeWord k) ambient none
  have drain : (advance (TM2.step (program d e hd he)))^[k + 2]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩ := by
    simpa only [next, encodeWord_length, Nat.add_assoc, update_tail, ambient, clean,
      MachineLazyRows.streamClean, MachinePortReindex.clean] using hd₀
  have increment : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .increment)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, memory_vertex, next,
      update_vertex, encodeWord, List.replicate_succ, List.cons_append]
  have all := joinTrace_inline_MachineOverlayTable drain increment
  simpa only [Nat.add_assoc] using all

/-- The complete old/expander pair for one actual vertex, with both physical
stream suffixes and the unchanged unary fuel accounted for. -/
theorem pairTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n)
    (g h gs hs nv mv f out : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[pairSteps G H v out]
      (some ⟨next (.old (0, none)), clean d e hd he a,
        memory g h (oldBlock G v ++ gs) (expanderBlock H v ++ hs)
          nv mv f (encodeWord v.val) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (v.val + 1)) [] (out ++ outputBlock G H v)⟩ := by
  have h₁ := oldVertexTrace d e hd he G v g h gs (expanderBlock H v ++ hs)
    nv mv f (encodeWord v.val) out a
  have h₂ := tailCopyTrace d e hd he g h gs (expanderBlock H v ++ hs)
    nv mv f (out ++ oldOutput G e v) v.val a
  have h₃ := expanderVertexTrace d e hd he H v g h gs hs nv mv f
    (encodeWord v.val) (out ++ oldOutput G e v) a
  have h₄ := tailFinishTrace d e hd he g h gs hs nv mv f
    ((out ++ oldOutput G e v) ++ expanderOutput d H v) v.val a
  simpa only [pairSteps, outputBlock, List.append_assoc] using
    joinTrace_inline_MachineOverlayTable (joinTrace_inline_MachineOverlayTable (joinTrace_inline_MachineOverlayTable h₁ h₂) h₃) h₄

theorem cleanupTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h out : List Bool) (n m : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[cleanupSteps n m]
      (some ⟨next .drainFuel, clean d e hd he a,
        memory g h [] [] (encodeWord n) (encodeWord m) (encodeWord 0) (encodeWord n) [] out⟩) =
      some ⟨none, clean d e hd he a, memory g h [] [] [] [] [] [] [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have h₁ := MachineDrain.drainTrace fuel (.inr .drainFuel) (next .drainVertex)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] (encodeWord n) [] out)
    (encodeWord 0) ambient none
  have h₂ := MachineDrain.drainTrace vertex (.inr .drainVertex) (next .drainVertexCount)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₃ := MachineDrain.drainTrace vertexCount (.inr .drainVertexCount) (next .drainDartCount)
    (program d e hd he) rfl (memory g h [] [] [] (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₄ := MachineDrain.drainTrace dartCount (.inr .drainDartCount) none
    (program d e hd he) rfl (memory g h [] [] [] [] [] [] [] out)
    (encodeWord m) ambient none
  simp only [encodeWord_length, update_fuel, update_vertex, update_vertexCount, update_dartCount] at h₁ h₂ h₃ h₄
  have all := joinTrace_inline_MachineOverlayTable (joinTrace_inline_MachineOverlayTable (joinTrace_inline_MachineOverlayTable h₁ h₂) h₃) h₄
  have hsteps : cleanupSteps n m = ((0 + 1 + 1 + (n + 1 + 1)) + (n + 1 + 1)) + (m + 1 + 1) := by
    unfold cleanupSteps
    omega
  rw [hsteps]
  exact all

def loopBase {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (r : Nat) : Tape → List Bool :=
  memory (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (n - r)) (remaining (expanderBlock H) (n - r))
    (encodeWord n) (encodeWord (n * d)) [] (encodeWord (n - r)) [] (outputPrefix G H (n - r))

/-- Each body premise needed by the generic unary counted-loop theorem is
constructed from the actual old/expander pair execution. -/
theorem loopBodyTraces {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    MachineCountedLoop.BodyTraces fuel (.inr .guard) (.inr (.old (0, none)))
      (program d e hd he) [] (fun _ => (clean d e hd he a).1) (fun _ => none)
      (loopBase G H) (loopCost G H) n := by
  intro r hr
  let v : Fin n := ⟨n - (r + 1), by omega⟩
  have hv : v.val + 1 = n - r := by dsimp [v]; omega
  have hinput : MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (oldBlock G v ++ remaining (oldBlock G) (v.val + 1))
        (expanderBlock H v ++ remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord v.val) []
        (outputPrefix G H v.val) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    change memory _ _ (remaining (oldBlock G) v.val) (remaining (expanderBlock H) v.val)
      _ _ _ _ _ _ = _
    rw [remaining_step (oldBlock G) v, remaining_step (expanderBlock H) v]
  have houtput : MachineUnaryCounter.counterTapes fuel (loopBase G H r) r [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
        (encodeWord n) (encodeWord (n * d)) (encodeWord r) (encodeWord (v.val + 1)) []
        (outputPrefix G H v.val ++ outputBlock G H v) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel]
    rw [← hv, outputPrefix_step]
  have run := pairTrace d e hd he G H v (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (v.val + 1)) (remaining (expanderBlock H) (v.val + 1))
    (encodeWord n) (encodeWord (n * d)) (encodeWord r) (outputPrefix G H v.val) a
  change (advance (TM2.step (program d e hd he)))^[loopCost G H r]
    (some ⟨next (.old (0, none)), clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H (r + 1)) r []⟩) =
    some ⟨next .guard, clean d e hd he a,
      MachineUnaryCounter.counterTapes fuel (loopBase G H r) r []⟩
  rw [hinput, houtput]
  simpa only [loopCost, dite_eq_left hr, v] using run

theorem loopTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineCountedLoop.totalSteps (loopCost G H) n]
      (some ⟨next .guard, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H)
          (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
          (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩) =
      some ⟨next .drainFuel, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] []
          (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have run := MachineCountedLoop.loopTrace fuel (.inr .guard) (.inr (.old (0, none)))
    (.inr .drainFuel) (program d e hd he) rfl []
    (fun _ => (clean d e hd he a).1) (fun _ => none) (loopBase G H) (loopCost G H) n
    (loopBodyTraces d e hd he G H a)
  have startFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H n) n [] =
      memory (PortTables.tableBits G) (rawExpander H)
        (MachineTableSplit.rowsBits (PortTables.graphTable G)) (rawExpander H)
        (encodeWord n) (encodeWord (n * d)) (encodeWord n) (encodeWord 0) []
        (encodeWords [n, n * (d + e)]) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_self, remaining_zero, outputPrefix, prefix_zero]
    simp only [graphRows_blocks, rawExpander, expanderRows_blocks]
  have endFrame : MachineUnaryCounter.counterTapes fuel (loopBase G H 0) 0 [] =
      memory (PortTables.tableBits G) (rawExpander H) [] []
        (encodeWord n) (encodeWord (n * d)) (encodeWord 0) (encodeWord n) []
        (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) := by
    simp only [MachineUnaryCounter.counterTapes, loopBase, List.append_nil, update_fuel,
      Nat.sub_zero, remaining_end, outputPrefix, prefix_end, tableBits_blocks]
  simp only [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration] at run
  rw [startFrame, endFrame] at run
  simpa only [next, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using run

theorem tableTrace {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    (advance (TM2.step (program d e hd he)))^[tableSteps G H]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
      some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩ := by
  have h₁ := splitTrace d e hd he (PortTables.graphTable G) (rawExpander H) a
  rw [splitTapes_memory] at h₁
  have header : encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G) =
      PortTables.tableBits G := (MachineTableSplit.tableBits_header_rows (PortTables.graphTable G)).symm
  change (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps n (n * d)
      (MachineTableSplit.rowsBits (PortTables.graphTable G))]
    (some ⟨some (.inl .copyFirst), clean d e hd he a,
      initialTapes (PortTables.tableBits G) (rawExpander H)⟩) =
    some ⟨next .copyHFirst, clean d e hd he a,
      memory (encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G))
        (rawExpander H) (MachineTableSplit.rowsBits (PortTables.graphTable G)) []
        (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ at h₁
  rw [header] at h₁
  have h₂ := preparationTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (MachineTableSplit.rowsBits (PortTables.graphTable G)) n (n * d) a
  have h₃ := loopTrace d e hd he G H a
  have h₄ := cleanupTrace d e hd he (PortTables.tableBits G) (rawExpander H)
    (PortTables.tableBits (PreprocessingOverlayTables.overlay G H)) n (n * d) a
  exact joinTrace_inline_MachineOverlayTable (joinTrace_inline_MachineOverlayTable (joinTrace_inline_MachineOverlayTable h₁ h₂) h₃) h₄

def tableInTime {n : Nat} (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (a : A) :
    StateTransition.EvalsToInTime (TM2.step (program d e hd he))
      ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (PortTables.tableBits G) (rawExpander H)⟩
      (some ⟨none, clean d e hd he a,
        memory (PortTables.tableBits G) (rawExpander H) [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingOverlayTables.overlay G H))⟩)
      ((timePolynomial d e).eval ((PortTables.tableBits G).length + (rawExpander H).length)) where
  steps := tableSteps G H
  evals_in_steps := tableTrace d e hd he G H a
  steps_le_m := tableSteps_le G H

end MaxCutGames.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePaddedOverlay
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical composition of vertex padding, expander generation, and overlay

The level produced by vertex padding is the family machine's actual input
stack. The two resulting archives are the overlay machine's actual archive
stacks. Static tape placement and finite-state framing preserve the original
input; no copying or recomputation is hidden in a phase boundary.
-/

namespace MaxCutGames.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

variable {d : Nat}

def overlaySource (d : Nat) (hd : 0 < d) : MachineOverlayTable.Label d overlayDegree →
    TM2.Stmt (fun _ : MachineOverlayTable.Tape => Bool) (MachineOverlayTable.Label d overlayDegree) (State d) :=
  MachineStateEquiv.program (overlayStates d) (MachineStateFrame.frameProgram
    (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive))

def program (H : BaseTable) (d : Nat) (hd : 0 < d) :
    Label d → TM2.Stmt Alphabet (Label d) (State d)
  | .inl l => Placement.statement paddingTape paddingLabel (some familyEntry) (MachineVertexPadding.program d hd l)
  | .inr (.inl l) => Placement.statement familyTape familyLabel (some overlayEntry)
      (familySource H d l)
  | .inr (.inr l) => Placement.statement overlayTape overlayLabel none (overlaySource d hd l)

def paddedTapes {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord (PreprocessingLevels.boundedLevel n)) [] [] []

def familyTapes (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord 0) (rotor H n) (encodeWord (PreprocessingLevels.paddedSize n)) []

def finalTapes (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord 0) (rotor H n) (encodeWord (PreprocessingLevels.paddedSize n))
    (PortTables.tableBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩).2)

/-- The actual padding execution stops at the family entry on the same
physical level stack, and preserves both inactive finite states. -/
noncomputable def paddingInTime (H : BaseTable) {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some main, clean H d hd, initialTapes t⟩
      (some ⟨some familyEntry, clean H d hd, paddedTapes t⟩)
      ((MachineVertexPadding.timePolynomial d).eval (PortTables.tableBits t).length) := by
  let ambient := (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H (),
    MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ())
  have run := placeExecution_inline_MachinePaddedOverlay paddingTape paddingView paddingView_left paddingView_right
    paddingLabel (some familyEntry) (fun _ => []) (MachineVertexPadding.program d hd) (program H d hd)
    (fun _ => rfl) (MachineVertexPadding.vertexPaddingInTime hd t ambient none)
  simpa only [Placement.configuration, Placement.label, padding_initial_memory,
    padding_final_memory, initialTapes, paddedTapes, padded, main, clean, ambient] using run

theorem family_initial_memory (input output : List Bool) (level : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes (MachineExpanderFamily.initialTapes level []))
      (memory input output (encodeWord level) [] [] []) =
      memory input output (encodeWord level) [] [] [] := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, familyView, memory,
      MachineVertexPadding.memory, MachineExpanderFamily.toBoolTapes,
      MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
      MachineEmbedding.tapes]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
            MachineExpanderFamily.tableFrame, MachineEmbedding.tapes]
      · cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
            MachineEmbedding.tapes]
    · rfl

theorem family_final_memory (H : BaseTable) (input output : List Bool) (level : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes (MachineExpanderFamily.familyTapes H level []))
      (memory input output (encodeWord level) [] [] []) =
      memory input output (encodeWord 0)
        (encodeWords (ExpanderTableWords.rotationWords (ExpanderTables.family H level)))
        (encodeWord (ExpanderTables.vertexCount overlayDegree level)) [] := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, familyView, memory,
      MachineVertexPadding.memory, MachineExpanderFamily.toBoolTapes,
      MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
      MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
      MachineEmbedding.tapes]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
            MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.tableFrame,
            MachineEmbedding.tapes]
      · cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
            MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
            MachineEmbedding.tapes, overlayDegree, PreprocessingRegularTables.internalDegree,
            ExpanderRowControl.degree]
    · simp [Placement.tapes, familyView, memory]

/-- The second phase executes the checked family program from the already
materialized level. Its runtime is polynomial in the original vertex count. -/
noncomputable def familyInTime (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some familyEntry, clean H d hd, paddedTapes t⟩
      (some ⟨some overlayEntry, clean H d hd, familyTapes H t⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
  let f := MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()
  let o := MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ()
  have caller : MachineExpanderFamily.caller f = () := Subsingleton.elim _ _
  have castRun := MachineAlphabetTransport.successfulExecutionInTime
    MachineExpanderFamily.alphabet_eq
    (MachineExpanderFamily.program MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)
    (MachineExpanderFamily.paddedFamilyInTime H n f [])
  have boolRun : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
        MachineExpanderFamily.baseDegree_cloud_gt_one))
      ⟨some (.inr .initialize_), f, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PreprocessingLevels.boundedLevel n) [])⟩
      (some ⟨none, f, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PreprocessingLevels.boundedLevel n) [])⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
    simpa only [MachineExpanderFamily.boolView, MachineExpanderFamily.configuration_toBool,
      caller] using castRun
  have framed := MachineStateFrame.frameExecution
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one) ((o, false), (none : Option Bool)) boolRun
  have transported := MachineStateEquiv.execution (familyStates d)
    (MachineStateFrame.frameProgram
      (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
        MachineExpanderFamily.baseDegree_cloud_gt_one)) framed
  have sourceRun : StateTransition.EvalsToInTime (TM2.step (familySource H d))
      ⟨some (.inr .initialize_), clean H d hd, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PreprocessingLevels.boundedLevel n) [])⟩
      (some ⟨none, clean H d hd, MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PreprocessingLevels.boundedLevel n) [])⟩)
      (MachineExpanderFamilyBounds.inputCoefficient * (n + 1)^5) := by
    simpa only [familySource, MachineStateEquiv.configuration,
      MachineStateFrame.frameConfiguration, Option.map_some, familyStates,
      Equiv.coe_fn_mk, clean, f, o]
      using transported
  have run := placeExecution_inline_MachinePaddedOverlay familyTape familyView familyView_left familyView_right
    familyLabel (some overlayEntry) (paddedTapes t) (familySource H d) (program H d hd)
    (fun _ => rfl) sourceRun
  have finishRaw := family_final_memory H (PortTables.tableBits t)
    (PortTables.tableBits (padded t)) (PreprocessingLevels.boundedLevel n)
  have hsize : ExpanderTables.vertexCount overlayDegree (PreprocessingLevels.boundedLevel n) =
      PreprocessingLevels.paddedSize n := PreprocessingLevels.table_vertexCount_eq_paddedSize n
  have count : memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
      (encodeWord 0) (rotor H n)
      (encodeWord (ExpanderTables.vertexCount overlayDegree (PreprocessingLevels.boundedLevel n))) [] =
      familyTapes H t :=
    congrArg (fun size => memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
      (encodeWord 0) (rotor H n) (encodeWord size) []) hsize
  have finish := finishRaw.trans count
  simpa only [Placement.configuration, Placement.label, paddedTapes,
    family_initial_memory, finish, familyEntry] using run

theorem overlay_memory (input graph raw count output : List Bool) :
    Placement.tapes overlayView
      (MachineOverlayTable.memory graph raw [] [] [] [] [] [] [] output)
      (memory input graph (encodeWord 0) raw count []) =
      memory input graph (encodeWord 0) raw count output := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, overlayView, memory, MachineVertexPadding.memory,
      MachineOverlayTable.memory, MachineOverlayTable.graphArchive]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, overlayView, memory, MachineExpanderFamily.tableTape,
            MachineOverlayTable.memory, MachineOverlayTable.expanderArchive]
      · cases k <;>
          simp [Placement.tapes, overlayView, memory, MachineExpanderFamily.tableTape,
            ]
    · rcases k with k | k <;> fin_cases k <;>
        simp [Placement.tapes, overlayView, memory, MachineOverlayTable.memory,
          MachineOverlayTable.graphArchive, MachineOverlayTable.expanderArchive,
          MachineOverlayTable.output]

/-- Overlay executes on the two archives physically produced above; only
its output stack changes in the retained outside frame. -/
noncomputable def overlayInTime (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some overlayEntry, clean H d hd, familyTapes H t⟩
      (some ⟨none, clean H d hd, finalTapes H t⟩)
      ((MachineOverlayTable.timePolynomial d overlayDegree).eval
        ((PortTables.tableBits (padded t)).length + (rotor H n).length)) := by
  let f := MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()
  have original := MachineOverlayTable.tableInTime d overlayDegree hd overlayDegree_positive
    (padded t) (PreprocessingStageMaps.familyAt H n) ()
  have framed := MachineStateFrame.frameExecution
    (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive)
    ((f, false), (none : Option Bool))
    original
  have transported := MachineStateEquiv.execution (overlayStates d)
    (MachineStateFrame.frameProgram
      (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive)) framed
  have sourceRun : StateTransition.EvalsToInTime (TM2.step (overlaySource d hd))
      ⟨some (.inl .copyFirst), clean H d hd,
        MachineOverlayTable.initialTapes (PortTables.tableBits (padded t)) (rotor H n)⟩
      (some ⟨none, clean H d hd,
        MachineOverlayTable.memory (PortTables.tableBits (padded t)) (rotor H n)
          [] [] [] [] [] [] []
          (PortTables.tableBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩).2)⟩)
      ((MachineOverlayTable.timePolynomial d overlayDegree).eval
        ((PortTables.tableBits (padded t)).length + (rotor H n).length)) := by
    simpa only [overlaySource, MachineStateEquiv.configuration,
      MachineStateFrame.frameConfiguration, Option.map_some, overlayStates, Equiv.coe_fn_mk, clean, f,
      rotor_familyAt, PreprocessingStageMaps.paddedOverlay, PreprocessingStageMaps.padding,
      padded] using transported
  have run := placeExecution_inline_MachinePaddedOverlay overlayTape overlayView overlayView_left overlayView_right
    overlayLabel none (familyTapes H t) (overlaySource d hd) (program H d hd)
    (fun _ => rfl) sourceRun
  simpa only [Placement.configuration, Placement.label, familyTapes, finalTapes,
    MachineOverlayTable.initialTapes_memory, overlay_memory, overlayEntry] using run

/-- The complete three-phase program executes from the original serialized
input alone, with a polynomial bound in that input's full unary length. -/
noncomputable def execution (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    StateTransition.EvalsToInTime (TM2.step (program H d hd))
      ⟨some main, clean H d hd, initialTapes t⟩
      (some ⟨none, clean H d hd, finalTapes H t⟩)
      ((timePolynomial d).eval (PortTables.tableBits t).length) := by
  let first := paddingInTime H hd t
  let second := familyInTime H hd t
  let third := overlayInTime H hd t
  let firstTwo := StateTransition.EvalsToInTime.trans (TM2.step (program H d hd))
    _ _ _ _ _ first second
  let all := StateTransition.EvalsToInTime.trans (TM2.step (program H d hd))
    _ _ _ _ _ firstTwo third
  refine { toEvalsTo := all.toEvalsTo, steps_le_m := all.steps_le_m.trans ?_ }
  have hn := PortTables.vertices_le_tableBits_length t
  have hf := Nat.mul_le_mul_left MachineExpanderFamilyBounds.inputCoefficient
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 5)
  have ho := natPolynomial_eval_mono (MachineOverlayTable.timePolynomial d overlayDegree)
    (archive_length_le H t)
  have h := Nat.add_le_add
    (Nat.add_le_add (Nat.le_refl ((MachineVertexPadding.timePolynomial d).eval
      (PortTables.tableBits t).length)) hf) ho
  simpa only [timePolynomial, familyPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def machine (H : BaseTable) (d : Nat) (hd : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .inl .original
  k₁ := .inr (.inr MachineOverlayTable.output)
  Γ := Alphabet
  Λ := Label d
  main := main
  σ := State d
  initialState := clean H d hd
  m := program H d hd

theorem initial_configuration (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    initList (machine H d hd) (PortTables.tableBits t) =
      ⟨some main, clean H d hd, initialTapes t⟩ := by
  have ht : (initList (machine H d hd) (PortTables.tableBits t)).stk = initialTapes t := by
    funext k
    rcases k with k | k
    · cases k <;> simp [initList, machine, initialTapes, memory, MachineVertexPadding.memory]
      rfl
    · rcases k with k | k
      · rcases k with k | k
        · rcases k with k | k <;> cases k <;>
            simp [initList, machine, initialTapes, memory]
        · cases k <;> simp [initList, machine, initialTapes, memory]
      · simp [initList, machine, initialTapes, memory]
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem final_output (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    finalTapes H t (machine H d hd).k₁ =
      PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩) := by
  simp [finalTapes, machine, memory, PortTables.inputBits]

end MaxCutGames.Foundations.Complexity.MachinePaddedOverlay

namespace MaxCutGames.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

def rawProgram (H : BaseTable) (d : Nat) (hd : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .inl .original
  output := .inr (.inr MachineOverlayTable.output)
  main := MachinePaddedOverlay.main
  initial := MachinePaddedOverlay.clean H d hd
  code := MachinePaddedOverlay.program H d hd

theorem cleanup_complete (H : BaseTable) (d : Nat) (hd : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H d hd).output := by
  simp [cleanupTapes, rawProgram]

theorem initial_configuration (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    initList (MachineCanonicalOutput.sourceMachine (rawProgram H d hd))
        (PortTables.inputBits a) =
      ⟨some MachinePaddedOverlay.main, MachinePaddedOverlay.clean H d hd,
        MachinePaddedOverlay.initialTapes a.2⟩ := by
  change initList (MachinePaddedOverlay.machine H d hd) (PortTables.tableBits a.2) = _
  exact MachinePaddedOverlay.initial_configuration H hd a.2

/-- The raw terminal witness is the actual three-phase execution. No phase
trace, output-size bound, or complexity assertion is an input hypothesis. -/
noncomputable def terminalRun (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram H d hd) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d a))
      ((MachinePaddedOverlay.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachinePaddedOverlay.clean H d hd
  tapes := MachinePaddedOverlay.finalTapes H a.2
  execution := by
    rw [initial_configuration]
    exact MachinePaddedOverlay.execution H hd a.2
  output_eq := MachinePaddedOverlay.final_output H hd a.2

/-- A concrete machine reaches the canonical `haltList` encoding of the
existing executable preprocessing map in polynomial time. -/
noncomputable def computableInPolyTime (H : BaseTable) (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := d + MachinePaddedOverlay.overlayDegree))
      (PreprocessingStageMaps.paddedOverlay H d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

/-- Finiteness belongs to the exact machine stored in the certificate above. -/
theorem finite_alphabet (H : BaseTable) (d : Nat) (hd : 0 < d) :
    ∀ k, Finite ((computableInPolyTime H d hd).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

end MaxCutGames.Foundations.Complexity.MachinePaddedOverlayRuntime

/-! Exact dummy-block codec used by the complete lazy-table machine. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTable
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual whole-table lazy-graph machine, with fixed positive old degree.
All unbounded counts and addresses reside on unary tapes. -/

namespace MaxCutGames.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

def program (d : Nat) (positive : 0 < d) :
    Label d → TM2.Stmt (fun _ : Tape => Bool) (Label d) (State d)
  | .split label => MachineCloudPadding.Placement.statement splitRoles Label.split
      (some .dartSeed) (MachineTableSplit.program label)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .darts .scratch .output 2 .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt .scratch .darts id false
      .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .vertices .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt .scratch .vertices id false
      .vertexRestore (some .fuelFirst)
  | .fuelFirst => Reduction.MachineTransfer.loopAt .vertices .scratch id false
      .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop .scratch .vertices .fuel false
      .fuelSecond (some .seedCounters)
  | .seedCounters => .push .vertex (fun _ => false)
      (.push .reverse (fun _ => false) (.goto fun _ => .guard))
  | .guard => MachineUnaryCounter.guard .fuel .copyVertexFirst .clearVertices
  | .copyVertexFirst => Reduction.MachineTransfer.loopAt .vertex .scratch id false
      .copyVertexFirst (some .copyVertexSecond)
  | .copyVertexSecond => MachineCopy.forkLoop .scratch .vertex .tail false
      .copyVertexSecond (some (.dummy (MachineDummyRows.start d)))
  | .dummy label => MachineCloudPadding.Placement.statement dummyRoles Label.dummy
      (some .clearDummyTail) (MachineDummyRows.program d label)
  | .clearDummyTail => MachineDrain.drain .tail .clearDummyTail (some .clearDummyRelation)
  | .clearDummyRelation => MachineDrain.drain .relation .clearDummyRelation (some (.oldRows (0, none)))
  | .oldRows label => MachineLazyRows.vertexInstruction d positive (2 * d) d oldRoles
      Label.oldRows (some .nextVertex) label
  | .nextVertex => pushWord .reverse (List.replicate d true)
      (.push .vertex (fun _ => true) (.goto fun _ => .guard))
  | .clearVertices => MachineDrain.drain .vertices .clearVertices (some .clearDarts)
  | .clearDarts => MachineDrain.drain .darts .clearDarts (some .clearFuel)
  | .clearFuel => MachineDrain.drain .fuel .clearFuel (some .clearVertex)
  | .clearVertex => MachineDrain.drain .vertex .clearVertex (some .clearReverse)
  | .clearReverse => MachineDrain.drain .reverse .clearReverse none

/-- Lift the actual dummy-block routine into the full program and account for
the exact preserved frame. The tail and relation are cleared in the next phase. -/
theorem dummyTrace (d : Nat) (positive : 0 < d) (base : Tape → List Bool) (v e : Nat)
    (ht : base .tail = encodeWord v) (he : base .reverse = encodeWord e)
    (hr : base .relation = []) (hb : base .rowBuffer = []) (hs : base .scratch = []) :
    (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v e (base .output) d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, base⟩) =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
          .relation MachineDummyRows.trueBits)
          .output (base .output ++ MachineDummyRows.rowsBits v e d)⟩ := by
  have initial : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.initialTapes v e (base .output)) base = base := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.initialTapes, MachineDummyRows.fieldTapes, ht, he, hr, hb, hs]
  have final : MachineCloudPadding.Placement.tapes dummyView
      (MachineDummyRows.fieldTapes v (e + d) (base .output ++ MachineDummyRows.rowsBits v e d))
      base = Function.update (Function.update (Function.update base .reverse (encodeWord (e + d)))
        .relation MachineDummyRows.trueBits)
        .output (base .output ++ MachineDummyRows.rowsBits v e d) := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, dummyView,
      MachineDummyRows.fieldTapes, ht, hb, hs]
  have run := MachineCloudPadding.Placement.trace dummyRoles dummyView
    dummyRoles_left dummyRoles_right Label.dummy (some .clearDummyTail) base
    (MachineDummyRows.program d) (program d positive) (fun _ => rfl) _ _ _
    (MachineDummyRows.allTrace d v e (base .output) (clean d positive).1 none)
  simpa only [clean_pair, MachineCloudPadding.Placement.configuration,
    MachineCloudPadding.Placement.label, initial, final] using run

theorem oldTrace {n m : Nat} (d : Nat) (positive : 0 < d)
    (base : Tape → List Bool) (rows : Fin d → GraphTables.DartRow n m) (rest : List Bool)
    (hi : base .source = MachineLazyRows.recordsInput (List.ofFn rows) ++ rest)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (oldRoles i) = []) :
    (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (base .output)]
      (some ⟨some (.oldRows (0, none)), clean d positive, base⟩) =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update base .source rest) .output
          (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows))⟩ := by
  let tailBase := Function.update base Tape.source rest
  have cleanBase : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → tailBase (oldRoles i) = [] := by
    intro i h7 h9
    have hn : oldRoles i ≠ Tape.source := by
      intro h
      have h' : oldRoles i = oldRoles 9 := h
      exact h9 (oldRoles_injective h')
    simpa only [tailBase, Function.update_of_ne hn] using empty i h7 h9
  have initial : MachineLazyRows.streamFrame oldRoles tailBase (List.ofFn rows) (base .output) = base := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, tailBase, oldRoles, hi]
  have final : MachineLazyRows.streamFrame (n := n) (m := m) oldRoles tailBase []
      (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) =
      Function.update (Function.update base .source rest) .output
        (base .output ++ MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)) := by
    funext t
    cases t <;> simp [MachineLazyRows.streamFrame, MachineLazyRows.recordsInput, tailBase, oldRoles]
  have run := MachineLazyRows.vertexTrace d positive (2 * d) d oldRoles oldRoles_injective
    Label.oldRows (some .nextVertex) (program d positive) (fun _ => rfl)
    tailBase rows cleanBase () (base .output)
  simpa only [initial, final, clean] using run

theorem prefixTrace (d : Nat) (positive : 0 < d) (n m : Nat) (rows : List Bool) :
    (advance (TM2.step (program d positive)))^[prefixSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive,
        initialTapes (encodeWords [n, m] ++ rows)⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d (encodeWords [n, m] ++ rows) n m n 0 rows (encodeWords [n, 2 * m])⟩ := by
  let word := encodeWords [n, m] ++ rows
  let header := encodeWords [n, 2 * m]
  let b₁ := frame word rows [] (encodeWord n) (encodeWord m) [] [] []
  let b₂ := frame word rows (encodeWord (2 * m)) (encodeWord n) (encodeWord m) [] [] []
  let b₃ := frame word rows header (encodeWord n) (encodeWord m) [] [] []
  let b₄ := frame word rows header (encodeWord n) (encodeWord m) (encodeWord n) [] []
  have hstart : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.initialTapes word) (fun _ => []) = initialTapes word := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.initialTapes, MachineTableSplit.tapes, initialTapes, frame]
  have hend : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.resultTapes n m rows) (fun _ => []) = b₁ := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.resultTapes, MachineTableSplit.tapes, b₁, frame, word]
  have split := MachineCloudPadding.Placement.trace splitRoles splitView
    splitRoles_left splitRoles_right Label.split (some .dartSeed) (fun _ => [])
    MachineTableSplit.program (program d positive) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n m rows (clean d positive).1 none)
  have c₀ : (advance (TM2.step (program d positive)))^[MachineTableSplit.exactSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes word⟩) =
      some ⟨some .dartSeed, clean d positive, b₁⟩ := by
    simp only [MachineCloudPadding.Placement.configuration,
      MachineCloudPadding.Placement.label] at split
    rw [hstart, hend] at split
    simpa only [clean_pair] using split
  have hdart : Function.update b₁ Tape.output (encodeWord (2 * m + 0) ++ b₁ .output) = b₂ := by
    funext t; cases t <;> simp [b₁, b₂, frame]
  have dart := MachineUnaryAffineAt.seededAffineTrace Tape.darts .scratch .output
    (by decide) (by decide) (by decide) 2 0 .dartSeed .dartScan .dartRestore
    (some .vertexSeed) (program d positive) rfl rfl rfl b₁ m []
    (by simp [b₁, frame]) rfl (clean d positive).1 none
  have c₁ : (advance (TM2.step (program d positive)))^[2 * (m + 1) + 1]
      (some ⟨some .dartSeed, clean d positive, b₁⟩) =
      some ⟨some .vertexSeed, clean d positive, b₂⟩ := by
    simpa only [hdart, clean_pair] using dart
  have hv : Function.update b₂ Tape.output (encodeWord (1 * n + 0) ++ b₂ .output) = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, frame, header, encodeWords]
  have vertex := MachineUnaryAffineAt.seededAffineTrace Tape.vertices .scratch .output
    (by decide) (by decide) (by decide) 1 0 .vertexSeed .vertexScan .vertexRestore
    (some .fuelFirst) (program d positive) rfl rfl rfl b₂ n []
    (by simp [b₂, frame]) rfl (clean d positive).1 none
  have c₂ : (advance (TM2.step (program d positive)))^[2 * (n + 1) + 1]
      (some ⟨some .vertexSeed, clean d positive, b₂⟩) =
      some ⟨some .fuelFirst, clean d positive, b₃⟩ := by
    simpa only [hv, clean_pair] using vertex
  have hf : Function.update b₃ Tape.fuel (b₃ .vertices ++ b₃ .fuel) = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have fuel := MachineCopy.copyTrace Tape.vertices .fuel .scratch
    (by decide) (by decide) (by decide) false .fuelFirst .fuelSecond
    (some .seedCounters) (program d positive) rfl rfl b₃ rfl (clean d positive).1 none
  rw [hf] at fuel
  have c₃ : (advance (TM2.step (program d positive)))^[2 * (n + 2)]
      (some ⟨some .fuelFirst, clean d positive, b₃⟩) =
      some ⟨some .seedCounters, clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .vertices = encodeWord n from rfl, encodeWord_length,
      Nat.add_assoc] using fuel
  have c₄ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .seedCounters, clean d positive, b₄⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d word n m n 0 rows header⟩ := by
    have ht : Function.update (Function.update b₄ Tape.vertex [false]) Tape.reverse [false] =
        loopTapes d word n m n 0 rows header := by
      funext t; cases t <;> simp [b₄, loopTapes, frame, encodeWord]
    simp only [Function.iterate_one, advance_some, TM2.step, program, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable c₀ c₁) c₂) c₃) c₄
  have hc : MachineTableSplit.exactSteps n m rows + (2 * (m + 1) + 1) +
      (2 * (n + 1) + 1) + 2 * (n + 2) + 1 = prefixSteps n m rows := by
    dsimp [MachineTableSplit.exactSteps, prefixSteps]
    omega
  rw [hc] at all
  exact all

/-- One entire vertex body: preserve-copy its tail, append the real dummy block,
clear its temporary fields, transform all old rows, and increment both counters
by actual pushes. The caller supplies no execution premise. -/
theorem bodyTrace {n m : Nat} (d : Nat) (positive : 0 < d) (input : List Bool)
    (left v : Nat) (rows : Fin d → GraphTables.DartRow n m) (rest output : List Bool) :
    (advance (TM2.step (program d positive)))^[bodySteps d v rows output]
      (some ⟨some .copyVertexFirst, clean d positive,
        loopTapes d input n m left v (MachineLazyRows.recordsInput (List.ofFn rows) ++ rest) output⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
  let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
  let dummy := MachineDummyRows.rowsBits v (2 * d * v) d
  let moving := MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)
  let b₀ := loopTapes d input n m left v source output
  let b₁ := Function.update b₀ Tape.tail (encodeWord v)
  let b₄ := frame input source (output ++ dummy) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  let b₂ := Function.update (Function.update b₄ Tape.tail (encodeWord v))
    Tape.relation MachineDummyRows.trueBits
  let b₃ := Function.update b₄ Tape.relation MachineDummyRows.trueBits
  let b₅ := frame input rest ((output ++ dummy) ++ moving) (encodeWord n) (encodeWord m)
    (encodeWord left) (encodeWord v) (encodeWord (2 * d * v + d))
  have hcopy : Function.update b₀ Tape.tail (b₀ .vertex ++ b₀ .tail) = b₁ := by
    simp [b₀, b₁, loopTapes, frame]
  have copy := MachineCopy.copyTrace Tape.vertex .tail .scratch
    (by decide) (by decide) (by decide) false .copyVertexFirst .copyVertexSecond
    (some (.dummy (MachineDummyRows.start d))) (program d positive) rfl rfl b₀ rfl
    (clean d positive).1 none
  rw [hcopy] at copy
  have c₀ : (advance (TM2.step (program d positive)))^[2 * (v + 2)]
      (some ⟨some .copyVertexFirst, clean d positive, b₀⟩) =
      some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩ := by
    simpa only [clean_pair, show b₀ .vertex = encodeWord v from rfl, encodeWord_length,
      Nat.add_assoc] using copy
  have hdummy : Function.update (Function.update (Function.update b₁ Tape.reverse
      (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
      Tape.output (b₁ .output ++ dummy) = b₂ := by
    funext t; cases t <;> simp [b₀, b₁, b₂, b₄, loopTapes, frame]
  have dummies := dummyTrace d positive b₁ v (2 * d * v)
    (by simp [b₁]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame]) (by simp [b₁, b₀, loopTapes, frame])
    (by simp [b₁, b₀, loopTapes, frame])
  have c₁ : (advance (TM2.step (program d positive)))^[MachineDummyRows.steps v
      (2 * d * v) output d + 1]
      (some ⟨some (.dummy (MachineDummyRows.start d)), clean d positive, b₁⟩) =
      some ⟨some .clearDummyTail, clean d positive, b₂⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .clearDummyTail, clean d positive,
        Function.update (Function.update (Function.update b₁ Tape.reverse
          (encodeWord (2 * d * v + d))) Tape.relation MachineDummyRows.trueBits)
          Tape.output (b₁ .output ++ dummy)⟩ at dummies
    rw [hdummy] at dummies
    simpa only [show b₁ .output = output by simp [b₁, b₀, loopTapes, frame]] using dummies
  have ht : Function.update b₂ Tape.tail [] = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, b₄, frame]
  have drainTail := MachineDrain.drainTrace Tape.tail .clearDummyTail (some .clearDummyRelation)
    (program d positive) rfl b₂ (b₂ .tail) (clean d positive).1 none
  simp only [Function.update_eq_self, ht] at drainTail
  have c₂ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearDummyTail, clean d positive, b₂⟩) =
      some ⟨some .clearDummyRelation, clean d positive, b₃⟩ := by
    simpa only [clean_pair, show b₂ .tail = encodeWord v by simp [b₂], encodeWord_length,
      Nat.add_assoc] using drainTail
  have hr : Function.update b₃ Tape.relation [] = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have drainRelation := MachineDrain.drainTrace Tape.relation .clearDummyRelation
    (some (.oldRows (0, none))) (program d positive) rfl b₃ (b₃ .relation)
    (clean d positive).1 none
  simp only [Function.update_eq_self, hr] at drainRelation
  have c₃ : (advance (TM2.step (program d positive)))^[8193]
      (some ⟨some .clearDummyRelation, clean d positive, b₃⟩) =
      some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .relation = MachineDummyRows.trueBits by simp [b₃],
      MachineDummyRows.trueBits_length] using drainRelation
  have hmoving : Function.update (Function.update b₄ Tape.source rest) Tape.output
      (b₄ .output ++ moving) = b₅ := by
    funext t; cases t <;> simp [b₄, b₅, frame]
  have old := oldTrace d positive b₄ rows rest rfl
    (fun i h7 h9 => frame_old_empty _ _ _ _ _ _ _ _ i h7 h9)
  have c₄ : (advance (TM2.step (program d positive)))^[MachineLazyRows.vertexSteps d (2 * d) d
      (List.ofFn rows) (output ++ dummy)]
      (some ⟨some (.oldRows (0, none)), clean d positive, b₄⟩) =
      some ⟨some .nextVertex, clean d positive, b₅⟩ := by
    change (advance (TM2.step (program d positive)))^[_] _ =
      some ⟨some .nextVertex, clean d positive,
        Function.update (Function.update b₄ Tape.source rest) Tape.output
          (b₄ .output ++ moving)⟩ at old
    rw [hmoving] at old
    exact old
  have c₅ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .nextVertex, clean d positive, b₅⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows)⟩ := by
    have hrev : List.replicate d true ++ encodeWord (2 * d * v + d) =
        encodeWord (2 * d * (v + 1)) := by
      have hw := MachineUnaryAffineAt.prepend_replicate_word d (2 * d * v + d) []
      simp only [List.append_nil] at hw
      rw [hw]
      exact congrArg encodeWord (show d + (2 * d * v + d) = 2 * d * (v + 1) by
        simp only [Nat.mul_add, Nat.mul_one]
        omega)
    have ht : Function.update (Function.update b₅ Tape.reverse
        ((List.replicate d true).reverse ++ b₅ .reverse)) Tape.vertex (true :: b₅ .vertex) =
        loopTapes d input n m left (v + 1) rest (output ++ vertexBlock d v rows) := by
      funext t
      cases t <;> simp [b₅, frame, loopTapes, vertexBlock, dummy, moving,
        hrev, List.append_assoc]
      simp [encodeWord, List.replicate_succ]
    simp only [Function.iterate_one, advance_some, TM2.step, program,
      stepAux_pushWord, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable c₀ c₁) c₂) c₃) c₄) c₅
  exact all

theorem drainPhase (d : Nat) (positive : 0 < d) (tape : Tape) (label : Label d)
    (exit : Option (Label d))
    (atLabel : program d positive label = MachineDrain.drain tape label exit)
    (base : Tape → List Bool) :
    (advance (TM2.step (program d positive)))^[(base tape).length + 1]
      (some ⟨some label, clean d positive, base⟩) =
      some ⟨exit, clean d positive, Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self, clean_pair] using
    MachineDrain.drainTrace tape label exit (program d positive) atLabel base
      (base tape) (clean d positive).1 none

theorem finishTrace (d : Nat) (positive : 0 < d) (input output : List Bool) (n m v : Nat) :
    (advance (TM2.step (program d positive)))^[finishSteps d n m v]
      (some ⟨some .guard, clean d positive, loopTapes d input n m 0 v [] output⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
  let b₀ := loopTapes d input n m 0 v [] output
  let b₁ := Function.update b₀ Tape.vertices []
  let b₂ := Function.update b₁ Tape.darts []
  let b₃ := Function.update b₂ Tape.fuel []
  let b₄ := Function.update b₃ Tape.vertex []
  have hframe : MachineUnaryCounter.counterTapes Tape.fuel b₀ 0 [] = b₀ := by
    funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
  have guard := MachineUnaryCounter.guardTrace_zero Tape.fuel .guard .copyVertexFirst
    .clearVertices (program d positive) rfl b₀ [] (clean d positive).1 none
  have c₀ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .guard, clean d positive, b₀⟩) =
      some ⟨some .clearVertices, clean d positive, b₀⟩ := by
    simpa only [hframe, clean_pair] using guard
  have c₁ : (advance (TM2.step (program d positive)))^[n + 2]
      (some ⟨some .clearVertices, clean d positive, b₀⟩) =
      some ⟨some .clearDarts, clean d positive, b₁⟩ := by
    simpa only [show b₀ .vertices = encodeWord n from rfl, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertices .clearVertices (some .clearDarts) rfl b₀
  have c₂ : (advance (TM2.step (program d positive)))^[m + 2]
      (some ⟨some .clearDarts, clean d positive, b₁⟩) =
      some ⟨some .clearFuel, clean d positive, b₂⟩ := by
    have hv : b₁ .darts = encodeWord m := by simp [b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .darts .clearDarts (some .clearFuel) rfl b₁
  have c₃ : (advance (TM2.step (program d positive)))^[2]
      (some ⟨some .clearFuel, clean d positive, b₂⟩) =
      some ⟨some .clearVertex, clean d positive, b₃⟩ := by
    have hv : b₂ .fuel = encodeWord 0 := by simp [b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length] using
      drainPhase d positive .fuel .clearFuel (some .clearVertex) rfl b₂
  have c₄ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearVertex, clean d positive, b₃⟩) =
      some ⟨some .clearReverse, clean d positive, b₄⟩ := by
    have hv : b₃ .vertex = encodeWord v := by simp [b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertex .clearVertex (some .clearReverse) rfl b₃
  have hend : Function.update b₄ Tape.reverse [] = finalTapes input output := by
    funext t; cases t <;> simp [b₄, b₃, b₂, b₁, b₀, loopTapes, finalTapes, frame]
  have c₅ : (advance (TM2.step (program d positive)))^[2 * d * v + 2]
      (some ⟨some .clearReverse, clean d positive, b₄⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
    have hv : b₄ .reverse = encodeWord (2 * d * v) := by
      simp [b₄, b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc, hend] using
      drainPhase d positive .reverse .clearReverse none rfl b₄
  have all := joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable c₀ c₁) c₂) c₃) c₄) c₅
  have hc : 1 + (n + 2) + (m + 2) + 2 + (v + 2) + (2 * d * v + 2) =
      finishSteps d n m v := by dsimp [finishSteps]; omega
  rw [hc] at all
  exact all

/-- Induction over the actual unary fuel and the actual stored vertex order. -/
theorem loopTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d)
    (input : List Bool) (count r : Nat) (hsum : r + count = n) (output : List Bool) :
    (advance (TM2.step (program d positive)))^[loopSteps table r count output]
      (some ⟨some .guard, clean d positive,
        loopTapes d input n (n * d) count r (inputBlocks table (remaining n r)) output⟩) =
      some ⟨none, clean d positive,
        finalTapes input (output ++ outputBlocks table (remaining n r))⟩ := by
  induction count generalizing r output with
  | zero =>
    have hr : r = n := by omega
    subst r
    simpa only [loopSteps, remaining_done, inputBlocks, outputBlocks, List.flatMap_nil,
      List.append_nil] using finishTrace d positive input output n (n * d) n
  | succ count ih =>
    have hr : r < n := by omega
    let rows := PreprocessingLazyWords.row table (⟨r, hr⟩ : Fin n)
    let rest := inputBlocks table (remaining n (r + 1))
    let source := MachineLazyRows.recordsInput (List.ofFn rows) ++ rest
    let b₀ := loopTapes d input n (n * d) (count + 1) r source output
    let b₁ := loopTapes d input n (n * d) count r source output
    have hguard (k : Nat) : MachineUnaryCounter.counterTapes Tape.fuel b₀ k [] =
        loopTapes d input n (n * d) k r source output := by
      funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
    have guard := MachineUnaryCounter.guardTrace_succ Tape.fuel .guard .copyVertexFirst
      .clearVertices (program d positive) rfl b₀ count [] (clean d positive).1 none
    have c₀ : (advance (TM2.step (program d positive)))^[1]
        (some ⟨some .guard, clean d positive, b₀⟩) =
        some ⟨some .copyVertexFirst, clean d positive, b₁⟩ := by
      simpa only [hguard, clean_pair] using guard
    have c₁ := bodyTrace d positive input count r rows rest output
    have c₂ := ih (r + 1) (by omega) (output ++ vertexBlock d r rows)
    have all := joinTrace_inline_MachineLazyTable (joinTrace_inline_MachineLazyTable c₀ c₁) c₂
    have hi : inputBlocks table (remaining n r) = source := by
      rw [remaining_cons n r hr]
      rfl
    have ho : outputBlocks table (remaining n r) =
        vertexBlock d r rows ++ outputBlocks table (remaining n (r + 1)) := by
      rw [remaining_cons n r hr]
      rfl
    simpa only [loopSteps, dite_eq_left hr, hi, ho, List.append_assoc] using all

/-- The full table execution, including all headers, all dummy and moving
rows, and complete work-tape cleanup, in the existing exact Boolean codec. -/
theorem tableTrace {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    (advance (TM2.step (program d positive)))^[totalSteps table]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes (PortTables.tableBits table)⟩) =
      some ⟨none, clean d positive,
        finalTapes (PortTables.tableBits table)
          (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩ := by
  have prefixRun := prefixTrace d positive n (n * d) (inputBlocks table (List.finRange n))
  rw [← input_table_codec table] at prefixRun
  have loop := loopTrace table positive (PortTables.tableBits table) n 0 (by omega)
    (encodeWords [n, 2 * (n * d)])
  simp only [remaining_zero] at loop
  have all := joinTrace_inline_MachineLazyTable prefixRun loop
  rw [← output_table_codec table] at all
  exact all

def machine (d : Nat) (positive : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label d
  main := .split .copyFirst
  σ := State d
  initialState := clean d positive
  m := program d positive

theorem initial_configuration (d : Nat) (positive : 0 < d) (input : List Bool) :
    initList (machine d positive) input =
      ⟨some (.split .copyFirst), clean d positive, initialTapes input⟩ := by
  have ht : (initList (machine d positive) input).stk = initialTapes input := by
    funext t
    cases t <;> simp [initList, machine, initialTapes, frame]
    rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- A full actual finite-machine execution with a fixed-degree polynomial
budget, the exact lazy-table output, preserved original input, and clean work. -/
def machineInTime {n d : Nat} (table : PortTables.Table n d) (positive : 0 < d) :
    StateTransition.EvalsToInTime (machine d positive).step
      (initList (machine d positive) (PortTables.tableBits table))
      (some ⟨none, clean d positive, finalTapes (PortTables.tableBits table)
        (PortTables.tableBits (PreprocessingOverlayTables.lazy table))⟩)
      ((timePolynomial d).eval (PortTables.tableBits table).length) where
  steps := totalSteps table
  evals_in_steps := by
    rw [initial_configuration]
    exact tableTrace table positive
  steps_le_m := totalSteps_le table

end MaxCutGames.Foundations.Complexity.MachineLazyTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label State)

def rawProgram (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .input
  output := .output
  main := .split .copyFirst
  initial := MachineLazyTable.clean d positive
  code := MachineLazyTable.program d positive

theorem cleanup_complete (d : Nat) (positive : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram d positive).output := by
  cases k <;> simp [cleanupTapes, rawProgram]

/-- The terminal witness is the checked full lazy-table execution. The wrapper
then drains the retained original input rather than assuming it disappeared. -/
def terminalRun (d : Nat) (positive : 0 < d) (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram d positive) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
      ((MachineLazyTable.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachineLazyTable.clean d positive
  tapes := MachineLazyTable.finalTapes (PortTables.inputBits a)
    (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
  execution := MachineLazyTable.machineInTime a.2 positive
  output_eq := rfl

/-- The actual canonical-output finite machine computes precisely the shared
degree-d to degree-2d stage map in polynomial time. -/
noncomputable def computableInPolyTime (d : Nat) (positive : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * d)) (PreprocessingStageMaps.lazy d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

/-- Every tape alphabet of this exact completed computation certificate is finite. -/
theorem finite_alphabet (d : Nat) (positive : 0 < d) :
    ∀ k, Finite ((computableInPolyTime d positive).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

end MaxCutGames.Foundations.Complexity.MachineLazyTableRuntime

/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/

/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/

/-!
An actual logarithmic-round counter. Unary input is stripped to a raw tally;
each positive round emits one tally and halves the remaining input by pairing
symbols. The zero input emits one round explicitly. All tapes except the
canonical output are empty at termination.
-/

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace MaxCutGames.Foundations.PCP.RoundTables

theorem gap_nonnegative (input : Input) : 0 ≤ gap input :=
  (GraphTables.semantics input.val).gap_nonnegative

theorem initial_satisfiable_iff (F : Target.Formula) : Satisfiable (initial F) ↔ F.Satisfiable :=
  RawInitialTables.table_satisfiable_iff F

end MaxCutGames.Foundations.PCP.RoundTables

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTableIteration
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial-time iteration of the concrete graph-table round. A
certificate for that one body is the only supplied machine input. Counter
preparation, repeated calls, tape handoffs, and final cleanup are all proved. -/

namespace MaxCutGames.Foundations.Complexity.MachineTableIteration

open Turing PCP RoundTables GraphIterationBounds

def finalTable (H : BaseTable) (input : Input) : GraphTables.Table :=
  TableIteration.runTables H (count input) input.val

noncomputable def counterCertificate : TM2ComputableInPolyTime inputBits countedBits (id : Input → Input) where
  toTM2ComputableAux := GraphCounterPrefix.computableInPolyTime.toTM2ComputableAux
  time := GraphCounterPrefix.computableInPolyTime.time
  outputsFun input := GraphCounterPrefix.computableInPolyTime.outputsFun input.val

variable (H : BaseTable)
  (body : TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits (build H))

/-- The generic repeat machine executes only the actual successive graph words.
Its polynomial bound uses the proved linear growth of their semantic sizes. -/
noncomputable def countedCertificate :
    TM2ComputableInPolyTime countedBits GraphTables.tableBits (finalTable H) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := runtimePolynomial body.time
  outputsFun input := by
    let budgets := fun i => body.time.eval (words H input i).length
    have runs (i : Nat) (_hi : i < count input) :
        TM2OutputsInTime body.tm ((words H input i).map body.inputAlphabet.symm)
          (some ((words H input (i + 1)).map body.outputAlphabet.symm)) (budgets i) := by
      exact body.outputsFun (TableIteration.runTables H i input.val)
    let run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      (count input) (words H input) budgets runs
    have start : encodeWord (count input) ++ words H input 0 = countedBits input := rfl
    have finish : words H input (count input) = GraphTables.tableBits (finalTable H input) := rfl
    rw [start, finish] at run
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    let N := (countedBits input).length
    let L := lengthPolynomial.eval N
    let B := body.time.eval L
    have hl (i : Nat) (hi : i ≤ count input) : (words H input i).length ≤ L :=
      intermediate_bits H input i hi
    have hb (i : Nat) (hi : i < count input) : budgets i ≤ B :=
      MachineComposition.natPolynomial_eval_mono body.time (hl i hi.le)
    have hloop := MachineRepeat.loopBudget_le (count input) (words H input) budgets B L hb hl
    have hc : count input ≤ N + 1 := count_le input
    rw [runtimePolynomial_eval]
    calc
      run.steps ≤ count input + 1 + MachineRepeat.loopBudget (count input) (words H input) budgets :=
        run.steps_le_m
      _ ≤ count input + 1 + (count input * (B + 2 * L + 3) + 2 * L + 3) :=
        Nat.add_le_add_left hloop _
      _ = count input * (B + 2 * L + 4) + 2 * L + 4 := by ring
      _ ≤ (N + 1) * (B + 2 * L + 4) + 2 * L + 4 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _) _

/-- One actual finite machine computes the complete logarithmic iteration. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputBits GraphTables.tableBits (finalTable H) :=
  MachineSequential.composeBits counterCertificate (countedCertificate H body)

noncomputable def initialCertificate :
    TM2ComputableInPolyTime formulaBits inputBits initial where
  toTM2ComputableAux := MachineRawInitialTable.computableInPolyTime.toTM2ComputableAux
  time := MachineRawInitialTable.computableInPolyTime.time
  outputsFun F := MachineRawInitialTable.computableInPolyTime.outputsFun F

/-- The initial graph and entire repeated table transformation have concrete
finite-machine executions with the same formula and table encodings. -/
noncomputable def tableCertificate :
    TM2ComputableInPolyTime formulaBits GraphTables.tableBits (TableIteration.outputTable H) := by
  change TM2ComputableInPolyTime formulaBits GraphTables.tableBits
    (fun F => finalTable H (initial F))
  exact MachineSequential.composeBits (f := initial) (g := finalTable H)
    initialCertificate (computableInPolyTime H body)

/-- Actual 3SAT gap-map runtime follows from the one concrete round certificate;
initialization, variable repetition, and the final CNF converter are supplied. -/
noncomputable def gapMapCertificate :
    TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H) :=
  MachineSequential.composeBits (f := TableIteration.outputTable H) (g := FinalTableFormula.output)
    (tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime

end MaxCutGames.Foundations.Complexity.MachineTableIteration

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete execution of the one fixed powering machine on the actual
port-table input and generic graph-table output encodings. The varying vertex
count remains on unary tapes throughout. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRuntime

open Turing MachineComposition PCP PoweringMachineGlobal

variable {vertices d : Nat}

def finishConfiguration (graph : PortTables.Table vertices d) (n : Nat) : (machine d n).Cfg :=
  ⟨some (finishEntry d n), PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
    beforeFinish graph n⟩

/-- Initialization and the actual outer loop's proved budgets. -/
def beforeFinishBudget (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  (3 * vertices + 5) + (vertices *
    (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1)

end MaxCutGames.Foundations.Complexity.PoweringMachineRuntime

end OAI
end


