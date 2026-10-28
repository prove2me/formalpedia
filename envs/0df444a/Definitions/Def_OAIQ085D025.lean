-- Prove2me | Definitions.Def_OAIQ085D025
-- name    : OAIQ085D025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:40:44.573285+00:00
-- url     : https://prove2.me/theorems/b7c41474-6166-420e-acb4-4360ea9eddac
-- title:
--   Definitions bundle OAIQ085D025 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 243 declarations of OpenAI's Lean: 108 definitions and 135 theorems. The definitions and types are `OAI.DFVSGames.Explicit.MachineUniformHeaders.headersInTime`, `OAI.DFVSGames.Explicit.MachineUniformProgram.machine`, `OAI.DFVSGames.Explicit.MachineUniformProgram.program`, `OAI.DFVSGames.Explicit.MachineUniformRun.emitInTime`, `OAI.DFVSGames.Explicit.MachineUniformRun.finishStartInTime`, `OAI.DFVSGames.Explicit.MachineUniformRun.prefixInTime`, `OAI.DFVSGames.Explicit.MachineUniformRun.scaleInTime`, `OAI.DFVSGames.Explicit.MachineUniformRun.timePolynomial`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.headPhaseInTime`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.relationInTime`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.rowInTime`, `OAI.DFVSGames.Foundations.Complexity.GraphCounterFinish.finishInTime`, `OAI.DFVSGames.Foundations.Complexity.GraphCounterModel.clockInTime`, `OAI.DFVSGames.Foundations.Complexity.GraphCounterPrefix.computableInPolyTime`, `OAI.DFVSGames.Foundations.Complexity.GraphCounterPrefix.output`, `OAI.DFVSGames.Foundations.Complexity.GraphCounterPrefix.outputsInTime`, `OAI.DFVSGames.Foundations.Complexity.GraphCounterPrefix.rawInTime`, `OAI.DFVSGames.Foundations.Complexity.GraphIterationBounds.count`, `OAI.DFVSGames.Foundations.Complexity.GraphIterationBounds.countedBits`, `OAI.DFVSGames.Foundations.Complexity.GraphIterationBounds.inputBits`, `OAI.DFVSGames.Foundations.Complexity.GraphIterationBounds.words`, `OAI.DFVSGames.Foundations.Complexity.MachineCanonicalOutput.cleanupExecution`, `OAI.DFVSGames.Foundations.Complexity.MachineCanonicalOutput.computableInPolyTime`, `OAI.DFVSGames.Foundations.Complexity.MachineCanonicalOutput.outputsInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.familyInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.levelLoopInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.paddedFamilyInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.resizeInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderRow.rowInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderRow.rowInTimeAt`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.preparedRowInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.suffixInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.suffixRun_aux_inline_MachineExpanderTableRows`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.tableInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.vertexInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.vertexLoopInTime`, `OAI.DFVSGames.Foundations.Complexity.MachineLazyRows.streamInstruction`, `OAI.DFVSGames.Foundations.Complexity.MachineLazyRows.streamRelationCopy`, `OAI.DFVSGames.Foundations.Complexity.MachineLazyRows.vertexInstruction`, `OAI.DFVSGames.Foundations.Complexity.MachineLazyTable.bodySteps` and 68 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Encoding_Lookup`, `DirectedFeedback_Encoding_PreprocessingStageMaps`, `DirectedFeedback_Encoding_TableIteration`, `DirectedFeedback_Games_InitialGraph`, `DirectedFeedback_Games_Target`, `DirectedFeedback_Machines_FinalCNFHeader`, `DirectedFeedback_Machines_FinalCNFStream`, `DirectedFeedback_Machines_GraphCounterFinish`, `DirectedFeedback_Machines_MachineDummyRows`, `DirectedFeedback_Machines_MachineExpanderFamilyLoop`, `DirectedFeedback_Machines_MachineExpanderFamilyTapes`, `DirectedFeedback_Machines_MachineExpanderRow`, `DirectedFeedback_Machines_MachineExpanderRowLookup`, `DirectedFeedback_Machines_MachineExpanderTableLoop`, `DirectedFeedback_Machines_MachineLazyTable`, `DirectedFeedback_Machines_MachineLazyTableRuntime`, `DirectedFeedback_Machines_MachineOverlayTable`, `DirectedFeedback_Machines_MachinePaddedExpanderFamily`, `DirectedFeedback_Machines_MachinePaddedOverlay`, `DirectedFeedback_Machines_MachinePortReindex`, `DirectedFeedback_Machines_MachinePreservingLookupClean`, `DirectedFeedback_Machines_MachineRegularExecutionBounds`, `DirectedFeedback_Machines_MachineTableRows`, `DirectedFeedback_Machines_RawInitialMachineFinish`, `DirectedFeedback_Machines_RuntimeFinish`, `DirectedFeedback_Machines_RuntimeSpace`, `DirectedFeedback_Machines_VertexLabel`.
--
--   **Imports.** It imports the bundles `OAIQ085D018`, `OAIQ085D019`, `OAIQ085D020` and `OAIQ085D021` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ085D029`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ085D018
import Definitions.Def_OAIQ085D019
import Definitions.Def_OAIQ085D020
import Definitions.Def_OAIQ085D021

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Target
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem cleanupTrace {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (labels : Label (workTapes enumeration output) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) =
      instruction (workTapes enumeration output) labels none l)
    (base : Tapes K) (ambient : σ) :
    (advance (TM2.step program))^[steps (workTapes enumeration output) base]
      (some ⟨entry (workTapes enumeration output) labels none, (ambient, none), base⟩) =
    some ⟨none, (ambient, none), haltTapes output (base output)⟩ := by
  simpa only [finalRegister_none, finalTapes_workTapes] using
    trace (workTapes enumeration output) labels none program atLabels base ambient none

end DFVSGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeFinish
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineUniformProgram

open Turing DFVSGames.Reduction
open DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad

def program (C : Nat) : Label C → TM2.Stmt (fun _ : Tape => Bool) (Label C) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .scale 0 => MachineUnaryAffineAt.seed .newOccurrences 0 (.scale 1)
  | .scale 1 => MachineUnaryAffineAt.scan .occurrences .affineScratch
      .newOccurrences C (.scale 1) (.scale 2)
  | .scale 2 => MachineTransfer.loopAt .affineScratch .occurrences id false
      (.scale 2) (some (emitEntry C))
  | .emit label => MachineFieldTemplate.instruction (tokens C) emitField
      .copyScratch .accumulator Label.emit (some .finishStart) label
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (C : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label C
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program C

end DFVSGames.Explicit.MachineUniformProgram


namespace DFVSGames.Explicit.MachineUniformHeaders

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineUniformProgram

theorem initList_eq (C : Nat) (bits : List Bool) :
    initList (machine C) bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1

def headersInTime (C q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label C) (.headerRead 0) (some (.headerStart 1))
    (program C) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabet (by decide)
    (.headerStart 1 : Label C) (.headerRead 1) (some (.headerStart 2))
    (program C) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label C) (.headerRead 2) (some (.scale 0))
    (program C) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  change StateTransition.EvalsToInTime (TM2.step (program C))
    ⟨some (.headerStart 0), initialState, inputTapes (encodeWords [n, q, Q] ++ body)⟩
    (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩) (n + q + Q + 6)
  simpa only [encodeWords, List.nil_append, List.append_assoc]
    using ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program C))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

end DFVSGames.Explicit.MachineUniformHeaders


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeSpace
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineUniformRun

open Turing DFVSGames.Reduction
open DFVSGames.Foundations Target
open DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad
open MachineUniformProgram

def scaleInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩
      (some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩)
      (2 * (Q + 1) + 1) where
  steps := 2 * (Q + 1) + 1
  evals_in_steps := by
    change (MachineComposition.advance (machine C).step)^[2 * (Q + 1) + 1]
      (some ⟨some (.scale 0), initialState, MachineUniformHeaders.resultTapes n q Q body⟩) =
      some ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
    have h := MachineUnaryAffineAt.seededAffineTrace Tape.occurrences .affineScratch
      .newOccurrences (by decide) (by decide) (by decide) C 0
      (.scale 0 : Label C) (.scale 1) (.scale 2) (some (emitEntry C))
      (program C) rfl rfl rfl (MachineUniformHeaders.resultTapes n q Q body)
      Q [] (by simp [MachineUniformHeaders.resultTapes])
      (by simp [MachineUniformHeaders.resultTapes]) ((), ()) none
    simp only [
      show MachineUniformHeaders.resultTapes n q Q body .newOccurrences = [] from rfl,
      Nat.add_zero, List.append_nil] at h
    exact h
  steps_le_m := Nat.le_refl _

def emitInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some (emitEntry C), initialState, afterScale C n q Q body⟩
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      (3 * (n + q + C * Q + 3 + C * body.length) + 3 * (C + 3) + 1) := by
  have h := MachineFieldTemplate.phaseInTime (tokens C) emitField
    Tape.copyScratch .accumulator
    (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide) (by decide)
    (Label.emit (C := C)) (some .finishStart) (program C) (fun _ => rfl)
    (afterScale C n q Q body) (by simp [afterScale, MachineUniformHeaders.resultTapes])
    initialState
  simp only [MachineFieldTemplate.reset, initialState,
    template_output, template_copiedLength,
    show (tokens C).length = C + 3 by simp [tokens]] at h
  exact h

def prefixInTime (C n q Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some .finishStart, initialState, afterEmit C n q Q body⟩)
      ((prefixPolynomial C).eval (encodeWords [n, q, Q] ++ body).length) := by
  let first := MachineUniformHeaders.headersInTime C q n Q body
  let second := scaleInTime C n q Q body
  let third := emitInTime C n q Q body
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo third
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, input_length]
  have hcopy : n + q + C * Q + 3 + C * body.length ≤
      (C + 1) * (n + q + Q + 3 + body.length) := by nlinarith
  nlinarith

noncomputable def timePolynomial (C : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine C) clearKeys.length (prefixPolynomial C + 1)

theorem haltList_eq (C : Nat) (bits : List Bool) :
    haltList (machine C) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes, Function.update]
  rfl

def finishStartInTime (C : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (C := C)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program C .finishStart) initialState base) = _
    rfl
  steps_le_m := Nat.le_refl _

end DFVSGames.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_InitialGraph
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.RoundTables

def step (H : BaseTable) (input : Input) : Input :=
  ⟨build H input.val, build_darts_positive H input.val⟩

def size (input : Input) : Nat := input.val.vertices + input.val.darts

theorem step_size (H : BaseTable) (input : Input) :
    size (step H input) ≤ sizeFactor * size input := build_size_le H input.val input.property

end DFVSGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_TableIteration
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def run (H : BaseTable) : Nat → Input → Input := AmplificationIteration.run (step H)

theorem run_val (H : BaseTable) (n : Nat) (input : Input) :
    (run H n input).val = runTables H n input.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change build H (run H n input).val = build H (runTables H n input.val)
      rw [ih]

end DFVSGames.Foundations.PCP.TableIteration

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Lookup
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

section Ambient

variable {q n m : Nat} (counter source destination : K) (labels : Label → Λ)
  (exit : Option Λ)
  (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
  (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)

include atStatement

theorem lookupTailTrace
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List (DartRow q n m)) (row : DartRow q n m)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost prior row]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord prior.length ++ counterSuffix)
          (rowsBits prior ++ (rowBits row ++ suffix)) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
          (encodeWord row.tail.val ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [lookupCost, prefixCost, List.map_nil, List.sum_nil, Nat.zero_add,
      List.length_nil, rowsBits_nil, List.nil_append]
    rw [show row.tail.val + 3 = (row.tail.val + 2) + 1 by omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_zero counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      counterSuffix ambient register
    have hcounter : MachineUnaryCounter.counterTapes counter
        (MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output) 0 counterSuffix =
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output := by
      simp only [MachineUnaryCounter.counterTapes, MachineLookup.update_index _ _ _ hcs hcd]
    rw [hcounter] at hg
    simp only [advance_some]
    rw [hg]
    have hs := selectTrace counter source destination labels exit P atStatement hsd
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      row suffix (by simp [hsd]) ambient none
    simpa only [MachineLookup.tapes_destination,
      MachineLookup.fieldTapes_eq _ _ _ hsd] using hs
  | cons first prior ih =>
    simp only [lookupCost, prefixCost, List.map_cons, List.sum_cons, List.length_cons,
      rowsBits_cons, List.append_assoc]
    rw [show skipCost first + (prior.map skipCost).sum + row.tail.val + 3 =
      ((prior.map skipCost).sum + row.tail.val + 3) +
        (first.tail.val + first.reverseIndex.val + 3) + 1 by simp only [skipCost]; omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_succ counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      prior.length counterSuffix ambient register
    simp only [MachineUnaryCounter.counterTapes,
      MachineLookup.update_index _ _ _ hcs hcd] at hg
    simp only [advance_some]
    rw [hg, Function.iterate_add_apply]
    have hs := skipRowTrace_fromTapes counter source destination labels exit P atStatement
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      first (rowsBits prior ++ (rowBits row ++ suffix)) (by simp [hsd]) ambient none
    rw [hs]
    simp only [MachineLookup.update_source _ _ _ hsd]
    exact ih none

end Ambient

theorem tableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e]]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (rowsBits (rowList table) ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have h := lookupTailTrace counter source destination labels exit P atStatement
    hcs hcd hsd base ((rowList table).take e.val) table.rows[e] counterSuffix
    (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix) output ambient register
  have hlength : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hsplit : rowsBits (rowList table) ++ suffix =
      rowsBits ((rowList table).take e.val) ++
        (rowBits table.rows[e] ++ (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)) := by
    have hrow : table.rows[e.val] = table.rows[e] := rfl
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_append_split (rowList table) e.val (by simp) suffix
  rw [hlength, ← hsplit] at h
  exact h

theorem fullTableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (headerVertices headerDarts : Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (atVertices : P headerVertices = MachineLookup.discard source headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard source headerDarts (labels .guard))
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e] +
        (table.darts + 1) + (table.vertices + 1)]
      (some ⟨some headerVertices, (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have hv := MachineLookup.discardTrace source headerVertices headerDarts P atVertices
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output)
    table.vertices (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix))
    (by simp only [MachineLookup.tapes_source _ _ _ hsd, Input.tableBits_header,
      rowsBits, List.append_assoc]) ambient register
  rw [Function.iterate_add_apply, hv]
  simp only [MachineLookup.update_source _ _ _ hsd]
  have hd := MachineLookup.discardTrace source headerDarts (labels .guard) P atDarts
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix)
      (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix)) output)
    table.darts (rowsBits (rowList table) ++ suffix) (by simp [hsd]) ambient none
  rw [Function.iterate_add_apply, hd]
  simp only [MachineLookup.update_source _ _ _ hsd]
  exact tableTailTrace counter source destination labels exit P atStatement hcs hcd hsd
    base table e counterSuffix suffix output ambient none

theorem tableTailCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    tableTailCost table e ≤ (tableBits table).length + 2 * (encodeWord e.val).length + 1 := by
  have htake : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hrow : table.rows[e.val] = table.rows[e] := rfl
  have hsplit : rowsBits (rowList table) = rowsBits ((rowList table).take e.val) ++
      (rowBits table.rows[e] ++ rowsBits ((rowList table).drop (e.val + 1))) := by
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_split (rowList table) e.val (by simp)
  have hp : (rowsBits ((rowList table).take e.val) ++ rowBits table.rows[e]).length ≤
      (rowsBits (rowList table)).length := by
    rw [hsplit]
    simp only [List.length_append]
    omega
  have hb := lookupCost_le ((rowList table).take e.val) table.rows[e]
  rw [htake] at hb
  have hh := congrArg List.length (Input.tableBits_header table)
  change (tableBits table).length =
    (encodeWord table.vertices ++ (encodeWord table.darts ++ rowsBits (rowList table))).length at hh
  simp only [List.length_append, encodeWord_length] at hh
  unfold tableTailCost
  omega

theorem headLookupCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    headLookupCost table e ≤ 7 * (tableBits table).length + 5 := by
  have hi : (encodeWord (headIndex table e).val).length ≤ (tableBits table).length := by
    rw [encodeWord_length]
    exact (Nat.succ_le_of_lt (headIndex table e).isLt).trans (darts_le_tableBits_length table)
  have hl := tableTailCost_le table (headIndex table e)
  unfold headLookupCost
  omega

def headLookupInTime {q : Nat}
    (tape : HeadTapes K) (hinj : Function.Injective tape)
    (tableFirst tableSecond indexFirst indexSecond headerVertices headerDarts : Λ)
    (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTableFirst : P tableFirst = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 5) id false tableFirst (some tableSecond))
    (atTableSecond : P tableSecond = MachineCopy.forkLoop
      (tape 5) (tape 0) (tape 2) false tableSecond (some indexFirst))
    (atIndexFirst : P indexFirst = Reduction.MachineTransfer.loopAt
      (tape 1) (tape 5) id false indexFirst (some indexSecond))
    (atIndexSecond : P indexSecond = MachineCopy.forkLoop
      (tape 5) (tape 1) (tape 3) false indexSecond (some headerVertices))
    (atVertices : P headerVertices = MachineLookup.discard (tape 2) headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard (tape 2) headerDarts (labels .guard))
    (atStatement : ∀ label,
      P (labels label) = statement q (tape 3) (tape 2) (tape 4) labels exit label)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (hTable : base (tape 0) = tableBits table)
    (hReverse : base (tape 1) = encodeWord (headIndex table e).val)
    (hHead : base (tape 4) = []) (hScratch : base (tape 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (headTimePolynomial.eval (tableBits table).length) := by
  have hne (i j : Fin 6) (h : i ≠ j) : tape i ≠ tape j := fun heq => h (hinj heq)
  let t₁ := Function.update base (tape 2) (tableBits table ++ base (tape 2))
  let t₂ := Function.update t₁ (tape 3) (encodeWord (headIndex table e).val ++ base (tape 3))
  have run₁ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨some indexFirst, (ambient, none), t₁⟩)
      (2 * ((tableBits table).length + 1)) := by
    simpa only [hTable, t₁] using MachineCopy.copyInTime (tape 0) (tape 2) (tape 5)
      (hne 0 2 (by decide)) (hne 0 5 (by decide)) (hne 2 5 (by decide)) false
      tableFirst tableSecond (some indexFirst) P atTableFirst atTableSecond
      base hScratch ambient register
  have hsrc : t₁ (tape 1) = encodeWord (headIndex table e).val := by
    simp only [t₁, Function.update_of_ne (hne 1 2 (by decide)), hReverse]
  have hdst : t₁ (tape 3) = base (tape 3) := by
    simp only [t₁, Function.update_of_ne (hne 3 2 (by decide))]
  have hscratch₁ : t₁ (tape 5) = [] := by
    simp only [t₁, Function.update_of_ne (hne 5 2 (by decide)), hScratch]
  have run₂ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some indexFirst, (ambient, none), t₁⟩
      (some ⟨some headerVertices, (ambient, none), t₂⟩)
      (2 * ((encodeWord (headIndex table e).val).length + 1)) := by
    simpa only [hsrc, hdst, t₂] using MachineCopy.copyInTime (tape 1) (tape 3) (tape 5)
      (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide)) false
      indexFirst indexSecond (some headerVertices) P atIndexFirst atIndexSecond
      t₁ hscratch₁ ambient none
  have ht₂ : t₂ = MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
      (encodeWord (headIndex table e).val ++ base (tape 3))
      (tableBits table ++ base (tape 2)) [] := by
    funext k
    by_cases hi : k = tape 3
    · subst k
      simp [t₂, MachineLookup.tapes, hne 3 2 (by decide), hne 3 4 (by decide)]
    · by_cases hs : k = tape 2
      · subst k
        simp [t₂, t₁, MachineLookup.tapes, hne 2 3 (by decide), hne 2 4 (by decide)]
      · by_cases hh : k = tape 4
        · subst k
          simp [t₂, t₁, MachineLookup.tapes, hne 4 3 (by decide),
            hne 4 2 (by decide), hHead]
        · simp [t₂, t₁, MachineLookup.tapes, hi, hs, hh]
  let run₃ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some headerVertices, (ambient, none), t₂⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (tableTailCost table (headIndex table e)) := {
    steps := tableTailCost table (headIndex table e)
    evals_in_steps := by
      change (advance (TM2.step P))^[tableTailCost table (headIndex table e)]
        (some ⟨some headerVertices, (ambient, none), t₂⟩) =
          some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩
      rw [ht₂]
      simpa only [headLookupTapes, headValue, tableTailCost, List.append_nil] using
        fullTableTailTrace (tape 3) (tape 2) (tape 4) labels exit
          headerVertices headerDarts P atStatement atVertices atDarts
          (hne 3 2 (by decide)) (hne 3 4 (by decide)) (hne 2 4 (by decide))
          base table (headIndex table e) (base (tape 3)) (base (tape 2)) [] ambient none
    steps_le_m := Nat.le_refl _ }
  let run₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁₂ run₃
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have ht := run.steps_le_m
  have hb := headLookupCost_le table e
  simp only [headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold headLookupCost at hb
  omega

end DFVSGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePreservingLookupClean
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem traceAt (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register),
        MachinePreservingLookup.initialTapes tape base index indexSuffix [] output⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ output)⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b :=
    fun h => hne (distinct h)
  have raw := MachinePreservingLookup.preservingLookupTrace tape distinct
    MachinePreservingLookup.Label.copyFirst MachinePreservingLookup.Label.copySecond
    MachinePreservingLookup.Label.lookup none (MachinePreservingLookup.program tape)
    rfl rfl (fun _ => rfl) base values tableWord scratchEmpty index value selected
    indexSuffix [] output ambient register
  have run := MachineSubroutine.trace (fun label => labels (.run label))
    (some (labels .cleanup)) (MachinePreservingLookup.program tape) target
    (fun label => code (.run label))
    (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1)
    _ _ raw
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at run
  have cleanup := MachineDrain.drainTrace (tape 2) (labels .cleanup) exit target
    (code .cleanup)
    (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
    (encodeWords (values.drop (index + 1))) ambient none
  have word : MachinePreservingLookup.finalTapes tape base values index value
      indexSuffix [] output (tape 2) = encodeWords (values.drop (index + 1)) := by
    simp only [MachinePreservingLookup.finalTapes,
      MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide)), List.append_nil]
  have start : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) (encodeWords (values.drop (index + 1))) =
      MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output := by
    rw [← word, Function.update_eq_self]
  have finish : Function.update
      (MachinePreservingLookup.finalTapes tape base values index value indexSuffix [] output)
      (tape 2) [] = MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
        (encodeWord value ++ output) := by
    unfold MachinePreservingLookup.finalTapes MachinePreservingLookup.initialTapes
    rw [MachineLookup.update_source _ _ _ (hd 2 3 (by decide))]
  rw [start, finish] at cleanup
  rw [show steps values index =
      ((encodeWords (values.drop (index + 1))).length + 1) +
        (2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values index + 1) by
        unfold steps
        omega,
    Function.iterate_add_apply, run]
  exact cleanup

theorem traceAt_fromTapes (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (code : ∀ label, target (labels label) = statement tape labels exit label)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = [])
    (index value : Nat) (selected : values[index]? = some value)
    (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps values index]
      (some ⟨some (labels (.run .copyFirst)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        MachinePreservingLookup.initialTapes tape base 0 indexSuffix []
          (encodeWord value ++ base (tape 3))⟩ := by
  have h := traceAt tape distinct labels exit target code base values tableWord scratchEmpty
    index value selected indexSuffix (base (tape 3)) ambient register
  rw [initialTapes_eq tape base index indexSuffix counterWord workEmpty] at h
  exact h

end DFVSGames.Foundations.Complexity.MachinePreservingLookupClean


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTableRows
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

def relationCopyAt {K σ Λ : Type} (src dst : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State σ) :=
  MachineStateEquiv.statement (copyStateEquiv σ)
    (PoweringMachineRow.encodedBlockAt src dst (id : Buffer → Buffer) exit)

theorem relationCopy_step {K Λ σ : Type} [DecidableEq K]
    (src dst : K) (hne : src ≠ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : program label = relationCopyAt src dst exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base src = encodeWords (relationWords relation) ++ suffix)
    (ambient : σ) (buffer : Buffer) (register : Option Bool) :
    TM2.step program ⟨some label, ((ambient, buffer), register), base⟩ =
      some ⟨exit, ((ambient, zeroBuffer), register),
        Function.update (Function.update base src suffix) dst
          (encodeWords (relationWords relation) ++ base dst)⟩ := by
  change some (TM2.stepAux (program label) _ base) = _
  rw [code]
  unfold relationCopyAt
  rw [MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (copyStateEquiv σ)
    (TM2.stepAux (PoweringMachineRow.encodedBlockAt src dst (id : Buffer → Buffer) exit)
      ((ambient, register), buffer) base)) = _
  have hinput : base src = PoweringMachineRow.encodeBits
      (List.ofFn (fun i : Fin 4096 => relation[i])) ++ suffix := by
    rw [relationBits_eq_encodedBlock]
    exact input
  rw [PoweringMachineRow.stepAux_encodedBlockAt src dst (id : Buffer → Buffer)
    exit hne (fun i : Fin 4096 => relation[i]) suffix
    ((ambient, register), buffer) base hinput]
  simp only [id_eq, relationBits_eq_encodedBlock, MachineStateEquiv.configuration,
    copyStateEquiv, zeroBuffer]
  rfl

end DFVSGames.Foundations.Complexity.MachineRegularOriginalRow
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderFamilyTapes
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

variable {ρ : Type} [Fintype ρ] {d : Nat}

section Embedded

variable {K Λ : Type} [DecidableEq K]

theorem firstEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .inputVertex) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .firstReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (firstAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.firstEmit l)) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
        (some (labels .firstReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (firstPlan ρ d) (fun _ : Fin 1 => ports .inputVertex)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.firstEmit k)) (some (labels .firstReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [firstPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, firstAddress] using run

theorem secondEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientFirst) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels .secondReverse), ((ambient, ()), none),
        emittedWord (ports .queryReverse) base (secondAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.secondEmit l)) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
        (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
        (some (labels .secondReverse)) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (secondPlan ρ d) (fun _ : Fin 1 => ports .quotientFirst)
    (ports .emitScratch) (ports .queryReverse)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.secondEmit k)) (some (labels .secondReverse)) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [secondPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, secondAddress] using run

theorem outputEmitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atLabels : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (n : Nat) (base : K → List Bool)
    (source : base (ports .quotientSecond) = encodeWord n)
    (scratch : base (ports .emitScratch) = [])
    (ambient : Ambient ρ d × Fin (degree d)) :
    (MachineComposition.advance (TM2.step target))^[emitSteps n]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        ((ambient, ()), none), base⟩) =
      some ⟨some (labels (.cleanup 0)), ((ambient, ()), none),
        emittedWord (ports .output) base (outputAddress n ambient.1.2)⟩ := by
  have code : ∀ l, target (labels (.outputEmit l)) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
        (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
        (some (labels (.cleanup 0))) l := by
    intro l
    rw [atLabels]
    rfl
  have run := Emitter.planTrace (outputPlan ρ d) (fun _ : Fin 1 => ports .quotientSecond)
    (ports .emitScratch) (ports .output)
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro i h; have h' := portsInjective h; cases h')
    (by intro h; have h' := portsInjective h; cases h')
    (fun k => labels (.outputEmit k)) (some (labels (.cleanup 0))) target code
    (fun _ : Fin 1 => n) base (fun _ => source) scratch ambient
  simpa only [outputPlan, affinePlan_steps, affinePlan_bits, Emitter.resultTapes,
    emittedWord, outputAddress] using run

end Embedded

end DFVSGames.Foundations.Complexity.MachineExpanderRow

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRowLookup
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

section Lookup

variable {v d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool) (G : Table v (degree d))
    (tableWord : base (ports .table) = encodeWords (rotationWords G))
    (scratchEmpty : base (ports .lookupRestore) = [])
    (x : Fin v × Fin (degree d)) (indexSuffix : List Bool)
    (counterWord : base (ports .queryIndex) =
      encodeWord (rowIndex v (degree d) x).val ++ indexSuffix)
    (workEmpty : base (ports .lookupWork) = [])
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code tableWord scratchEmpty counterWord workEmpty

theorem lookupPhaseTrace :
    (advance (TM2.step target))^[MachinePreservingLookupClean.steps
        (rotationWords G) (rowIndex v (degree d) x).val]
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩) =
      some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩ := by
  apply MachinePreservingLookupClean.traceAt_fromTapes (ports ∘ lookupTape)
    (distinct.comp lookupTape_injective)
    (fun l => labels (lookupPhaseLabel second l)) (some (labels (scanPhaseLabel second)))
    target
  · intro l
    cases second
    · exact code (.firstLookup l)
    · exact code (.secondLookup l)
  · exact tableWord
  · exact scratchEmpty
  · exact rotationWords_getElem? G (rowIndex v (degree d) x)
  · exact counterWord
  · exact workEmpty

end Lookup

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRow
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

section Execution

variable {v d : Nat} {ρ Λ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive r.smallTable id labels exit l)

include code

theorem rowTraceAt :
    (advance (TM2.step target))^[rowSteps r output]
      (some ⟨some (labels .initialize_), divisionState positive ambient r.control0 none,
        frame0 r output⟩) =
      some ⟨exit, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩ := by
  let zero := MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive) 0
  have h0 : (advance (TM2.step target))^[1]
      (some ⟨some (labels .initialize_), divisionState positive ambient r.control0 none,
        frame0 r output⟩) =
      some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control0 none, frame1 r output⟩ := by
    simpa only [Function.iterate_one, advance_some, divisionState, frame1] using
      initializeStepAt positive r.smallTable id Function.injective_id labels exit target code
        (frame0 r output) (divisionState positive ambient r.control0 none)
  have h1 := firstEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.inputVertex.val (frame1 r output)
    (by simp) (by simp) ((ambient,r.control0),zero)
  change (advance (TM2.step target))^[emitSteps r.inputVertex.val]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control0 none, frame1 r output⟩) =
      some ⟨some (labels .firstReverse), divisionState positive ambient r.control0 none,
        frame2 r output⟩ at h1
  have h2 := reversePhaseTrace_unary false positive r.smallTable id Function.injective_id
    labels exit target code (frame2 r output) (((ambient,r.control0),zero),()) none
    r.query1 [] (by simp) (by simp)
  simp only [List.append_nil] at h2
  change (advance (TM2.step target))^[r.query1 + 2]
      (some ⟨some (labels .firstReverse), divisionState positive ambient r.control0 none,
        frame2 r output⟩) =
      some ⟨some (labels (.firstLookup (.run .copyFirst))),
        divisionState positive ambient r.control0 none, frame3 r output⟩ at h2
  have h3 := lookupPhaseTrace false positive r.smallTable id Function.injective_id
    labels exit target code (frame3 r output) r.oldTable
    (by simp) (by simp)
    (r.inputVertex, firstOffset r.control0) []
    (by simpa [frameContents, RowData.firstRow] using
      congrArg encodeWord r.query1_eq_firstRow)
    (by simp) (((ambient,r.control0),zero),()) none
  change (advance (TM2.step target))^[MachinePreservingLookupClean.steps
      (rotationWords r.oldTable) r.firstRow.val]
      (some ⟨some (labels (.firstLookup (.run .copyFirst))),
        divisionState positive ambient r.control0 none, frame3 r output⟩) =
      some ⟨some (labels .firstScan), divisionState positive ambient r.control0 none,
        frame4 r output⟩ at h3
  have h4 := firstDivisionTrace positive r.smallTable id Function.injective_id labels exit
    target code (frame4 r output) r.firstValue [] [] []
    (by simp) (by simp) (by simp)
    ambient r.control0 none
  rw [← r.firstReturn_eq_residue positive] at h4
  change (advance (TM2.step target))^[r.firstValue + 2]
      (some ⟨some (labels .firstScan), divisionState positive ambient r.control0 none,
        frame4 r output⟩) =
      some ⟨some (labels .clearQuery), divisionState positive ambient r.control1 none,
        frame5 r output⟩ at h4
  have h5 : (advance (TM2.step target))^[1]
      (some ⟨some (labels .clearQuery), divisionState positive ambient r.control1 none,
        frame5 r output⟩) =
      some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control1 none, frame6 r output⟩ := by
    simpa only [Function.iterate_one, advance_some, frame6] using
      clearQueryStepAt positive r.smallTable id Function.injective_id labels exit target code
        (frame5 r output) (divisionState positive ambient r.control1 none)
  have h6 := secondEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.firstVertex.val (frame6 r output)
    (by simp) (by simp) ((ambient,r.control1),zero)
  change (advance (TM2.step target))^[emitSteps r.firstVertex.val]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control1 none, frame6 r output⟩) =
      some ⟨some (labels .secondReverse), divisionState positive ambient r.control1 none,
        frame7 r output⟩ at h6
  have h7 := reversePhaseTrace_unary true positive r.smallTable id Function.injective_id
    labels exit target code (frame7 r output) (((ambient,r.control1),zero),()) none
    r.query2 [] (by simp) (by simp)
  simp only [List.append_nil] at h7
  change (advance (TM2.step target))^[r.query2 + 2]
      (some ⟨some (labels .secondReverse), divisionState positive ambient r.control1 none,
        frame7 r output⟩) =
      some ⟨some (labels (.secondLookup (.run .copyFirst))),
        divisionState positive ambient r.control1 none, frame8 r output⟩ at h7
  have h8 := lookupPhaseTrace true positive r.smallTable id Function.injective_id
    labels exit target code (frame8 r output) r.oldTable
    (by simp) (by simp)
    (r.firstVertex, secondOffset r.control1) []
    (by simpa [frameContents, RowData.secondRow] using
      congrArg encodeWord r.query2_eq_secondRow)
    (by simp) (((ambient,r.control1),zero),()) none
  change (advance (TM2.step target))^[MachinePreservingLookupClean.steps
      (rotationWords r.oldTable) r.secondRow.val]
      (some ⟨some (labels (.secondLookup (.run .copyFirst))),
        divisionState positive ambient r.control1 none, frame8 r output⟩) =
      some ⟨some (labels .secondScan), divisionState positive ambient r.control1 none,
        frame9 r output⟩ at h8
  have h9 := secondDivisionTrace positive r.smallTable id Function.injective_id labels exit
    target code (frame9 r output) r.secondValue [] [] []
    (by simp) (by simp) (by simp)
    ambient r.control1 none
  rw [← r.secondReturn_eq_residue positive] at h9
  change (advance (TM2.step target))^[r.secondValue + 2]
      (some ⟨some (labels .secondScan), divisionState positive ambient r.control1 none,
        frame9 r output⟩) =
      some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control2 none, frame10 r output⟩ at h9
  have h10 := outputEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.secondVertex.val (frame10 r output)
    (by simp) (by simp) ((ambient,r.control2),zero)
  change (advance (TM2.step target))^[emitSteps r.secondVertex.val]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control2 none, frame10 r output⟩) =
      some ⟨some (labels (.cleanup 0)), divisionState positive ambient r.control2 none,
        frame11 r output⟩ at h10
  have h11 := cleanupExitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code (frame11 r output) (divisionState positive ambient r.control2 none)
  change (advance (TM2.step target))^[cleanupSteps id (frame11 r output) + 1]
      (some ⟨some (labels (.cleanup 0)), divisionState positive ambient r.control2 none,
        frame11 r output⟩) =
      some ⟨exit, divisionState positive ambient r.control2 none, frame12 r output⟩ at h11
  rw [final_frame_eq] at h11
  exact concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow
    (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow
      (concatenate_inline_MachineExpanderRow h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11

end Execution

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

def rowInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ) :
    StateTransition.EvalsToInTime (TM2.step (program positive r.smallTable))
      ⟨some .initialize_, divisionState positive ambient r.control0 none, frame0 r output⟩
      (some ⟨none, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩)
      (80 * (r.tableLength + 1)) :=
  rowInTimeAt positive r output ambient id none (program positive r.smallTable) (fun _ => rfl)

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

variable {ρ : Type} [Fintype ρ] {v d : Nat}

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

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderTableLoop
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

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

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

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

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

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

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderFamilyLoop
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

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

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

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

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open MachineCloudPadding
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem ceiling_initial_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => [])
      (MachineStateEquiv.configuration (ceilingStates ρ)
        ⟨some .init, ((state, false), register), ceilingInput requested⟩) =
      ⟨some main, initialState state register, initialTapes requested⟩ := by
  simp only [Placement.configuration, Placement.label, MachineStateEquiv.configuration,
    ceilingStates_apply, ceiling_initial_tapes, ceilingLabel, main, initialState]

theorem family_initial_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (metadata : Bool × Option Bool) :
    Placement.configuration familyView familyLabel none (retainedFrame requested)
      (MachineStateFrame.frameConfiguration metadata
        (MachineAlphabetTransport.configuration MachineExpanderFamily.alphabet_eq
          ⟨some (.inr .initialize_), state,
            MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []⟩)) =
      ⟨some familyEntry, (state, metadata), handoffTapes requested⟩ := by
  rw [MachineExpanderFamily.configuration_toBool]
  simp only [MachineStateFrame.frameConfiguration, Placement.configuration, Placement.label,
    family_initial_tapes, familyEntry, familyLabel]

theorem family_final_configuration {ρ : Type} (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) :
    Placement.configuration familyView familyLabel none (retainedFrame requested)
      (MachineStateFrame.frameConfiguration (false, none)
        (MachineAlphabetTransport.configuration MachineExpanderFamily.alphabet_eq
          ⟨none,
            MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
              (MachineExpanderFamily.caller state),
            MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []⟩)) =
      ⟨none, finalState H state, finalTapes H requested⟩ := by
  rw [MachineExpanderFamily.configuration_toBool]
  simp only [MachineStateFrame.frameConfiguration, Placement.configuration, Placement.label,
    family_final_tapes, finalState]

theorem finalTapes_currentSize (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape (.inr .currentSize)) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := by
  change encodeWord (vertexCount (degree fixedDegree)
    (PCP.PreprocessingLevels.boundedLevel requested)) = _
  exact congrArg encodeWord (PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize requested)

end DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def timeCoefficient : Nat :=
  MachineExpanderFamilyBounds.inputCoefficient + PCP.ExpanderFamily.growth + 29

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C timeCoefficient * Polynomial.X^5

theorem timePolynomial_encoding (k : Nat) :
    timePolynomial.eval (encodeWord k).length = timeCoefficient * (k + 1)^5 := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, encodeWord_length]

theorem combinedCost_le (k : Nat) :
    (MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord k).length +
      MachineExpanderFamilyBounds.inputCoefficient * (k + 1)^5 ≤
        timePolynomial.eval (encodeWord k).length := by
  rw [timePolynomial_encoding]
  have h := ceilingCost_le PCP.ExpanderFamily.growth k
  unfold timeCoefficient
  nlinarith only [h]

end DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePaddedExpanderFamily
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open MachineCloudPadding
open MachineComposition

variable {ρ : Type} [Fintype ρ]

noncomputable def ceilingInTime (H : SmallTable) (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program H))
      ⟨some main, initialState state register, initialTapes requested⟩
      (some ⟨some familyEntry, (state, (false, none)), handoffTapes requested⟩)
      ((MachineCeilingPower.timePolynomial PCP.ExpanderFamily.growth).eval
        (encodeWord requested).length) := by
  let original := MachineCeilingPower.paddingInTime requested state register
  let renamed := MachineStateEquiv.execution (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth) original
  let placed := liftExecutionInTime (TM2.step (ceilingSource (ρ := ρ)))
    (TM2.step (program H))
    (Placement.configuration ceilingView ceilingLabel (some familyEntry) (fun _ => []))
    (Placement.step_simulation ceilingTape ceilingView ceilingView_left ceilingView_right
      ceilingLabel (some familyEntry) (fun _ => []) (ceilingSource (ρ := ρ))
      (program H) (program_ceiling H)) renamed
  have initialEq := ceiling_initial_configuration requested state register
  have finalEq := ceiling_handoff_configuration requested state
  unfold ceilingInput at initialEq
  unfold ceilingOutput at finalEq
  simpa only [initialEq, finalEq] using placed

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

end DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

abbrev Alphabet (_ : Tape) := Bool

end DFVSGames.Foundations.Complexity.MachineRegularFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineDummyRows
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachinePaddingRows

open Turing MachineComposition

def extra (d : Nat) (hd : 0 < d) : Control → TM2.Stmt Alphabet (Label d) State
  | .initialize_ => Reduction.MachineSubstitution.pushWord (.inl 2)
      MachineDummyRows.trueBits.reverse
      (.load (fun _ => (((), none), ())) (.goto (fun _ => .inr .guard)))
  | .guard => .pop (.inr ()) (fun _ bit => (((), bit), ()))
      (.branch (fun s => s.1.2.getD false)
        (.load (fun _ => (((), none), ())) (.goto (fun _ => bodyEntry d hd)))
        (.push (.inr ()) (fun _ => false)
          (.load (fun _ => (((), none), ())) .halt)))
  | .bump => .push (.inl 0) (fun _ => true) (.goto (fun _ => .inr .guard))

def program (d : Nat) (hd : 0 < d) : Label d → TM2.Stmt Alphabet (Label d) State :=
  MachineEmbedding.program (some (.inr .bump)) (MachineDummyRows.program d) (extra d hd)

def tapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  MachineEmbedding.tapes (MachineDummyRows.fieldTapes v e output)
    (fun _ : Unit => encodeWord fuel)

def cfg (d : Nat) (label : Option (Label d)) (v e fuel : Nat)
    (output : List Bool) : TM2.Cfg Alphabet (Label d) State :=
  ⟨label, (((), none), ()), tapes v e fuel output⟩

theorem bodyTrace (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d]
      (some (cfg d (some (bodyEntry d hd)) v e fuel output)) =
      some (cfg d (some (.inr .bump)) v (e + d) fuel
        (output ++ MachineDummyRows.rowsBits v e d)) := by
  have run := MachineDummyRows.suffixTrace d ⟨0, hd⟩ (by simp)
    v e output () none
  have lifted := liftSuccessfulTrace
    (TM2.step (MachineDummyRows.program d)) (TM2.step (program d hd))
    (MachineEmbedding.configuration (some (.inr .bump)) ()
      (fun _ : Unit => encodeWord fuel))
    (by
      intro a b h
      exact MachineEmbedding.step_simulation (some (.inr Control.bump)) ()
        (fun _ : Unit => encodeWord fuel) (MachineDummyRows.program d) (extra d hd) a b h)
    (MachineDummyRows.steps v e output d) _ _ run
  exact lifted

theorem guard_succ (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .guard)) v e (fuel + 1) output) =
      some (cfg d (some (bodyEntry d hd)) v e fuel output) := by
  change some (TM2.stepAux (extra d hd .guard) _ _) = _
  simp only [extra, TM2.stepAux, tapes, MachineEmbedding.tapes_inr,
    encodeWord, List.replicate_succ, List.cons_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_true]
  congr 2
  funext k
  cases k <;> simp [tapes, MachineEmbedding.tapes, Function.update, encodeWord]

theorem guard_zero (d : Nat) (hd : 0 < d) (v e : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .guard)) v e 0 output) =
      some (cfg d none v e 0 output) := by
  change some (TM2.stepAux (extra d hd .guard) _ _) = _
  simp only [extra, TM2.stepAux, tapes, MachineEmbedding.tapes_inr,
    encodeWord, List.replicate_zero, List.nil_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext k
  cases k <;> simp [tapes, MachineEmbedding.tapes, Function.update, encodeWord]

theorem bump_step (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .bump)) v e fuel output) =
      some (cfg d (some (.inr .guard)) (v + 1) e fuel output) := by
  change some (TM2.stepAux (extra d hd .bump) _ _) = _
  simp only [extra, TM2.stepAux]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [tapes, MachineEmbedding.tapes,
      MachineDummyRows.fieldTapes, encodeWord, List.replicate_succ]
  | inr k => simp [tapes, MachineEmbedding.tapes]

def paddingBits (d v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => MachineDummyRows.rowsBits v e d ++ paddingBits d (v + 1) (e + d) count

def steps (d v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 1
  | count + 1 => (MachineDummyRows.steps v e output d + 2) +
      steps d (v + 1) (e + d) (output ++ MachineDummyRows.rowsBits v e d) count

theorem loopTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count]
      (some (cfg d (some (.inr .guard)) v e count output)) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  induction count generalizing v e output with
  | zero => simpa [steps, paddingBits] using guard_zero d hd v e output
  | succ count ih =>
      rw [steps, Nat.add_comm (MachineDummyRows.steps v e output d + 2),
        Function.iterate_add_apply]
      have hb : (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d + 2]
          (some (cfg d (some (.inr .guard)) v e (count + 1) output)) =
          some (cfg d (some (.inr .guard)) (v + 1) (e + d) count
            (output ++ MachineDummyRows.rowsBits v e d)) := by
        rw [show MachineDummyRows.steps v e output d + 2 =
          (MachineDummyRows.steps v e output d + 1) + 1 by omega,
          Function.iterate_succ_apply, advance_some, guard_succ,
          Function.iterate_succ_apply', bodyTrace, advance_some, bump_step]
      rw [hb, ih]
      simp only [paddingBits, List.append_assoc, Nat.succ_mul]
      congr 2 <;> omega

def initialTapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  Function.update (tapes v e fuel output) (.inl 2) []

theorem initialize_step (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd)
      ⟨some (.inr .initialize_), (((), none), ()), initialTapes v e fuel output⟩ =
      some (cfg d (some (.inr .guard)) v e fuel output) := by
  change some (TM2.stepAux (extra d hd .initialize_) _ _) = _
  simp only [extra, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, initialTapes, Function.update_self, List.append_nil,
    Function.update_idem, TM2.stepAux]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [tapes, MachineEmbedding.tapes,
      MachineDummyRows.fieldTapes]
  | inr k => simp [tapes, MachineEmbedding.tapes]

theorem paddingTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count + 1]
      (some ⟨some (.inr .initialize_), (((), none), ()), initialTapes v e count output⟩) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  rw [Function.iterate_succ_apply, advance_some, initialize_step, loopTrace]

def machine (d : Nat) (hd : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .inl 0
  k₁ := .inl 4
  Γ := Alphabet
  Λ := Label d
  main := .inr .initialize_
  σ := State
  initialState := (((), none), ())
  m := program d hd

end DFVSGames.Foundations.Complexity.MachinePaddingRows
end

section

namespace DFVSGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

theorem rowBits_flat (table : Table n d) (i : Fin (n * d)) :
    encodeWords (GraphTables.rowWords ((flatRows table)[i])) =
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2 := by
  simp only [flatRows, Vector.getElem_ofFn, Fin.getElem_fin,
    MachineTableRows.rowBits_eq, rowBits, Prod.eta, Equiv.apply_symm_apply]

theorem rowsBits_eq_vertices (table : Table n d) :
    rowsBits table = (List.ofFn (fun v : Fin n => vertexBits table v)).flatten := by
  have hflat : (flatRows table).toList =
      List.ofFn (fun i : Fin (n * d) => (flatRows table)[i]) := by
    simp only [flatRows, Vector.toList_ofFn, Vector.getElem_ofFn, Fin.getElem_fin]
  unfold rowsBits
  rw [hflat, encodeWords_flatMap_inline_PreprocessingPaddingWords, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun i : Fin (n * d) =>
    encodeWords (GraphTables.rowWords ((flatRows table)[i])))).flatten = _
  simp_rw [rowBits_flat]
  simpa only [Equiv.symm_apply_apply, vertexBits] using
    flatten_ofFn_rowIndex (fun i : Fin (n * d) =>
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2)

theorem rowBits_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) p =
      MachineDummyRows.rowBits (n + v.val) (p.val + d * (n + v.val)) := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_new,
    PreprocessingPaddingTables.relations_pad_new]
  rfl

theorem dummy_rowsBits_eq_ofFn (v e count : Nat) :
    MachineDummyRows.rowsBits v e count =
      (List.ofFn (fun p : Fin count => MachineDummyRows.rowBits v (e + p.val))).flatten := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    rw [MachineDummyRows.rowsBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext p
    congr 1
    omega

theorem paddingBits_eq_ofFn (d v e count : Nat) :
    MachinePaddingRows.paddingBits d v e count =
      (List.ofFn (fun k : Fin count =>
        MachineDummyRows.rowsBits (v + k.val) (e + k.val * d) d)).flatten := by
  induction count generalizing v e with
  | zero => rfl
  | succ count ih =>
    rw [MachinePaddingRows.paddingBits, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Fin.val_succ, Nat.add_mul, Nat.one_mul]
    congr 1
    apply congrArg (fun f : Fin count → List Bool => (List.ofFn f).flatten)
    funext k
    congr 1 <;> omega

theorem vertexBits_pad_new (table : Table n d) (h : n ≤ m) (v : Fin (m - n)) :
    vertexBits (PreprocessingPaddingTables.pad table h)
        (PreprocessingPaddingTables.vertexEquiv h (.inr v)) =
      MachineDummyRows.rowsBits (n + v.val) (n * d + v.val * d) d := by
  unfold vertexBits
  simp_rw [rowBits_pad_new]
  rw [dummy_rowsBits_eq_ofFn]
  apply congrArg (fun f : Fin d → List Bool => (List.ofFn f).flatten)
  funext p
  congr 1
  ring

theorem rowsBits_pad (table : Table n d) (h : n ≤ m) :
    rowsBits (PreprocessingPaddingTables.pad table h) =
      rowsBits table ++ MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  rw [rowsBits_eq_vertices, ofFn_split h, List.flatten_append]
  simp_rw [vertexBits_pad_old, vertexBits_pad_new]
  rw [← rowsBits_eq_vertices, ← paddingBits_eq_ofFn]

theorem tableBits_pad (table : Table n d) (h : n ≤ m) :
    tableBits (PreprocessingPaddingTables.pad table h) =
      encodeWords [m, m * d] ++ rowsBits table ++
        MachinePaddingRows.paddingBits d n (n * d) (m - n) := by
  change encodeWords (PortTables.tableWords (PreprocessingPaddingTables.pad table h)) = _
  rw [tableWords_eq, encodeWords_append]
  change encodeWords [m, m * d] ++ rowsBits (PreprocessingPaddingTables.pad table h) = _
  rw [rowsBits_pad, List.append_assoc]

end DFVSGames.Foundations.PCP.PreprocessingPaddingWords

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineRegularExecutionBounds
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

section Machine

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

def cleanupExecution (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output) (state : σ)
    (register : Option Bool) (base : K → List Bool) :
    StateTransition.EvalsToInTime (completedMachine P chosen).step
      ⟨cleanupEntry chosen, (state, register), base⟩
      (some (haltList (completedMachine P chosen) (base P.output)))
      (MachineDrainMany.steps chosen base + 1) := by
  let after : (completedMachine P chosen).Cfg :=
    ⟨some (resetLabel chosen), (state, MachineDrainMany.finalRegister chosen register),
      MachineDrainMany.finalTapes chosen base⟩
  have drains : StateTransition.EvalsToInTime (completedMachine P chosen).step
      ⟨cleanupEntry chosen, (state, register), base⟩ (some after)
      (MachineDrainMany.steps chosen base) := {
    steps := MachineDrainMany.steps chosen base
    evals_in_steps := MachineDrainMany.trace chosen (cleanupLabel chosen)
      (some (resetLabel chosen)) (completedProgram P chosen) (fun _ => rfl) base state register
    steps_le_m := le_rfl }
  have reset : StateTransition.EvalsToInTime (completedMachine P chosen).step
      after (some (haltList (completedMachine P chosen) (base P.output))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (⟨none, (P.initial, none), MachineDrainMany.finalTapes chosen base⟩ :
          TM2.Cfg (fun _ : K => Bool) (Label Λ chosen) (σ × Option Bool)) =
        some (haltList (completedMachine P chosen) (base P.output))
      rw [finalTapes_eq P chosen complete, haltList_eq]
      rfl
    steps_le_m := le_rfl }
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans _ (MachineDrainMany.steps chosen base) 1
      _ after _ drains reset

def outputsInTime (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (input output : List Bool) (state : σ) (base : K → List Bool) (budget : Nat)
    (raw : StateTransition.EvalsToInTime (sourceMachine P).step
      (initList (sourceMachine P) input) (some ⟨none, state, base⟩) budget)
    (correctOutput : base P.output = output) :
    TM2OutputsInTime (completedMachine P chosen) input (some output)
      (budget + chosen.length *
        (input.length + budget * Runtime.programPushBound (sourceMachine P) + 1) + 1) := by
  let lifted := liftExecutionInTime (sourceMachine P).step
    (completedMachine P chosen).step (embeddedCfg P chosen) (step_simulation P chosen) raw
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ lifted
    (cleanupExecution P chosen complete state none base)
  have stackBound : ∀ k, (base k).length ≤
      input.length + budget * Runtime.programPushBound (sourceMachine P) := by
    intro k
    have h := Runtime.executionSizeBound (sourceMachine P).step
      (fun cfg => (cfg.stk k).length) (Runtime.programPushBound (sourceMachine P))
      (Runtime.stepStackLength (sourceMachine P) k) raw
    exact h.trans (Nat.add_le_add_right (Runtime.initialStackLength (sourceMachine P) input k) _)
  have cleanupBound := MachineDrainMany.steps_le_uniform chosen base _ stackBound
  rw [embedded_init, correctOutput] at joined
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := joined.steps_le_m.trans (by omega) }

noncomputable def computableInPolyTime {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    TM2ComputableInPolyTime encodeIn encodeOut f where
  tm := completedMachine P chosen
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := completedTime P chosen rawTime
  outputsFun a := by
    have execution : TM2OutputsInTime (completedMachine P chosen) (encodeIn a)
        (some (encodeOut (f a))) ((completedTime P chosen rawTime).eval (encodeIn a).length) := by
      simpa only [completedTime_eval] using
        outputsInTime P chosen complete _ _ (run a).state (run a).tapes _
          (run a).execution (run a).output_eq
    exact (congrArg₂ (fun input output : List Bool =>
      TM2OutputsInTime (completedMachine P chosen) input (some output)
        ((completedTime P chosen rawTime).eval (encodeIn a).length))
      (List.map_id (encodeIn a)) (List.map_id (encodeOut (f a)))).mpr execution

theorem computableInPolyTime_finite_alphabet {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computableInPolyTime P chosen complete encodeIn encodeOut f rawTime run).tm :=
  finiteAlphabet P chosen

end Machine

end DFVSGames.Foundations.Complexity.MachineCanonicalOutput
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PreprocessingStageMaps
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.PreprocessingStageMaps
open PreprocessingRegularTables

def padding (d : Nat) (input : PortTables.Input d) : PortTables.Input d :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingPaddingTables.pad input.2 (PreprocessingLevels.le_paddedSize input.1)⟩

def familyAt (H : BaseTable) (n : Nat) :
    ExpanderTables.Table (PreprocessingLevels.paddedSize n) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize n)
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n))

def paddedOverlay (H : BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (d + internalDegree) :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingOverlayTables.overlay (padding d input).2 (familyAt H input.1)⟩

end DFVSGames.Foundations.PCP.PreprocessingStageMaps

namespace DFVSGames.Foundations.Complexity.MachinePaddingBounds

theorem rowsBits_length_le (v e count : Nat) :
    (MachineDummyRows.rowsBits v e count).length ≤ count * (v + e + count + 8194) := by
  induction count generalizing e with
  | zero => simp [MachineDummyRows.rowsBits]
  | succ count ih =>
    have hi := ih (e + 1)
    have hb : v + (e + 1) + count + 8194 = v + e + (count + 1) + 8194 := by omega
    rw [hb] at hi
    have hr : v + e + 8194 ≤ v + e + (count + 1) + 8194 := by omega
    simp only [MachineDummyRows.rowsBits, List.length_append, MachineDummyRows.rowBits_length]
    calc
      _ ≤ (v + e + (count + 1) + 8194) +
          count * (v + e + (count + 1) + 8194) := Nat.add_le_add hr hi
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

theorem steps_le_bound (d v e : Nat) (output : List Bool) (count : Nat) :
    MachinePaddingRows.steps d v e output count ≤
      count * (d * (4 * rowBound d v e count +
        2 * (output.length + count * d * rowBound d v e count) + 10) + 2) + 1 := by
  induction count generalizing v e output with
  | zero => simp [MachinePaddingRows.steps]
  | succ count ih =>
    let B := rowBound d v e (count + 1)
    let C := d * (4 * B + 2 * (output.length + (count + 1) * d * B) + 10) + 2
    have hb : rowBound d (v + 1) (e + d) count = B := rowBound_next d v e count
    have hr : v + e + d + 8194 ≤ B := blockRow_le_rowBound d v e count
    have hlen : (MachineDummyRows.rowsBits v e d).length ≤ d * B :=
      (rowsBits_length_le v e d).trans (Nat.mul_le_mul_left d hr)
    have hout : (output ++ MachineDummyRows.rowsBits v e d).length + count * d * B ≤
        output.length + (count + 1) * d * B := by
      rw [List.length_append]
      calc
        _ ≤ output.length + d * B + count * d * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hlen output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hi := ih (v + 1) (e + d) (output ++ MachineDummyRows.rowsBits v e d)
    rw [hb] at hi
    have hconstant :
        d * (4 * B + 2 * ((output ++ MachineDummyRows.rowsBits v e d).length +
          count * d * B) + 10) + 2 ≤ C := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left d
        (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10)) 2
    have hremaining := hi.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left count hconstant) 1)
    have hcount : d * B ≤ (count + 1) * d * B := by
      simpa only [Nat.one_mul, Nat.mul_assoc] using
        Nat.mul_le_mul_right (d * B) (Nat.succ_le_succ (Nat.zero_le count))
    have hbodyOutput : output.length + d * (v + e + d + 8194) ≤
        output.length + (count + 1) * d * B :=
      Nat.add_le_add_left ((Nat.mul_le_mul_left d hr).trans hcount) output.length
    have hbodyInner : 4 * (v + e + d + 8194) +
        2 * (output.length + d * (v + e + d + 8194)) + 10 ≤
          4 * B + 2 * (output.length + (count + 1) * d * B) + 10 := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hr)
        (Nat.mul_le_mul_left 2 hbodyOutput)) 10
    have hbody : MachineDummyRows.steps v e output d + 2 ≤ C :=
      Nat.add_le_add_right ((MachineDummyRows.steps_le_bound v e output d).trans
        (Nat.mul_le_mul_left d hbodyInner)) 2
    change (MachineDummyRows.steps v e output d + 2) +
      MachinePaddingRows.steps d (v + 1) (e + d)
        (output ++ MachineDummyRows.rowsBits v e d) count ≤ (count + 1) * C + 1
    calc
      _ ≤ C + (count * C + 1) := Nat.add_le_add hbody hremaining
      _ = _ := by rw [Nat.add_mul, Nat.one_mul]; omega

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

end DFVSGames.Foundations.Complexity.MachinePaddingBounds

namespace DFVSGames.Foundations.Complexity.MachinePaddingTable

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

end DFVSGames.Foundations.Complexity.MachinePaddingTable

namespace DFVSGames.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open DFVSGames.Foundations.PCP
open MachineCloudPadding

def rowProgram {σ : Type} (d : Nat) (hd : 0 < d) :
    MachinePaddingRows.Label d →
      TM2.Stmt (fun _ : MachinePaddingRows.Tape => Bool) (MachinePaddingRows.Label d) (State σ) :=
  MachineStateEquiv.program (rowStateEquiv σ)
    (MachineStateFrame.frameProgram
      (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd)))

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

def rowTime {n d m : Nat} (t : PortTables.Table n d) : Nat :=
  MachinePaddingRows.steps d n (n * d) (MachinePaddingTable.initialOutput (m := m) t) (m - n) + 1

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

def totalTime {n d : Nat} (t : PortTables.Table n d) : Nat :=
  otherTime t + rowTime (m := PreprocessingLevels.paddedSize n) t

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

theorem power_length_bound {n d : Nat} (t : PortTables.Table n d) :
    PreprocessingLevels.paddedSize n ≤ ExpanderFamily.growth * ((PortTables.tableBits t).length + 1) :=
  (MachineCeilingPower.paddingOutput_bounds n).2.2.trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (PortTables.vertices_le_tableBits_length t) 1))

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

theorem otherTime_le {n d : Nat} (t : PortTables.Table n d) :
    otherTime t ≤ (otherPolynomial d).eval (PortTables.tableBits t).length := by
  have hs := MachineTableSplit.exactSteps_le n (n * d) (PreprocessingPaddingWords.rowsBits t)
  rw [← tableBits_split, MachineTableSplit.timePolynomial_eval] at hs
  have hc := MachineCeilingPower.totalTime_le ExpanderFamily.growth n
  have hn := PortTables.vertices_le_tableBits_length t
  have hm := power_length_bound t
  have hsq := Nat.mul_le_mul_left (ExpanderFamily.growth + 8)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2)
  have hmul := Nat.mul_le_mul_left (d + 8) hm
  simp only [otherPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold otherTime cleanupTime
  unfold MachineCeilingPower.timeBound at hc
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

end DFVSGames.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePortReindex
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open DFVSGames.Foundations.Complexity

variable {n d : Nat}

theorem row_lazy_stay (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (false, p)) = stayRow d v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      rowIndex n (2 * d) (v, lazyPorts d (false, p)) := by
    rw [← rowIndex_rotation, lazy_rotation_false]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      trueRelation := by
    apply relation_ext_inline_PreprocessingLazyWords
    intro a b
    simpa only [PortTables.accepts, relationAt, trueRelation, Fin.getElem_fin,
      Vector.getElem_replicate] using lazy_accepts_false table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem row_lazy_move (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (true, p)) = moveRow table v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      rowIndex n (2 * d) ((rotation table (v, p)).1,
        lazyPorts d (true, (rotation table (v, p)).2)) := by
    rw [← rowIndex_rotation, lazy_rotation_true]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      table.relations[rowIndex n d (v, p)] := by
    apply relation_ext_inline_PreprocessingLazyWords
    intro a b
    exact lazy_accepts_true table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem flatRows_list (table : PortTables.Table n d) :
    (flatRows table).toList =
      (List.ofFn fun v : Fin n => List.ofFn (row table v)).flatten := by
  rw [flatRows, Vector.toList_ofFn, ofFn_rowIndex]
  simp only [Equiv.symm_apply_apply]
  rfl

def vertexRows (table : PortTables.Table n d) (v : Fin n) :
    List (DartRow n (n * (2 * d))) :=
  List.ofFn (stayRow d v) ++ List.ofFn (moveRow table v)

theorem flatRows_lazy (table : PortTables.Table n d) :
    (flatRows (lazy table)).toList = (List.ofFn (vertexRows table)).flatten := by
  rw [flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_lazyPorts]
  simp only [row_lazy_stay, row_lazy_move]
  rfl

theorem tableWords_lazy (table : PortTables.Table n d) :
    PortTables.tableWords (lazy table) =
      [n, n * (2 * d)] ++ (List.ofFn (vertexRows table)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_lazy]

theorem tableBits_lazy (table : PortTables.Table n d) :
    PortTables.tableBits (lazy table) =
      encodeWords ([n, n * (2 * d)] ++
        (List.ofFn (vertexRows table)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (lazy table)) = _
  rw [tableWords_lazy]

end DFVSGames.Foundations.PCP.PreprocessingLazyWords
end

section

namespace DFVSGames.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

def streamRelationCopy (d : Nat) (source destination : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d) :=
  MachineStateEquiv.statement (relationStateEquiv A d)
    (MachineRegularOriginalRow.relationCopyAt source destination exit)

theorem streamRelationCopy_step (d : Nat) (positive : 0 < d)
    (source destination : K) (different : source ≠ destination)
    (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (code : program label = streamRelationCopy d source destination exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base source = encodeWords (relationWords relation) ++ suffix) (ambient : A) :
    TM2.step program ⟨some label, streamClean d positive ambient, base⟩ =
      some ⟨exit, streamClean d positive ambient,
        Function.update (Function.update base source suffix) destination
          (encodeWords (relationWords relation) ++ base destination)⟩ := by
  have hraw := MachineRegularOriginalRow.relationCopy_step source destination different label exit
    (fun _ => MachineRegularOriginalRow.relationCopyAt source destination exit) rfl
    relation suffix base input (ambient, MachineFixedDivMod.residue d positive 0)
    MachineRegularOriginalRow.zeroBuffer none
  have haux := Option.some.inj hraw
  change some (TM2.stepAux (program label) (streamClean d positive ambient) base) = _
  rw [code, streamRelationCopy, MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (relationStateEquiv A d)
    (TM2.stepAux (MachineRegularOriginalRow.relationCopyAt source destination exit)
      (((ambient, MachineFixedDivMod.residue d positive 0),
        MachineRegularOriginalRow.zeroBuffer), none) base)) = _
  rw [haux]
  rfl

def streamInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : StreamLabel d → Λ) (exit : Option Λ) :
    StreamLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | .tailStart => Hastad.SourceMachine.fieldStart (tape 0) (labels .tailRead)
  | .tailRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 0) (labels .tailRead)
      (some (labels .reverseStart))
  | .reverseStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .reverseRead)
  | .reverseRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1) (labels .reverseRead)
      (some (labels .copyRelation))
  | .copyRelation => streamRelationCopy d (tape 9) (tape 2)
      (some (labels (.row (.inl .copySeed))))
  | .row stage => reindexInstruction d positive c b (tape ∘ bodyIndex)
      (fun stage => labels (.row stage)) (some (labels .clearTail)) stage
  | .clearTail => MachineDrain.drain (tape 0) (labels .clearTail) (some (labels .clearOld))
  | .clearOld => MachineDrain.drain (tape 1) (labels .clearOld) (some (labels .clearRelation))
  | .clearRelation => MachineDrain.drain (tape 2) (labels .clearRelation) (some (labels .clearNew))
  | .clearNew => MachineDrain.drain (tape 6) (labels .clearNew) exit

theorem streamRowTrace (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : StreamLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = streamInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (v j : Nat) (relation : RelationTable) (suffix : List Bool)
    (input : base (tape 9) = inputRowBits v j relation ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A) :
    (advance (TM2.step program))^[streamRowSteps d c b v j relation (base (tape 7))]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamResultTapes d c b v j relation tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have hb6 : bodyIndex 6 = 6 := rfl
  have hb7 : bodyIndex 7 = 7 := rfl
  have h₀ := empty 0 (by decide) (by decide)
  have h₁ := empty 1 (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide)
  let relationBits := encodeWords (relationWords relation)
  let tailLoaded := Function.update (Function.update base (tape 9)
    (encodeWord j ++ (relationBits ++ suffix))) (tape 0) (encodeWord v)
  let reverseLoaded := Function.update (Function.update tailLoaded (tape 9)
    (relationBits ++ suffix)) (tape 1) (encodeWord j)
  let loaded := Function.update (Function.update reverseLoaded (tape 9) suffix) (tape 2) relationBits
  let rowed := reindexResultTapes d c b v j relation (tape ∘ bodyIndex) loaded
  let tailCleared := Function.update rowed (tape 0) []
  let oldCleared := Function.update tailCleared (tape 1) []
  let relationCleared := Function.update oldCleared (tape 2) []
  have tailRun : (advance (TM2.step program))^[v + 2]
      (some ⟨some (labels .tailStart), streamClean d positive ambient, base⟩) =
      some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 0) (hd 9 0 (by decide))
      (labels .tailStart) (labels .tailRead) (some (labels .reverseStart)) program
      (atLabels .tailStart) (atLabels .tailRead) base v
      (encodeWord j ++ (relationBits ++ suffix))
      (by simpa only [inputRowBits, List.append_assoc] using input)
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      h₀, List.append_nil] at h
    convert h using 1 <;> rfl
  have reverseRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .reverseStart), streamClean d positive ambient, tailLoaded⟩) =
      some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩ := by
    have hstart : tailLoaded (tape 1) = [] := by
      simp [tailLoaded, hd 1 0 (by decide), hd 1 9 (by decide), h₁]
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .reverseStart) (labels .reverseRead) (some (labels .copyRelation)) program
      (atLabels .reverseStart) (atLabels .reverseRead) tailLoaded j (relationBits ++ suffix)
      (by simp [tailLoaded, hd 9 0 (by decide)])
      ((ambient, MachineRegularOriginalRow.zeroBuffer),
        MachineFixedDivMod.residue d positive 0) none).evals_in_steps
    simp only [Hastad.SourceMachine.fieldInTime, Hastad.SourceMachine.fieldTapes,
      hstart, List.append_nil] at h
    convert h using 1 <;> rfl
  have copyRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), streamClean d positive ambient, reverseLoaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩ := by
    have hempty : reverseLoaded (tape 2) = [] := by
      simp [reverseLoaded, tailLoaded, hd 2 1 (by decide), hd 2 9 (by decide),
        hd 2 0 (by decide), h₂]
    have h := streamRelationCopy_step d positive (tape 9) (tape 2) (hd 9 2 (by decide))
      (labels .copyRelation) (some (labels (.row (.inl .copySeed)))) program
      (atLabels .copyRelation) relation suffix reverseLoaded
      (by simp [reverseLoaded, relationBits, hd 9 1 (by decide)]) ambient
    simpa only [Function.iterate_one, advance_some, hempty, List.append_nil, loaded] using h
  have hs (i : Fin 10) (hi : i ≠ 0) (hi' : i ≠ 1) (hi'' : i ≠ 2) (hi''' : i ≠ 9) :
      loaded (tape i) = base (tape i) := by
    simp [loaded, reverseLoaded, tailLoaded, hd i 0 hi, hd i 1 hi',
      hd i 2 hi'', hd i 9 hi''']
  have loadedTail : loaded (tape 0) = encodeWord v := by
    simp [loaded, reverseLoaded, tailLoaded, hd 0 2 (by decide), hd 0 9 (by decide),
      hd 0 1 (by decide)]
  have loadedReverse : loaded (tape 1) = encodeWord j := by
    simp [loaded, reverseLoaded, hd 1 2 (by decide), hd 1 9 (by decide)]
  have loadedRelation : loaded (tape 2) = relationBits := by simp [loaded]
  have bodyRun := reindexRowTrace d positive c b (tape ∘ bodyIndex)
    (distinct.comp bodyIndex_injective) (fun stage => labels (.row stage))
    (some (labels .clearTail)) program (fun stage => atLabels (.row stage)) loaded v j relation
    loadedTail loadedReverse loadedRelation
    ((hs 3 (by decide) (by decide) (by decide) (by decide)).trans h₃)
    ((hs 4 (by decide) (by decide) (by decide) (by decide)).trans h₄)
    ((hs 5 (by decide) (by decide) (by decide) (by decide)).trans h₅)
    ((hs 6 (by decide) (by decide) (by decide) (by decide)).trans h₆)
    ((hs 8 (by decide) (by decide) (by decide) (by decide)).trans h₈)
    (ambient, MachineRegularOriginalRow.zeroBuffer)
  have hout : loaded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[reindexSteps d c b v j relation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), streamClean d positive ambient, loaded⟩) =
    some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩ at bodyRun
  have rowedTail : rowed (tape 0) = encodeWord v := by
    simp only [rowed, reindexResultTapes, reindexMappedTapes, Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 0 7 (by decide)),
      Function.update_of_ne (hd 0 6 (by decide))] using loadedTail
  have rowedOld : tailCleared (tape 1) = encodeWord j := by
    simp only [tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 1 0 (by decide)),
      Function.update_of_ne (hd 1 7 (by decide)), Function.update_of_ne (hd 1 6 (by decide))]
      using loadedReverse
  have rowedRelation : oldCleared (tape 2) = relationBits := by
    simp only [oldCleared, tailCleared, rowed, reindexResultTapes, reindexMappedTapes,
      Function.comp_apply, hb6, hb7]
    simpa only [Function.update_of_ne (hd 2 1 (by decide)),
      Function.update_of_ne (hd 2 0 (by decide)), Function.update_of_ne (hd 2 7 (by decide)),
      Function.update_of_ne (hd 2 6 (by decide))] using loadedRelation
  have rowedNew : relationCleared (tape 6) = encodeWord (MachinePortReindex.value d c b j) := by
    simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
      reindexMappedTapes, Function.comp_apply, bodyIndex, hd 6 2 (by decide),
      hd 6 1 (by decide), hd 6 0 (by decide), hd 6 7 (by decide)]
  have clearTail := (MachineDrain.drainInTime (tape 0) (labels .clearTail)
    (some (labels .clearOld)) program (atLabels .clearTail) rowed
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 0)).length + 1]
    (some ⟨some (labels .clearTail), streamClean d positive ambient, rowed⟩) =
    some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩ at clearTail
  rw [rowedTail, encodeWord_length] at clearTail
  have clearOld := (MachineDrain.drainInTime (tape 1) (labels .clearOld)
    (some (labels .clearRelation)) program (atLabels .clearOld) tailCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(tailCleared (tape 1)).length + 1]
    (some ⟨some (labels .clearOld), streamClean d positive ambient, tailCleared⟩) =
    some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩ at clearOld
  rw [rowedOld, encodeWord_length] at clearOld
  have clearRelation := (MachineDrain.drainInTime (tape 2) (labels .clearRelation)
    (some (labels .clearNew)) program (atLabels .clearRelation) oldCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 2)).length + 1]
    (some ⟨some (labels .clearRelation), streamClean d positive ambient, oldCleared⟩) =
    some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩ at clearRelation
  rw [rowedRelation] at clearRelation
  have clearNew := (MachineDrain.drainInTime (tape 6) (labels .clearNew)
    exit program (atLabels .clearNew) relationCleared
    ((ambient, MachineRegularOriginalRow.zeroBuffer),
      MachineFixedDivMod.residue d positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(relationCleared (tape 6)).length + 1]
    (some ⟨some (labels .clearNew), streamClean d positive ambient, relationCleared⟩) =
    some ⟨exit, streamClean d positive ambient,
      Function.update relationCleared (tape 6) []⟩ at clearNew
  rw [rowedNew, encodeWord_length] at clearNew
  have finalFrame : Function.update relationCleared (tape 6) [] =
      streamResultTapes d c b v j relation tape base suffix := by
    funext k
    by_cases h6 : k = tape 6
    · subst k
      simp [streamResultTapes, hd 6 7 (by decide), hd 6 9 (by decide), h₆]
    · by_cases h2 : k = tape 2
      · subst k
        simp [relationCleared, streamResultTapes, hd 2 6 (by decide),
          hd 2 7 (by decide), hd 2 9 (by decide), h₂]
      · by_cases h1 : k = tape 1
        · subst k
          simp [relationCleared, oldCleared, streamResultTapes,
            hd 1 6 (by decide), hd 1 2 (by decide), hd 1 7 (by decide),
            hd 1 9 (by decide), h₁]
        · by_cases h0 : k = tape 0
          · subst k
            simp [relationCleared, oldCleared, tailCleared, streamResultTapes,
              hd 0 6 (by decide), hd 0 2 (by decide), hd 0 1 (by decide),
              hd 0 7 (by decide), hd 0 9 (by decide), h₀]
          · by_cases h7 : k = tape 7
            · subst k
              simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                reindexMappedTapes, Function.comp_apply, bodyIndex, streamResultTapes,
                loaded, reverseLoaded, tailLoaded, hd 7 6 (by decide), hd 7 2 (by decide),
                hd 7 1 (by decide), hd 7 0 (by decide), hd 7 9 (by decide)]
            · by_cases h9 : k = tape 9
              · subst k
                simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, hd 9 6 (by decide), hd 9 2 (by decide),
                  hd 9 1 (by decide), hd 9 0 (by decide), hd 9 7 (by decide)]
              · simp [relationCleared, oldCleared, tailCleared, rowed, reindexResultTapes,
                  reindexMappedTapes, Function.comp_apply, bodyIndex, loaded, reverseLoaded,
                  tailLoaded, streamResultTapes, h6, h2, h1, h0, h7, h9]
  rw [finalFrame] at clearNew
  exact joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows
    (joinTrace_inline_MachineLazyRows tailRun reverseRun) copyRun) bodyRun) clearTail) clearOld) clearRelation) clearNew

end DFVSGames.Foundations.Complexity.MachineLazyRows
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_VertexLabel
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace DFVSGames.Foundations.Complexity.MachineLazyRows
open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)
variable {K Λ A : Type} [DecidableEq K]

def vertexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : VertexLabel d → Λ) (exit : Option Λ) :
    VertexLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | (i, none) => if i.val < d then .goto fun _ => labels (i, some .tailStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < d then
      streamInstruction d positive c b tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

theorem streamFrame_afterRow_inline_MachineLazyRows {n m : Nat} (d c b : Nat) (r : DartRow n m)
    (tape : Fin 10 → K) (distinct : Function.Injective tape) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) :
    streamResultTapes d c b r.tail.val r.reverseIndex.val r.relation tape
      (streamFrame tape base (r :: rows) output) (recordsInput rows ++ base (tape 9)) =
      streamFrame tape base rows
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) := by
  have h79 : tape 7 ≠ tape 9 := fun h => (by decide : (7 : Fin 10) ≠ 9) (distinct h)
  funext k
  by_cases h7 : k = tape 7
  · subst k
    simp [streamResultTapes, streamFrame]
  · by_cases h9 : k = tape 9
    · subst k
      simp [streamResultTapes, streamFrame, Ne.symm h79]
    · simp [streamResultTapes, streamFrame, h7, h9]

theorem vertexSuffixTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = []) (ambient : A)
    (remaining : Nat) (i : Fin (d + 1)) (count : i.val + remaining = d) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b ((List.ofFn rows).drop i.val) output]
      (some ⟨some (labels (i, none)), streamClean d positive ambient,
        streamFrame tape base ((List.ofFn rows).drop i.val) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base []
          (output ++ recordsOutput d c b ((List.ofFn rows).drop i.val))⟩ := by
  have hd (a k : Fin 10) (h : a ≠ k) : tape a ≠ tape k := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = d := by omega
      have hdrop : (List.ofFn rows).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, recordsOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < d := by omega
      let port : Fin d := ⟨i.val, hi⟩
      let next : Fin (d + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn rows).drop (i.val + 1)
      have split : (List.ofFn rows).drop i.val = rows port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn rows)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (rows port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), streamClean d positive ambient, initial⟩) =
          some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := streamRowTrace d positive c b tape distinct
        (fun stage => labels (i, some stage)) (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using (atLabels (i, some stage)))
        initial (rows port).tail.val (rows port).reverseIndex.val (rows port).relation
        (recordsInput rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 9 7 (by decide), recordsInput, List.append_assoc])
        (by
          intro k hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[streamRowSteps d c b
        (rows port).tail.val (rows port).reverseIndex.val (rows port).relation output]
        (some ⟨some (labels (i, some .tailStart)), streamClean d positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
            (rows port).relation tape initial (recordsInput rest ++ base (tape 9))⟩ at body
      rw [show streamResultTapes d c b (rows port).tail.val (rows port).reverseIndex.val
        (rows port).relation tape initial (recordsInput rest ++ base (tape 9)) =
        streamFrame tape base rest
          (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) from
          streamFrame_afterRow_inline_MachineLazyRows d c b (rows port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = d := by dsimp [next]; omega
      have tail := ih next nextCount
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)
      change (advance (TM2.step program))^[vertexSteps d c b rest
        (output ++ reindexRowBits d c b (rows port).tail.val
          (rows port).reverseIndex.val (rows port).relation)]
        (some ⟨some (labels (next, none)), streamClean d positive ambient,
          streamFrame tape base rest (output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation)⟩) =
        some ⟨exit, streamClean d positive ambient,
          streamFrame (n := n) (m := m) tape base [] ((output ++ reindexRowBits d c b (rows port).tail.val
            (rows port).reverseIndex.val (rows port).relation) ++ recordsOutput d c b rest)⟩ at tail
      rw [split]
      have all := joinTrace_inline_MachineLazyRows (joinTrace_inline_MachineLazyRows boundary body) tail
      simpa only [vertexSteps, initial, recordsOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace {n m : Nat} (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 10 → K) (distinct : Function.Injective tape)
    (labels : VertexLabel d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d positive c b tape labels exit l)
    (base : K → List Bool) (rows : Fin d → DartRow n m)
    (empty : ∀ i : Fin 10, i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d c b (List.ofFn rows) output]
      (some ⟨some (labels (0, none)), streamClean d positive ambient,
        streamFrame tape base (List.ofFn rows) output⟩) =
      some ⟨exit, streamClean d positive ambient,
        streamFrame (n := n) (m := m) tape base [] (output ++ recordsOutput d c b (List.ofFn rows))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d positive c b tape distinct
    labels exit program atLabels base rows empty ambient d 0 (by simp) output

theorem streamRowSteps_le {n m : Nat} (d c b : Nat) (r : DartRow n m) (output : List Bool) :
    streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output ≤
      rowCostBound c b n m + 2 * output.length := by
  have htail := r.tail.isLt.le
  have hj := r.reverseIndex.isLt.le
  have hdiv := (Nat.div_le_self r.reverseIndex.val d).trans hj
  have hvalue := reindexValue_le d c b r
  have hrelation := relationBits_length_le r.relation
  have hsize := reindexRowBits_length_le d c b r
  unfold streamRowSteps reindexSteps MachinePortReindex.steps rowCostBound
  omega

theorem vertexSteps_le_capacity_inline_MachineLazyRows {n m : Nat} (d c b capacity : Nat)
    (rows : List (DartRow n m)) (output : List Bool)
    (room : output.length + rows.length * rowSizeBound c b n m ≤ capacity) :
    vertexSteps d c b rows output ≤
      rows.length * (rowCostBound c b n m + 2 * capacity + 1) + 1 := by
  induction rows generalizing output with
  | nil => simp [vertexSteps]
  | cons r rows ih =>
      have hsize := reindexRowBits_length_le d c b r
      have hcost := streamRowSteps_le d c b r output
      have hout : output.length ≤ capacity := by omega
      have hroom : (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation).length +
          rows.length * rowSizeBound c b n m ≤ capacity := by
        rw [List.length_append]
        simp only [List.length_cons, Nat.succ_mul] at room
        omega
      have htail := ih
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) hroom
      change 1 + streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output +
        vertexSteps d c b rows
          (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) ≤
        (rows.length + 1) * (rowCostBound c b n m + 2 * capacity + 1) + 1
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem vertexSteps_le {n m : Nat} (d c b : Nat) (rows : List (DartRow n m))
    (output : List Bool) :
    vertexSteps d c b rows output ≤ rows.length * (rowCostBound c b n m +
      2 * (output.length + rows.length * rowSizeBound c b n m) + 1) + 1 :=
  vertexSteps_le_capacity_inline_MachineLazyRows d c b _ rows output (Nat.le_refl _)

end DFVSGames.Foundations.Complexity.MachineLazyRows
end

section

namespace DFVSGames.Foundations.PCP.PreprocessingOverlayWords

open PortTables GraphTables PreprocessingOverlayTables
open Complexity

variable {n d e : Nat}

abbrev row := @PreprocessingLazyWords.row

theorem row_overlay_old (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin d) :
    row (overlay G H) v (overlayPorts d e (.inl p)) = oldRow G e v p := by
  have hr : (overlay G H).reverseIndex[rowIndex n (d + e) (v, overlayPorts d e (.inl p))] =
      rowIndex n (d + e) ((rotation G (v, p)).1,
        overlayPorts d e (.inl (rotation G (v, p)).2)) := by
    rw [← rowIndex_rotation, overlay_rotation_old]
  have hp : (overlay G H).relations[rowIndex n (d + e) (v, overlayPorts d e (.inl p))] =
      G.relations[rowIndex n d (v, p)] := by
    apply relation_ext_inline_PreprocessingOverlayWords
    exact overlay_accepts_old G H v p
  exact congrArg₂ (DartRow.mk v) hr hp

theorem row_overlay_expander (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin e) :
    row (overlay G H) v (overlayPorts d e (.inr p)) = expanderRow d H v p := by
  have hr : (overlay G H).reverseIndex[rowIndex n (d + e) (v, overlayPorts d e (.inr p))] =
      rowIndex n (d + e) ((ExpanderTables.lookup H (v, p)).1,
        overlayPorts d e (.inr (ExpanderTables.lookup H (v, p)).2)) := by
    rw [← rowIndex_rotation, overlay_rotation_expander]
  have hp : (overlay G H).relations[rowIndex n (d + e) (v, overlayPorts d e (.inr p))] =
      trueRelation := by
    apply relation_ext_inline_PreprocessingOverlayWords
    intro a b
    simpa only [PortTables.accepts, relationAt, trueRelation,
      PreprocessingLazyWords.trueRelation, Fin.getElem_fin, Vector.getElem_replicate] using
      overlay_accepts_expander G H v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem oldRow_reverse_val (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (oldRow G e v p).reverseIndex.val = oldReverseMap d e (row G v p).reverseIndex.val := by
  simp only [oldRow, rowIndex_val, overlayPorts_inl_val, oldReverseMap, row,
    PreprocessingLazyWords.row]
  change (G.reverseIndex[rowIndex n d (v, p)]).val % d +
      (d + e) * ((G.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem oldRow_words (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (oldRow G e v p) =
      [v.val, oldReverseMap d e (row G v p).reverseIndex.val] ++
        relationWords (row G v p).relation := by
  rw [rowWords, oldRow_reverse_val]
  rfl

theorem flatRows_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    (flatRows (overlay G H)).toList = (List.ofFn (vertexRows G H)).flatten := by
  rw [PreprocessingLazyWords.flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_overlayPorts]
  simp only [row_overlay_old, row_overlay_expander]
  rfl

theorem tableWords_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableWords (overlay G H) =
      [n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_overlay]

theorem tableBits_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableBits (overlay G H) = encodeWords
      ([n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (overlay G H)) = _
  rw [tableWords_overlay]

end DFVSGames.Foundations.PCP.PreprocessingOverlayWords

end

section

namespace DFVSGames.Foundations.Complexity.MachineOverlayRows

open Turing MachineComposition
open PCP.GraphTables PCP.PreprocessingOverlayWords
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

theorem rowTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : Label e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = instruction d e positive tape labels exit l)
    (base : K → List Bool) (v j : Nat) (suffix : List Bool)
    (tailWord : base (tape 0) = encodeWord v)
    (inputWord : base (tape 9) = encodeWord j ++ suffix)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) :
    (advance (TM2.step program))^[rowSteps d e v j (base (tape 7))]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        resultTapes d e v j tape base suffix⟩ := by
  have hd (i k : Fin 10) (h : i ≠ k) : tape i ≠ tape k := fun x => h (distinct x)
  have h₁ := empty 1 (by decide) (by decide) (by decide)
  have h₂ := empty 2 (by decide) (by decide) (by decide)
  have h₃ := empty 3 (by decide) (by decide) (by decide)
  have h₄ := empty 4 (by decide) (by decide) (by decide)
  have h₅ := empty 5 (by decide) (by decide) (by decide)
  have h₆ := empty 6 (by decide) (by decide) (by decide)
  have h₈ := empty 8 (by decide) (by decide) (by decide)
  have hi0 : bodyIndex 0 = 0 := rfl
  have hi3 : bodyIndex 3 = 3 := rfl
  have hi4 : bodyIndex 4 = 4 := rfl
  have hi5 : bodyIndex 5 = 5 := rfl
  have hi6 : bodyIndex 6 = 6 := rfl
  have hi8 : bodyIndex 8 = 8 := rfl
  let loaded := Function.update (Function.update base (tape 9) suffix) (tape 1) (encodeWord j)
  let seeded := Function.update loaded (tape 2) trueBits
  let rowed := MachineLazyRows.reindexResultTapes e (d + e) d v j trueRelation
    (tape ∘ bodyIndex) seeded
  let oldCleared := Function.update rowed (tape 1) []
  let newCleared := Function.update oldCleared (tape 6) []
  have loadRun : (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩ := by
    have h := (Hastad.SourceMachine.fieldInTime (tape 9) (tape 1) (hd 9 1 (by decide))
      (labels .loadStart) (labels .loadLoop) (some (labels .seedRelation)) program
      (atLabels .loadStart) (atLabels .loadLoop) base j suffix inputWord
      (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
    change (advance (TM2.step program))^[j + 2]
      (some ⟨some (labels .loadStart), MachinePortReindex.clean e positive ambient, base⟩) =
      some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient,
        Hastad.SourceMachine.fieldTapes (tape 9) (tape 1) base suffix
          (encodeWord j ++ base (tape 1))⟩ at h
    simpa only [Hastad.SourceMachine.fieldTapes,
      h₁, List.append_nil, MachinePortReindex.clean, loaded] using h
  have seedRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seedRelation), MachinePortReindex.clean e positive ambient, loaded⟩) =
      some ⟨some (labels (.row (.inl .copySeed))),
        MachinePortReindex.clean e positive ambient, seeded⟩ := by
    change some (TM2.stepAux (program (labels .seedRelation)) _ _) = _
    rw [atLabels]
    simp [instruction, stepAux_pushWord, TM2.stepAux, seeded, loaded,
      hd 2 1 (by decide), hd 2 9 (by decide), h₂]
  have hs (i : Fin 10) (hi : i ≠ 1) (hi' : i ≠ 2) (hi'' : i ≠ 9) :
      seeded (tape i) = base (tape i) := by
    simp [seeded, loaded, hd i 1 hi, hd i 2 hi', hd i 9 hi'']
  have bodyRun := MachineLazyRows.reindexRowTrace e positive (d + e) d
    (tape ∘ bodyIndex) (distinct.comp bodyIndex_injective) (fun s => labels (.row s))
    (some (labels .drainOld)) program (fun s => atLabels (.row s)) seeded v j trueRelation
    (by simpa only [Function.comp_apply, hi0] using
      (hs 0 (by decide) (by decide) (by decide)).trans tailWord)
    (by simp [seeded, loaded, Function.comp_apply, bodyIndex, hd 1 2 (by decide)])
    (by simp [seeded, Function.comp_apply, bodyIndex, trueBits])
    (by simpa only [Function.comp_apply, hi3] using
      (hs 3 (by decide) (by decide) (by decide)).trans h₃)
    (by simpa only [Function.comp_apply, hi4] using
      (hs 4 (by decide) (by decide) (by decide)).trans h₄)
    (by simpa only [Function.comp_apply, hi5] using
      (hs 5 (by decide) (by decide) (by decide)).trans h₅)
    (by simpa only [Function.comp_apply, hi6] using
      (hs 6 (by decide) (by decide) (by decide)).trans h₆)
    (by simpa only [Function.comp_apply, hi8] using
      (hs 8 (by decide) (by decide) (by decide)).trans h₈) ambient
  have hout : seeded ((tape ∘ bodyIndex) 7) = base (tape 7) :=
    hs 7 (by decide) (by decide) (by decide)
  rw [hout] at bodyRun
  change (advance (TM2.step program))^[MachineLazyRows.reindexSteps e (d + e) d v j
      trueRelation (base (tape 7))]
    (some ⟨some (labels (.row (.inl .copySeed))), MachinePortReindex.clean e positive ambient, seeded⟩) =
    some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩ at bodyRun
  have rowedOld : rowed (tape 1) = encodeWord j := by
    simp [rowed, MachineLazyRows.reindexResultTapes, MachineLazyRows.reindexMappedTapes,
      Function.comp_apply, bodyIndex, seeded, loaded, hd 1 7 (by decide),
      hd 1 6 (by decide), hd 1 2 (by decide)]
  have rowedNew : oldCleared (tape 6) = encodeWord (MachinePortReindex.value e (d + e) d j) := by
    simp [oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
      hd 6 1 (by decide), hd 6 7 (by decide)]
  have rowedRelation : newCleared (tape 2) = trueBits := by
    simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
      MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex, seeded,
      hd 2 6 (by decide), hd 2 1 (by decide), hd 2 7 (by decide)]
  have drainOld := (MachineDrain.drainInTime (tape 1) (labels .drainOld)
    (some (labels .drainNew)) program (atLabels .drainOld) rowed
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(rowed (tape 1)).length + 1]
    (some ⟨some (labels .drainOld), MachinePortReindex.clean e positive ambient, rowed⟩) =
    some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩ at drainOld
  rw [rowedOld, encodeWord_length] at drainOld
  have drainNew := (MachineDrain.drainInTime (tape 6) (labels .drainNew)
    (some (labels .drainRelation)) program (atLabels .drainNew) oldCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(oldCleared (tape 6)).length + 1]
    (some ⟨some (labels .drainNew), MachinePortReindex.clean e positive ambient, oldCleared⟩) =
    some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩ at drainNew
  rw [rowedNew, encodeWord_length] at drainNew
  have drainRelation := (MachineDrain.drainInTime (tape 2) (labels .drainRelation)
    exit program (atLabels .drainRelation) newCleared
    (ambient, MachineFixedDivMod.residue e positive 0) none).evals_in_steps
  change (advance (TM2.step program))^[(newCleared (tape 2)).length + 1]
    (some ⟨some (labels .drainRelation), MachinePortReindex.clean e positive ambient, newCleared⟩) =
    some ⟨exit, MachinePortReindex.clean e positive ambient,
      Function.update newCleared (tape 2) []⟩ at drainRelation
  rw [rowedRelation] at drainRelation
  have finalFrame : Function.update newCleared (tape 2) [] = resultTapes d e v j tape base suffix := by
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [resultTapes, hd 2 7 (by decide), hd 2 9 (by decide), h₂]
    · by_cases h6 : k = tape 6
      · subst k
        simp [newCleared, resultTapes, hd 6 2 (by decide), hd 6 7 (by decide),
          hd 6 9 (by decide), h₆]
      · by_cases h1 : k = tape 1
        · subst k
          simp [newCleared, oldCleared, resultTapes, hd 1 2 (by decide),
            hd 1 6 (by decide), hd 1 7 (by decide), hd 1 9 (by decide), h₁]
        · by_cases h7 : k = tape 7
          · subst k
            simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              resultTapes, rowBits, seeded, loaded, hd 7 2 (by decide),
              hd 7 6 (by decide), hd 7 1 (by decide), hd 7 9 (by decide)]
          · simp [newCleared, oldCleared, rowed, MachineLazyRows.reindexResultTapes,
              MachineLazyRows.reindexMappedTapes, Function.comp_apply, bodyIndex,
              seeded, loaded, resultTapes, h2, h6, h1, h7]
  rw [finalFrame] at drainRelation
  exact joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows loadRun seedRun) bodyRun)
    drainOld) drainNew) drainRelation

theorem vertexSuffixTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (remaining : Nat) (i : Fin (e + 1)) (count : i.val + remaining = e)
    (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v ((List.ofFn values).drop i.val) output]
      (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base ((List.ofFn values).drop i.val) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v ((List.ofFn values).drop i.val))⟩ := by
  have hd (a b : Fin 10) (h : a ≠ b) : tape a ≠ tape b := fun x => h (distinct x)
  induction remaining generalizing i output with
  | zero =>
      have hi : i.val = e := by omega
      have hdrop : (List.ofFn values).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [List.length_ofFn, hi, le_refl]
      rw [hdrop]
      simp only [vertexSteps, streamOutput, List.flatMap_nil, List.append_nil]
      change some (TM2.stepAux (program (labels (i, none))) _ _) = _
      rw [atLabels]
      cases exit <;> simp [vertexInstruction, hi, MachinePortReindex.exitAt, TM2.stepAux]
  | succ remaining ih =>
      have hi : i.val < e := by omega
      let port : Fin e := ⟨i.val, hi⟩
      let next : Fin (e + 1) := ⟨i.val + 1, by omega⟩
      let rest := (List.ofFn values).drop (i.val + 1)
      have split : (List.ofFn values).drop i.val = values port :: rest := by
        have h := List.getElem_cons_drop (as := List.ofFn values)
          (i := i.val) (by simpa only [List.length_ofFn] using hi)
        simpa only [List.getElem_ofFn, port, rest] using h.symm
      let initial := streamFrame tape base (values port :: rest) output
      have boundary : (advance (TM2.step program))^[1]
          (some ⟨some (labels (i, none)), MachinePortReindex.clean e positive ambient, initial⟩) =
          some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩ := by
        change some (TM2.stepAux (program (labels (i, none))) _ _) = _
        rw [atLabels]
        simp [vertexInstruction, hi, TM2.stepAux]
      have body := rowTrace d e positive tape distinct (fun stage => labels (i, some stage))
        (some (labels (next, none))) program
        (by
          intro stage
          simpa only [vertexInstruction, hi, dite_true, next] using
            (atLabels (i, some stage))) initial v (values port)
        (encodeWords rest ++ base (tape 9))
        (by simp [initial, streamFrame, hd 0 7 (by decide), hd 0 9 (by decide), tailWord])
        (by simp [initial, streamFrame, hd 9 7 (by decide), encodeWords, List.append_assoc])
        (by
          intro k hk0 hk7 hk9
          simp [initial, streamFrame, hd k 7 hk7, hd k 9 hk9, empty k hk0 hk7 hk9]) ambient
      have initialOutput : initial (tape 7) = output := by simp [initial, streamFrame]
      rw [initialOutput] at body
      change (advance (TM2.step program))^[rowSteps d e v (values port) output]
        (some ⟨some (labels (i, some .loadStart)), MachinePortReindex.clean e positive ambient, initial⟩) =
        some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9))⟩ at body
      rw [show resultTapes d e v (values port) tape initial (encodeWords rest ++ base (tape 9)) =
        streamFrame tape base rest (output ++ rowBits d e v (values port)) from
          streamFrame_afterRow_inline_MachineOverlayRows d e v (values port) tape distinct base rest output] at body
      have nextCount : next.val + remaining = e := by dsimp [next]; omega
      have tail := ih next nextCount (output ++ rowBits d e v (values port))
      change (advance (TM2.step program))^[vertexSteps d e v rest (output ++ rowBits d e v (values port))]
        (some ⟨some (labels (next, none)), MachinePortReindex.clean e positive ambient,
          streamFrame tape base rest (output ++ rowBits d e v (values port))⟩) =
        some ⟨exit, MachinePortReindex.clean e positive ambient,
          streamFrame tape base [] ((output ++ rowBits d e v (values port)) ++ streamOutput d e v rest)⟩ at tail
      rw [split]
      have all := joinTrace_inline_MachineOverlayRows (joinTrace_inline_MachineOverlayRows boundary body) tail
      simpa only [vertexSteps, initial, streamOutput, List.flatMap_cons, List.append_assoc] using all

theorem vertexTrace (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (labels : VertexLabel e → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A e))
    (atLabels : ∀ l, program (labels l) = vertexInstruction d e positive tape labels exit l)
    (base : K → List Bool) (v : Nat) (values : Fin e → Nat)
    (tailWord : base (tape 0) = encodeWord v)
    (empty : ∀ i : Fin 10, i ≠ 0 → i ≠ 7 → i ≠ 9 → base (tape i) = [])
    (ambient : A) (output : List Bool) :
    (advance (TM2.step program))^[vertexSteps d e v (List.ofFn values) output]
      (some ⟨some (labels (0, none)), MachinePortReindex.clean e positive ambient,
        streamFrame tape base (List.ofFn values) output⟩) =
      some ⟨exit, MachinePortReindex.clean e positive ambient,
        streamFrame tape base [] (output ++ streamOutput d e v (List.ofFn values))⟩ := by
  simpa only [Fin.val_zero, List.drop_zero] using vertexSuffixTrace d e positive tape distinct
    labels exit program atLabels base v values tailWord empty ambient e 0 (by simp) output

end DFVSGames.Foundations.Complexity.MachineOverlayRows

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineOverlayTable
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineOverlayTable

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding

variable {A : Type}

abbrev Ambient (A : Type) (d e : Nat) := ((A × Fin e) × MachineLazyRows.Buffer) × Fin d
abbrev State (A : Type) (d e : Nat) := Ambient A d e × Option Bool

def clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : A) : State A d e :=
  MachineLazyRows.streamClean d hd (a, MachineFixedDivMod.residue e he 0)

def expanderState (A : Type) (d e : Nat) :
    MachineOverlayRows.State ((A × MachineLazyRows.Buffer) × Fin d) e ≃ State A d e where
  toFun
    | ((((a, buffer), rd), re), bit) => ((((a, re), buffer), rd), bit)
  invFun
    | ((((a, re), buffer), rd), bit) => ((((a, buffer), rd), re), bit)
  left_inv := by rintro ⟨⟨⟨⟨a, buffer⟩, rd⟩, re⟩, bit⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨a, re⟩, buffer⟩, rd⟩, bit⟩; rfl

theorem expanderState_clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : A) :
    expanderState A d e (MachinePortReindex.clean e he
      ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0)) =
      clean d e hd he a := rfl

def mainInstruction (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    MainLabel d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State A d e)
  | .copyHFirst => Reduction.MachineTransfer.loopAt expanderArchive scratch id false
      (.inr .copyHFirst) (next .copyHSecond)
  | .copyHSecond => MachineCopy.forkLoop scratch expanderArchive expanderStream false
      (.inr .copyHSecond) (next .countSeed)
  | .countSeed => MachineUnaryAffineAt.seed output 0 (.inr .countScan)
  | .countScan => MachineUnaryAffineAt.scan vertexCount scratch output (d + e)
      (.inr .countScan) (.inr .countRestore)
  | .countRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .countRestore) (next .headerSeed)
  | .headerSeed => MachineUnaryAffineAt.seed output 0 (.inr .headerScan)
  | .headerScan => MachineUnaryAffineAt.scan vertexCount scratch output 1
      (.inr .headerScan) (.inr .headerRestore)
  | .headerRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .headerRestore) (next .fuelSeed)
  | .fuelSeed => MachineUnaryAffineAt.seed fuel 0 (.inr .fuelScan)
  | .fuelScan => MachineUnaryAffineAt.scan vertexCount scratch fuel 1
      (.inr .fuelScan) (.inr .fuelRestore)
  | .fuelRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .fuelRestore) (next .vertexSeed)
  | .vertexSeed => .push vertex (fun _ => false) (.goto fun _ => .inr .guard)
  | .guard => MachineUnaryCounter.guard fuel (.inr (.old (0, none))) (.inr .drainFuel)
  | .old stage => MachineLazyRows.vertexInstruction d hd (d + e) 0 oldTapes
      (fun stage => .inr (.old stage)) (next .tailSeed) stage
  | .tailSeed => MachineUnaryAffineAt.seed tail 0 (.inr .tailScan)
  | .tailScan => MachineUnaryAffineAt.scan vertex scratch tail 1
      (.inr .tailScan) (.inr .tailRestore)
  | .tailRestore => Reduction.MachineTransfer.loopAt scratch vertex id false
      (.inr .tailRestore) (next (.expander (0, none)))
  | .expander stage => MachineStateEquiv.statement (expanderState A d e)
      (MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage)
  | .drainTail => MachineDrain.drain tail (.inr .drainTail) (next .increment)
  | .increment => .push vertex (fun _ => true) (.goto fun _ => .inr .guard)
  | .drainFuel => MachineDrain.drain fuel (.inr .drainFuel) (next .drainVertex)
  | .drainVertex => MachineDrain.drain vertex (.inr .drainVertex) (next .drainVertexCount)
  | .drainVertexCount => MachineDrain.drain vertexCount (.inr .drainVertexCount) (next .drainDartCount)
  | .drainDartCount => MachineDrain.drain dartCount (.inr .drainDartCount) none

def program (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    Label d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State A d e)
  | .inl l => Placement.statement Sum.inl Sum.inl (next .copyHFirst)
      (MachineTableSplit.program l)
  | .inr l => mainInstruction d e hd he l

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

def oldRows {n d : Nat} (G : PortTables.Table n d) (v : Fin n) := List.ofFn (row G v)

def oldBlock {n d : Nat} (G : PortTables.Table n d) (v : Fin n) : List Bool :=
  MachineLazyRows.recordsInput (oldRows G v)

def oldOutput {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) : List Bool :=
  MachineLazyRows.recordsOutput d (d + e) 0 (oldRows G v)
def outputBlock {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) : List Bool := oldOutput G e v ++ expanderOutput d H v

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

theorem graphRows_blocks {n d : Nat} (G : PortTables.Table n d) :
    MachineTableSplit.rowsBits (PortTables.graphTable G) = (List.ofFn (oldBlock G)).flatten := by
  change encodeWords ((PortTables.flatRows G).toList.flatMap rowWords) = _
  rw [PreprocessingLazyWords.flatRows_list, encodeWords_flatten_flatMap_inline_MachineOverlayTable, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (MachineLazyRows.recordsInput_eq_codec (oldRows G v)).symm

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

theorem oldFrame {n m : Nat} (g h gs hs nv mv f v out : List Bool)
    (rows : List (DartRow n m)) :
    MachineLazyRows.streamFrame oldTapes (memory g h gs hs nv mv f v [] []) rows out =
      memory g h (MachineLazyRows.recordsInput rows ++ gs) hs nv mv f v [] out := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [MachineLazyRows.streamFrame, oldTapes, memory, tail, oldReverse, relation,
      scratch, dividedCopy, quotient, newReverse, output, rowBuffer, graphStream]

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

def pairSteps {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (out : List Bool) : Nat :=
  MachineLazyRows.vertexSteps d (d + e) 0 (oldRows G v) out + (2 * (v.val + 1) + 1) +
    MachineOverlayRows.vertexSteps d e v.val (List.ofFn (expanderValues H v))
      (out ++ oldOutput G e v) + (v.val + 3)

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

def outputPrefix {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (k : Nat) : List Bool := encodeWords [n, n * (d + e)] ++ emittedPrefix (outputBlock G H) k

theorem outputPrefix_step {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    outputPrefix G H (v.val + 1) = outputPrefix G H v.val ++ outputBlock G H v := by
  simp only [outputPrefix, prefix_step, List.append_assoc]

def loopBase {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (r : Nat) : Tape → List Bool :=
  memory (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (n - r)) (remaining (expanderBlock H) (n - r))
    (encodeWord n) (encodeWord (n * d)) [] (encodeWord (n - r)) [] (outputPrefix G H (n - r))

def loopCost {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (r : Nat) : Nat :=
  if hr : r < n then
    pairSteps G H ⟨n - (r + 1), by omega⟩ (outputPrefix G H (n - (r + 1)))
  else 0

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

def tableSteps {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) : Nat :=
  MachineTableSplit.exactSteps n (n * d) (MachineTableSplit.rowsBits (PortTables.graphTable G)) +
    preparationSteps n (rawExpander H) + MachineCountedLoop.totalSteps (loopCost G H) n +
    cleanupSteps n (n * d)

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

theorem oldOutput_length_le {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) :
    (oldOutput G e v).length ≤ d * oldSize d e n := by
  have bound := flatMap_length_le_inline_MachineOverlayTable (oldRows G v)
    (fun r => MachineLazyRows.reindexRowBits d (d + e) 0 r.tail.val r.reverseIndex.val r.relation)
    (oldSize d e n) (fun r _ => MachineLazyRows.reindexRowBits_length_le d (d + e) 0 r)
  simpa only [oldOutput, MachineLazyRows.recordsOutput, oldRows, List.length_ofFn] using bound

theorem outputBlock_length_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    (outputBlock G H v).length ≤ blockSize d e n := by
  have hg := oldOutput_length_le G e v
  have hh := expanderOutput_length_le d H v
  simp only [outputBlock, List.length_append, blockSize]
  omega

theorem outputPrefix_length_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (k : Nat) :
    (outputPrefix G H k).length ≤ outputCapacity d e n := by
  have hblocks := flatten_length_le_inline_MachineOverlayTable ((List.ofFn (outputBlock G H)).take k)
    (blockSize d e n) (by
      intro xs hx
      have hm := List.mem_of_mem_take hx
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hm
      exact outputBlock_length_le G H v)
  have hlen : ((List.ofFn (outputBlock G H)).take k).length ≤ n := by
    simp only [List.length_take, List.length_ofFn]
    exact Nat.min_le_right _ _
  have hcap := Nat.mul_le_mul_right (blockSize d e n) hlen
  simp only [outputPrefix, emittedPrefix, List.length_append, encodeWords_length,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, Nat.add_zero, outputCapacity]
  omega

theorem pairSteps_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (out : List Bool)
    (hout : out.length ≤ outputCapacity d e n) : pairSteps G H v out ≤ pairBudget d e n := by
  have hold := MachineLazyRows.vertexSteps_le d (d + e) 0 (oldRows G v) out
  simp only [oldRows, List.length_ofFn] at hold
  have hgsize := oldOutput_length_le G e v
  have hnew := MachineOverlayRows.vertexSteps_le d e v.val (n * e)
    (List.ofFn (expanderValues H v)) (by
      intro j hj
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hj
      exact MachineOverlayRows.expanderValues_bounded H v p) (out ++ oldOutput G e v)
  simp only [List.length_ofFn, List.length_append] at hnew
  have hv := v.isLt.le
  have hsize : MachineOverlayRows.rowSizeBound d e v.val (n * e) ≤ expanderSize d e n := by
    unfold expanderSize MachineOverlayRows.rowSizeBound
    omega
  have hcost : MachineOverlayRows.rowCostBound d e v.val (n * e) ≤
      MachineOverlayRows.rowCostBound d e n (n * e) := by
    unfold MachineOverlayRows.rowCostBound
    change _ ≤ 8 * (n * e) + 4 * expanderSize d e n + _ + _ + 28
    omega
  have hsizeMul := Nat.mul_le_mul_left e hsize
  have holdBudget := Nat.mul_le_mul_left d
    (show MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
        2 * (out.length + d * MachineLazyRows.rowSizeBound (d + e) 0 n (n * d)) + 1 ≤
      MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
        2 * (outputCapacity d e n + d * oldSize d e n) + 1 by

      unfold oldSize
      omega)
  have hnewBudget := Nat.mul_le_mul_left e
    (show MachineOverlayRows.rowCostBound d e v.val (n * e) +
        2 * (out.length + (oldOutput G e v).length + e * MachineOverlayRows.rowSizeBound d e v.val (n * e)) + 1 ≤
      MachineOverlayRows.rowCostBound d e n (n * e) +
        2 * (outputCapacity d e n + d * oldSize d e n + e * expanderSize d e n) + 1 by omega)
  unfold pairSteps pairBudget oldRows
  omega

theorem loopSteps_le {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    MachineCountedLoop.totalSteps (loopCost G H) n ≤ n * (pairBudget d e n + 1) + 1 := by
  apply MachineCountedLoop.totalSteps_le
  intro r hr
  rw [loopCost, dite_eq_left hr]
  exact pairSteps_le G H _ _ (outputPrefix_length_le G H _)

theorem tableSteps_le {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    tableSteps G H ≤ (timePolynomial d e).eval ((PortTables.tableBits G).length + (rawExpander H).length) := by
  have hsplit := MachineTableSplit.exactSteps_le n (n * d)
    (MachineTableSplit.rowsBits (PortTables.graphTable G))
  have header : encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G) =
      PortTables.tableBits G := (MachineTableSplit.tableBits_header_rows (PortTables.graphTable G)).symm
  rw [header, MachineTableSplit.timePolynomial_eval] at hsplit
  have hn := PortTables.vertices_le_tableBits_length G
  have hloop := loopSteps_le G H
  have hmono := natPolynomial_eval_mono (phasePolynomial d e)
    (show n ≤ (PortTables.tableBits G).length + (rawExpander H).length by omega)
  rw [phasePolynomial_eval] at hmono
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  unfold tableSteps preparationSteps
  omega

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

end DFVSGames.Foundations.Complexity.MachineOverlayTable
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePaddedOverlay
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

variable {d : Nat}

abbrev State (d : Nat) := MachineVertexPadding.State (MachineExpanderFamily.State Unit baseDegree × MachineOverlayTable.State Unit d overlayDegree)

def familyStates (d : Nat) :
    (MachineExpanderFamily.State Unit baseDegree × ((MachineOverlayTable.State Unit d overlayDegree × Bool) × Option Bool)) ≃
      State d where
  toFun s := (((s.1, s.2.1.1), s.2.1.2), s.2.2)
  invFun s := (s.1.1.1, ((s.1.1.2, s.1.2), s.2))
  left_inv := by rintro ⟨f, ⟨⟨o, b⟩, r⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨f, o⟩, b⟩, r⟩; rfl

def overlayStates (d : Nat) :
    (MachineOverlayTable.State Unit d overlayDegree × ((MachineExpanderFamily.State Unit baseDegree × Bool) × Option Bool)) ≃
      State d where
  toFun s := (((s.2.1.1, s.1), s.2.1.2), s.2.2)
  invFun s := (s.1.1.2, ((s.1.1.1, s.1.2), s.2))
  left_inv := by rintro ⟨o, ⟨⟨f, b⟩, r⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨f, o⟩, b⟩, r⟩; rfl

def familySource (H : BaseTable) (d : Nat) : MachineExpanderFamily.Label baseDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet (MachineExpanderFamily.Label baseDegree) (State d) :=
  MachineStateEquiv.program (familyStates d) (MachineStateFrame.frameProgram
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H MachineExpanderFamily.baseDegree_cloud_gt_one))

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

def clean (H : BaseTable) (d : Nat) (hd : 0 < d) : State d :=
  (((MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H (),
    MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ()), false), none)

def padded {n d : Nat} (t : PortTables.Table n d) :=
  PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)

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

theorem rotor_familyAt (H : BaseTable) (n : Nat) :
    MachineOverlayTable.rawExpander (PreprocessingStageMaps.familyAt H n) = rotor H n := by
  unfold MachineOverlayTable.rawExpander PreprocessingStageMaps.familyAt rotor
  exact congrArg encodeWords
    (rotationWords_resize (PreprocessingLevels.table_vertexCount_eq_paddedSize n)
      (ExpanderTables.family H (PreprocessingLevels.boundedLevel n)))

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

theorem archive_length_le (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) :
    (PortTables.tableBits (padded t)).length + (rotor H n).length ≤
      (archivePolynomial d).eval (PortTables.tableBits t).length := by
  let m := PreprocessingLevels.paddedSize n
  let s := ExpanderFamily.growth * ((PortTables.tableBits t).length + 1)
  have hm : m ≤ s := MachineVertexPadding.power_length_bound t
  have hmd : m*d ≤ s*d := Nat.mul_le_mul_right d hm
  have hmq : m*overlayDegree ≤ s*overlayDegree := Nat.mul_le_mul_right overlayDegree hm
  have hg := GraphTables.tableBits_length_le (PortTables.graphTable (padded t))
  change (PortTables.tableBits (padded t)).length ≤
    m + m*d + 2 + m*d*(m + m*d + 8192) at hg
  have hg' := hg.trans (Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hm hmd) 2)
    (Nat.mul_le_mul hmd (Nat.add_le_add_right (Nat.add_le_add hm hmd) 8192)))
  have hr := ExpanderTableWords.encode_rotationWords_length_le
    (PreprocessingStageMaps.familyAt H n)
  change (MachineOverlayTable.rawExpander (PreprocessingStageMaps.familyAt H n)).length ≤
    (m*overlayDegree)*(m*overlayDegree+1) at hr
  rw [rotor_familyAt] at hr
  have hr' := hr.trans (Nat.mul_le_mul hmq (Nat.add_le_add_right hmq 1))
  have h := Nat.add_le_add hg' hr'
  simpa only [archivePolynomial, sizePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
    s] using h

noncomputable def familyPolynomial : Polynomial Nat :=
  Polynomial.C MachineExpanderFamilyBounds.inputCoefficient * (Polynomial.X + 1)^5

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachineVertexPadding.timePolynomial d + familyPolynomial +
    (MachineOverlayTable.timePolynomial d overlayDegree).comp (archivePolynomial d)

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

end DFVSGames.Foundations.Complexity.MachinePaddedOverlay
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLazyTable
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

def vertexBlock {n m : Nat} (d v : Nat) (rows : Fin d → GraphTables.DartRow n m) : List Bool :=
  MachineDummyRows.rowsBits v (2 * d * v) d ++
    MachineLazyRows.recordsOutput d (2 * d) d (List.ofFn rows)

def bodySteps {n m : Nat} (d v : Nat) (rows : Fin d → GraphTables.DartRow n m)
    (output : List Bool) : Nat :=
  2 * (v + 2) + (MachineDummyRows.steps v (2 * d * v) output d + 1) + (v + 2) + 8193 +
    MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows)
      (output ++ MachineDummyRows.rowsBits v (2 * d * v) d) + 1

def inputBlocks {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) : List Bool :=
  events.flatMap (fun v => MachineLazyRows.recordsInput (List.ofFn (PreprocessingLazyWords.row table v)))

def outputBlocks {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) : List Bool :=
  events.flatMap (fun v => vertexBlock d v.val (PreprocessingLazyWords.row table v))

theorem vertexBlock_codec {n d : Nat} (table : PortTables.Table n d) (v : Fin n) :
    vertexBlock d v.val (PreprocessingLazyWords.row table v) =
      encodeWords ((PreprocessingLazyWords.vertexRows table v).flatMap GraphTables.rowWords) := by
  rw [vertexBlock, MachineLazyCodec.rowsBits_stay, MachineLazyRows.recordsOutput_lazy,
    PreprocessingLazyWords.vertexRows, List.flatMap_append, encodeWords_append]

theorem inputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    inputBlocks table events = encodeWords
      ((events.flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatMap
        GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap_inline_MachineLazyTable]
  simp only [inputBlocks, MachineLazyRows.recordsInput_eq_codec]

theorem outputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    outputBlocks table events = encodeWords
      ((events.flatMap (PreprocessingLazyWords.vertexRows table)).flatMap GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap_inline_MachineLazyTable]
  simp only [outputBlocks, vertexBlock_codec]

theorem input_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits table = encodeWords [n, n * d] ++ inputBlocks table (List.finRange n) := by
  rw [inputBlocks_codec]
  change encodeWords (PortTables.tableWords table) = _
  rw [PortTables.tableWords_eq, PreprocessingLazyWords.flatRows_list, encodeWords_append]
  have hrows : (List.ofFn (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatten =
      (List.finRange n).flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v)) := by
    rw [List.ofFn_eq_map]
    rfl
  rw [hrows]

theorem output_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits (PreprocessingOverlayTables.lazy table) =
      encodeWords [n, 2 * (n * d)] ++ outputBlocks table (List.finRange n) := by
  rw [outputBlocks_codec, PreprocessingLazyWords.tableBits_lazy, encodeWords_append]
  have hm : n * (2 * d) = 2 * (n * d) := by ac_rfl
  have hrows : (List.ofFn (PreprocessingLazyWords.vertexRows table)).flatten =
      (List.finRange n).flatMap (PreprocessingLazyWords.vertexRows table) := by
    rw [List.ofFn_eq_map]
    rfl
  exact congrArg₂ List.append (congrArg (fun k => encodeWords [n, k]) hm)
    (congrArg (fun rows => encodeWords (rows.flatMap GraphTables.rowWords)) hrows)

def loopSteps {n d : Nat} (table : PortTables.Table n d) (r : Nat) : Nat → List Bool → Nat
  | 0, _ => finishSteps d n (n * d) r
  | count + 1, output => if h : r < n then
      (1 + bodySteps d r (PreprocessingLazyWords.row table ⟨r, h⟩) output) +
        loopSteps table (r + 1) count
          (output ++ vertexBlock d r (PreprocessingLazyWords.row table ⟨r, h⟩))
      else 0

def totalSteps {n d : Nat} (table : PortTables.Table n d) : Nat :=
  prefixSteps n (n * d) (inputBlocks table (List.finRange n)) +
    loopSteps table 0 n (encodeWords [n, 2 * (n * d)])

theorem dummyRows_length_le_inline_MachineLazyTable (v e count : Nat) :
    (MachineDummyRows.rowsBits v e count).length ≤ count * (v + e + count + 8194) := by
  induction count generalizing e with
  | zero => simp [MachineDummyRows.rowsBits]
  | succ count ih =>
    simp only [MachineDummyRows.rowsBits, List.length_append, MachineDummyRows.rowBits_length]
    have h := ih (e + 1)
    have he : v + (e + 1) + count + 8194 = v + e + (count + 1) + 8194 := by omega
    rw [he] at h
    nlinarith only [h]

theorem bodySteps_le {n d : Nat} (rows : Fin d → GraphTables.DartRow n (n * d))
    (v L : Nat) (output : List Bool) (hv : v ≤ n) (hn : n ≤ L) (hm : n * d ≤ L)
    (ho : output.length ≤ 20000 * (L + 1) ^ 2) :
    bodySteps d v rows output ≤ 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2 := by
  let D := d + 1
  let N := L + 1
  let P := D * N
  let Q := P * P
  let S := v + 2 * d * v + d + 8194
  let V := (2 * d) * (n * d) + n * d + d
  let R := n + V + 8194
  let C := 2 * n + 8 * (n * d) + V + 4 * R + 8224
  let dummy := MachineDummyRows.rowsBits v (2 * d * v) d
  let after := output ++ dummy
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hdD : d ≤ D := by dsimp [D]; omega
  have hLN : L ≤ N := by dsimp [N]; omega
  have hDP : D ≤ P := by
    have h := Nat.mul_le_mul_left D hN
    simpa [P] using h
  have hNP : N ≤ P := by
    have h := Nat.mul_le_mul_right N hD
    simpa [P] using h
  have hP : 1 ≤ P := hN.trans hNP
  have hPQ : P ≤ Q := by
    have h := Nat.mul_le_mul_right P hP
    simpa [Q] using h
  have hQ : 1 ≤ Q := hP.trans hPQ
  have hdP : d ≤ P := hdD.trans hDP
  have hvN : v ≤ N := hv.trans (hn.trans hLN)
  have hvP : v ≤ P := hvN.trans hNP
  have hnP : n ≤ P := hn.trans (hLN.trans hNP)
  have hmN : n * d ≤ N := hm.trans hLN
  have hmP : n * d ≤ P := hmN.trans hNP
  have hdv : d * v ≤ P := by simpa [P] using Nat.mul_le_mul hdD hvN
  have hdm : d * (n * d) ≤ P := by simpa [P] using Nat.mul_le_mul hdD hmN
  have hdPQ : d * P ≤ Q := by simpa [Q] using Nat.mul_le_mul_right P hdP
  have hNQ : N ^ 2 ≤ Q := by simpa [pow_two, Q] using Nat.mul_le_mul hNP hNP
  have hS : S ≤ 10000 * P := by
    have hconst := Nat.mul_le_mul_left 8194 hP
    dsimp [S]
    nlinarith only [hvP, hdP, hdv, hconst, hP]
  have hV : V ≤ 4 * P := by
    dsimp [V]
    nlinarith only [hdm, hmP, hdP]
  have hR : R ≤ 10000 * P := by
    have hconst := Nat.mul_le_mul_left 8194 hP
    dsimp [R]
    nlinarith only [hnP, hV, hconst, hP]
  have hC : C ≤ 50000 * P := by
    have hconst := Nat.mul_le_mul_left 8224 hP
    dsimp [C]
    nlinarith only [hnP, hmP, hV, hR, hconst, hP]
  have hSQ : S ≤ 10000 * Q := hS.trans (Nat.mul_le_mul_left 10000 hPQ)
  have hCQ : C ≤ 50000 * Q := hC.trans (Nat.mul_le_mul_left 50000 hPQ)
  have hdSQ : d * S ≤ 10000 * Q := by
    calc
      d * S ≤ d * (10000 * P) := Nat.mul_le_mul_left d hS
      _ = 10000 * (d * P) := by ring
      _ ≤ 10000 * Q := Nat.mul_le_mul_left 10000 hdPQ
  have hdRQ : d * R ≤ 10000 * Q := by
    calc
      d * R ≤ d * (10000 * P) := Nat.mul_le_mul_left d hR
      _ = 10000 * (d * P) := by ring
      _ ≤ 10000 * Q := Nat.mul_le_mul_left 10000 hdPQ
  have hOut : output.length ≤ 20000 * Q := by
    change output.length ≤ 20000 * N ^ 2 at ho
    exact ho.trans (Nat.mul_le_mul_left 20000 hNQ)
  have hDummyLength : dummy.length ≤ 10000 * Q := by
    have h := dummyRows_length_le_inline_MachineLazyTable v (2 * d * v) d
    change dummy.length ≤ d * S at h
    exact h.trans hdSQ
  have hAfter : after.length ≤ 30000 * Q := by
    dsimp [after]
    rw [List.length_append]
    omega
  have hDummyInside : 4 * S + 2 * (output.length + d * S) + 10 ≤ 100010 * Q := by
    have hconst := Nat.mul_le_mul_left 10 hQ
    nlinarith only [hSQ, hOut, hdSQ, hconst]
  have hDummySteps : MachineDummyRows.steps v (2 * d * v) output d ≤ 100010 * d * Q := by
    calc
      MachineDummyRows.steps v (2 * d * v) output d ≤
          d * (4 * S + 2 * (output.length + d * S) + 10) := by
        simpa only [S] using MachineDummyRows.steps_le_bound v (2 * d * v) output d
      _ ≤ d * (100010 * Q) := Nat.mul_le_mul_left d hDummyInside
      _ = 100010 * d * Q := by ring
  have hOldInside : C + 2 * (after.length + d * R) + 1 ≤ 130001 * Q := by
    nlinarith only [hCQ, hAfter, hdRQ, hQ]
  have hOldSteps : MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
      130001 * d * Q + 1 := by
    have h := MachineLazyRows.vertexSteps_le d (2 * d) d (List.ofFn rows) after
    simp only [List.length_ofFn] at h
    change MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
      d * (C + 2 * (after.length + d * R) + 1) + 1 at h
    calc
      MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after ≤
          d * (C + 2 * (after.length + d * R) + 1) + 1 := h
      _ ≤ d * (130001 * Q) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left d hOldInside) 1
      _ = 130001 * d * Q + 1 := by ring
  have hvQ : v ≤ Q := hvP.trans hPQ
  have hOverhead : 3 * v + 8201 ≤ 10000 * Q := by
    have hconst := Nat.mul_le_mul_left 8201 hQ
    nlinarith only [hvQ, hconst, hQ]
  have hBody : bodySteps d v rows output ≤ 230011 * d * Q + 10000 * Q + 1 := by
    change 2 * (v + 2) + (MachineDummyRows.steps v (2 * d * v) output d + 1) +
      (v + 2) + 8193 + MachineLazyRows.vertexSteps d (2 * d) d (List.ofFn rows) after + 1 ≤ _
    nlinarith only [hDummySteps, hOldSteps, hOverhead]
  have hdQQ : d * Q ≤ D * Q := Nat.mul_le_mul_right Q hdD
  have hQQ : Q ≤ D * Q := by simpa using Nat.mul_le_mul_right Q hD
  have hDQ : 1 ≤ D * Q := hQ.trans hQQ
  have hCoarse : bodySteps d v rows output ≤ 300000 * D * Q := by
    nlinarith only [hBody, hdQQ, hQQ, hDQ]
  calc
    bodySteps d v rows output ≤ 300000 * D * Q := hCoarse
    _ ≤ 1000000 * D * Q := by
      have h := Nat.mul_le_mul_right (D * Q) (by norm_num : (300000 : Nat) ≤ 1000000)
      simpa only [Nat.mul_assoc] using h
    _ = 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2 := by dsimp [D, N, P, Q]; ring

theorem loopSteps_le {n d : Nat} (table : PortTables.Table n d) (L count r : Nat)
    (hsum : r + count = n) (hn : n ≤ L) (hm : n * d ≤ L) (output : List Bool)
    (hout : (output ++ outputBlocks table (remaining n r)).length ≤ 20000 * (L + 1) ^ 2) :
    loopSteps table r count output ≤
      count * (1 + 1000000 * (d + 1) ^ 3 * (L + 1) ^ 2) + 5 * L + 11 := by
  induction count generalizing r output with
  | zero =>
    have hr : r = n := by omega
    subst r
    have hdouble : 2 * d * n = 2 * (n * d) := by ac_rfl
    simp only [loopSteps, finishSteps, Nat.zero_mul, Nat.zero_add, hdouble]
    omega
  | succ count ih =>
    have hr : r < n := by omega
    let rows := PreprocessingLazyWords.row table (⟨r, hr⟩ : Fin n)
    have ho : output.length ≤ 20000 * (L + 1) ^ 2 := by
      rw [List.length_append] at hout
      omega
    have hb := bodySteps_le rows r L output hr.le hn hm ho
    have hs : outputBlocks table (remaining n r) =
        vertexBlock d r rows ++ outputBlocks table (remaining n (r + 1)) := by
      rw [remaining_cons n r hr]
      rfl
    have hout' : ((output ++ vertexBlock d r rows) ++
        outputBlocks table (remaining n (r + 1))).length ≤ 20000 * (L + 1) ^ 2 := by
      simpa only [hs, List.append_assoc] using hout
    have ht := ih (r + 1) (by omega) (output ++ vertexBlock d r rows) hout'
    simp only [loopSteps, dite_eq_left hr]
    change (1 + bodySteps d r rows output) +
      loopSteps table (r + 1) count (output ++ vertexBlock d r rows) ≤ _
    nlinarith only [hb, ht]

theorem totalSteps_le {n d : Nat} (table : PortTables.Table n d) :
    totalSteps table ≤ (timePolynomial d).eval (PortTables.tableBits table).length := by
  let L := (PortTables.tableBits table).length
  let N := L + 1
  let C := 1000000 * (d + 1) ^ 3
  have hn : n ≤ L := PortTables.vertices_le_tableBits_length table
  have hm : n * d ≤ L := GraphTables.darts_le_tableBits_length (PortTables.graphTable table)
  have hout : (encodeWords [n, 2 * (n * d)] ++
      outputBlocks table (remaining n 0)).length ≤ 20000 * (L + 1) ^ 2 := by
    rw [remaining_zero, ← output_table_codec]
    exact output_length_le table
  have hl := loopSteps_le table L n 0 (by omega) hn hm _ hout
  have hp : prefixSteps n (n * d) (inputBlocks table (List.finRange n)) ≤ 10 * L + 17 := by
    unfold prefixSteps
    rw [← input_table_codec table]
    change 2 * L + 5 * n + 3 * (n * d) + 17 ≤ _
    omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hnN : n ≤ N := by dsimp [N]; omega
  have hN2 : 1 ≤ N ^ 2 := by nlinarith only [hN]
  have hN3 : N ≤ N ^ 3 := by
    have h := Nat.mul_le_mul_left N hN2
    nlinarith only [h]
  have hc := Nat.mul_le_mul_right (1 + C * N ^ 2) hnN
  change loopSteps table 0 n (encodeWords [n, 2 * (n * d)]) ≤ n * (1 + C * N ^ 2) + 5 * L + 11 at hl
  rw [timePolynomial_eval]
  change totalSteps table ≤ (C + 100) * N ^ 3
  unfold totalSteps
  have hLN : L + 1 = N := rfl
  nlinarith only [hp, hl, hc, hN, hN3, hLN]

end DFVSGames.Foundations.Complexity.MachineLazyTable
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineLogCounter

open Turing

theorem restoreTrace (n : Nat) (output : List Bool) (started : Bool) :
    next^[n + 1] (some (configuration (some 4) ((false, started), none)
      [] (List.replicate n true) output)) =
      some (configuration (some 2) ((false, started), none) (List.replicate n true) [] output) := by
  have run := Reduction.MachineTransfer.transferAt_fromTapes (1 : Fin 3) 0 (by decide)
    id false (4 : Fin 5) (some 2) program rfl
    (rawTapes [] (List.replicate n true) output) (false, started) none
  simp only [rawTapes, List.length_replicate, List.reverse_replicate, List.map_id,
    List.append_nil] at run
  have tapesEq : Reduction.MachineTransfer.tapesAt (1 : Fin 3) 0
      (rawTapes [] (List.replicate n true) output) [] (List.replicate n true) =
      rawTapes (List.replicate n true) [] output := by
    funext k
    fin_cases k <;> rfl
  rw [tapesEq] at run
  exact run

theorem coreTrace (n : Nat) (output : List Bool) (started : Bool) :
    next^[coreTime n] (some (configuration (some 2) ((false, started), none)
      (List.replicate n true) [] output)) =
      some (configuration none initialState [] []
        (List.replicate (increments n started) true ++ output)) := by
  induction n using Nat.strong_induction_on generalizing output started with
  | h n ih =>
    cases n with
    | zero =>
      rw [coreTime_zero]
      cases started with
      | false => exact guardStep_zero output false
      | true => exact guardStep_zero output true
    | succ n =>
      have nonzero : n + 1 ≠ 0 := by omega
      have smaller : (n + 1) / 2 < n + 1 := by omega
      have recursive := ih ((n + 1) / 2) smaller (true :: output) true
      have half := halfTrace (n + 1) 0 (true :: output) false true none
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add,
        List.replicate_zero] at half
      have restore := restoreTrace ((n + 1) / 2) (true :: output) true
      rw [coreTime_positive nonzero]
      rw [show n + 1 + (n + 1) / 2 + 3 + coreTime ((n + 1) / 2) =
        (coreTime ((n + 1) / 2) + ((n + 1) / 2 + 1) + (n + 1 + 1)) + 1 by omega,
        Function.iterate_succ_apply]
      change next^[coreTime ((n + 1) / 2) + ((n + 1) / 2 + 1) + (n + 1 + 1)]
        (machine.step (configuration (some 2) ((false, started), none)
          (List.replicate (n + 1) true) [] output)) = _
      rw [guardStep_positive, Function.iterate_add_apply, half,
        Function.iterate_add_apply, restore, recursive]
      rw [increments_half nonzero started]
      simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]

theorem machineTrace (n : Nat) :
    next^[totalTime n] (some (initList machine (encodeWord n))) =
      some (haltList machine (encodeWord (n.log2 + 1))) := by
  rw [initList_eq, haltList_eq]
  rw [show totalTime n = (coreTime n + (n + 1) + (n + 1)) + 1 by
    unfold totalTime; omega, Function.iterate_succ_apply]
  change next^[coreTime n + (n + 1) + (n + 1)]
    (machine.step (configuration (some 0) initialState (encodeWord n) [] [])) = _
  rw [initialStep, Function.iterate_add_apply, stripTrace]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply]
  dsimp only [initialState]
  rw [restoreTrace n [false] false, coreTrace, increments_false]
  rfl

def outputsInTime (n : Nat) :
    TM2OutputsInTime machine (encodeWord n) (some (encodeWord (n.log2 + 1))) (8 * n + 4) where
  steps := totalTime n
  evals_in_steps := machineTrace n
  steps_le_m := totalTime_bound n

end DFVSGames.Foundations.Complexity.MachineLogCounter

end

section

namespace DFVSGames.Foundations.Complexity.GraphCounterModel

open Turing

def clockInTime (extra : ExtraTape → List Bool) (register : Option Bool) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration extra register (initList MachineLogCounter.machine (encodeWord n)))
      (some (clockConfiguration extra register
        (haltList MachineLogCounter.machine (encodeWord (n.log2 + 1))))) (8 * n + 4) :=
  MachineComposition.liftExecutionInTime _ _ (clockConfiguration extra register)
    (clockStep extra register) (MachineLogCounter.outputsInTime n)

end DFVSGames.Foundations.Complexity.GraphCounterModel

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_GraphCounterFinish
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

theorem clockCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[counter.length + 1]
      (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) =
      some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inl (2 : Fin 3))
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .clockCopy)
    (some (.inr .archiveCopy)) program rfl (frame [] original counter [] [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[counter.length + 1]
    (some ⟨some (.inr .clockCopy), initialState, frame [] original counter [] []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inl (2 : Fin 3))
      (Sum.inr ExtraTape.scratch) (frame [] original counter [] []) []
        ((frame [] original counter [] [] (.inl 2)).reverse.map id ++
          frame [] original counter [] [] (.inr .scratch)) =
      frame [] original [] counter.reverse [] := by
    funext tape
    cases tape with
    | inl i => fin_cases i <;> simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem archiveCopyTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + 1]
      (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) =
      some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩ := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.archive)
    (Sum.inr ExtraTape.scratch) (by decide) id false (.inr .archiveCopy)
    (some (.inr .finalReverse)) program rfl (frame [] original [] counter.reverse [])
    MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[original.length + 1]
    (some ⟨some (.inr .archiveCopy), initialState, frame [] original [] counter.reverse []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.archive)
      (Sum.inr ExtraTape.scratch) (frame [] original [] counter.reverse []) []
        ((frame [] original [] counter.reverse [] (.inr .archive)).reverse.map id ++
          frame [] original [] counter.reverse [] (.inr .scratch)) =
      frame [] [] [] (original.reverse ++ counter.reverse) [] := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  simpa only [update, initialState] using h

theorem reverseTrace (original counter : List Bool) :
    (MachineComposition.advance (TM2.step program))^[original.length + counter.length + 1]
      (some ⟨some (.inr .finalReverse), initialState,
        frame [] [] [] (original.reverse ++ counter.reverse) []⟩) =
      some (haltList machine (counter ++ original)) := by
  have h := (Reduction.MachineTransfer.transferAtInTime (Sum.inr ExtraTape.scratch)
    (Sum.inr ExtraTape.output) (by decide) id false (.inr .finalReverse) none program rfl
    (frame [] [] [] (original.reverse ++ counter.reverse) []) MachineLogCounter.initialState none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
    (original.reverse ++ counter.reverse).length + 1]
    (some ⟨some (.inr .finalReverse), initialState,
      frame [] [] [] (original.reverse ++ counter.reverse) []⟩) = _ at h
  have update : Reduction.MachineTransfer.tapesAt (Sum.inr ExtraTape.scratch)
      (Sum.inr ExtraTape.output) (frame [] [] [] (original.reverse ++ counter.reverse) []) []
        ((frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .scratch)).reverse.map id ++
          frame [] [] [] (original.reverse ++ counter.reverse) [] (.inr .output)) =
      frame [] [] [] [] (counter ++ original) := by
    funext tape
    cases tape with
    | inl i => simp [Reduction.MachineTransfer.tapesAt, frame]
    | inr k => cases k <;> simp [Reduction.MachineTransfer.tapesAt, frame]
  rw [update] at h
  rw [← finish_eq]
  simp only [List.length_append, List.length_reverse, initialState] at h
  exact h

theorem finishTrace (counter rest original : List Bool) :
    (MachineComposition.advance (TM2.step program))^[
        rest.length + 2 * counter.length + 2 * original.length + 4]
      (some (clockConfiguration (extraTapes rest original) none
        (haltList MachineLogCounter.machine counter))) =
      some (haltList machine (counter ++ original)) := by
  rw [start_eq]
  have total := trace_trans_inline_GraphCounterFinish _
    (trace_trans_inline_GraphCounterFinish _ (trace_trans_inline_GraphCounterFinish _ (drainTrace rest original counter)
      (clockCopyTrace original counter)) (archiveCopyTrace original counter))
    (reverseTrace original counter)
  simpa only [show rest.length + 1 + (counter.length + 1) + (original.length + 1) +
      (original.length + counter.length + 1) =
      rest.length + 2 * counter.length + 2 * original.length + 4 by omega] using total

def finishInTime (counter rest original : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (clockConfiguration (extraTapes rest original) none (haltList MachineLogCounter.machine counter))
      (some (haltList machine (counter ++ original)))
      (rest.length + 2 * counter.length + 2 * original.length + 4) where
  steps := rest.length + 2 * counter.length + 2 * original.length + 4
  evals_in_steps := finishTrace counter rest original
  steps_le_m := le_rfl

end DFVSGames.Foundations.Complexity.GraphCounterFinish

namespace DFVSGames.Foundations.Complexity.GraphCounterPrefix

open Turing PCP GraphCounterModel GraphCounterFinish

def rawInTime (n m : Nat) (rest : List Bool) :
    TM2OutputsInTime machine (encodeWords [n, m] ++ rest) (some (rawOutput n m rest))
      (20 * (encodeWords [n, m] ++ rest).length + 30) := by
  let original := encodeWords [n, m] ++ rest
  let start := startInTime n m rest
  let clock := clockInTime (extraTapes rest original) none (n + m)
  let finish := finishInTime (encodeWord ((n + m).log2 + 1)) rest original
  have start' : StateTransition.EvalsToInTime (TM2.step program)
      (initList machine original)
      (some (clockConfiguration (extraTapes rest original) none
        (initList MachineLogCounter.machine (encodeWord (n + m)))))
      (2 * (original.length + 1) + 1 + (n + 1) + (m + 1)) := start
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start' clock
  let total := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first finish
  refine { toEvalsTo := total.toEvalsTo, steps_le_m := ?_ }
  have bound := total.steps_le_m
  have hlog := Nat.log2_le_self (n + m)
  have hlength : original.length = n + m + 2 + rest.length := by
    simp only [original, List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  simp only [encodeWord_length] at bound
  change total.steps ≤ 20 * original.length + 30
  omega

def output (table : GraphTables.Table) : List Bool :=
  encodeWord (count table) ++ GraphTables.tableBits table

def outputsInTime (table : GraphTables.Table) :
    TM2OutputsInTime machine (GraphTables.tableBits table) (some (output table))
      (20 * (GraphTables.tableBits table).length + 30) := by
  have run := rawInTime table.vertices table.darts (rowsBits table)
  simpa only [rawOutput, output, count, tableBits_decomposition] using run

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime GraphTables.tableBits id output where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 20 * Polynomial.X + 30
  outputsFun table := by
    change TM2OutputsInTime machine ((GraphTables.tableBits table).map id)
      (some ((output table).map id))
      ((20 * Polynomial.X + 30 : Polynomial Nat).eval (GraphTables.tableBits table).length)
    have input_eq := @List.map_id (machine.Γ machine.k₀) (GraphTables.tableBits table)
    have output_eq := @List.map_id (machine.Γ machine.k₁) (output table)
    rw [input_eq, output_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    exact outputsInTime table

end DFVSGames.Foundations.Complexity.GraphCounterPrefix

namespace DFVSGames.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

def inputBits (input : Input) : List Bool := GraphTables.tableBits input.val

def countedBits (input : Input) : List Bool := GraphCounterPrefix.output input.val

def words (H : BaseTable) (input : Input) (i : Nat) : List Bool :=
  GraphTables.tableBits (TableIteration.runTables H i input.val)

def count (input : Input) : Nat := GraphCounterPrefix.count input.val

theorem inputBits_le_countedBits (input : Input) : (inputBits input).length ≤ (countedBits input).length := by
  simp only [inputBits, countedBits, GraphCounterPrefix.output, List.length_append]
  omega

theorem size_le_inputBits (input : Input) : size input ≤ (inputBits input).length := by
  have h := GraphTableComplexity.size_add_two_le_bits input.val
  unfold size inputBits
  omega

theorem count_le (input : Input) : count input ≤ (countedBits input).length + 1 :=
  (PCPIterationMachine.rounds_le (size input)).trans
    (Nat.add_le_add_right ((size_le_inputBits input).trans (inputBits_le_countedBits input)) 1)

theorem intermediate_size (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    size (TableIteration.run H i input) ≤ PCPIterationMachine.sizeEnvelope sizeFactor (size input) := by
  apply PCPIterationMachine.semanticSize_bound
    (fun j => size (TableIteration.run H j input)) sizeFactor (size input)
    sizeFactor_positive (Nat.le_succ _) _ i hi
  intro j _
  exact step_size H (TableIteration.run H j input)

theorem intermediate_bits (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    (words H input i).length ≤ lengthPolynomial.eval (countedBits input).length := by
  have hsize := intermediate_size H input i hi
  have hinput := (size_le_inputBits input).trans (inputBits_le_countedBits input)
  have heval := MachineComposition.natPolynomial_eval_mono
    (PCPIterationMachine.sizePolynomial sizeFactor) hinput
  rw [PCPIterationMachine.sizePolynomial_eval, PCPIterationMachine.sizePolynomial_eval] at heval
  have hs := hsize.trans heval
  have htable : (TableIteration.runTables H i input.val).vertices +
      (TableIteration.runTables H i input.val).darts ≤
        PCPIterationMachine.sizeEnvelope sizeFactor (countedBits input).length := by
    rw [← TableIteration.run_val]
    exact hs
  rw [lengthPolynomial, Polynomial.eval_comp, PCPIterationMachine.sizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ htable

end DFVSGames.Foundations.Complexity.GraphIterationBounds

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RawInitialMachineFinish
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

section RelationReader

variable {K Λ σ : Type} {N : Nat}

theorem unaryBits_eq_encodeWords (slots : List (Fin N)) (bits : Buffer N) :
    unaryBits slots bits = encodeWords (slots.map fun i => GraphTables.bitWord (bits i)) := by
  induction slots with
  | nil => rfl
  | cons i slots ih => simpa only [unaryBits, List.flatMap_cons, List.map_cons,
      encodeWords] using congrArg (encodeWord (GraphTables.bitWord (bits i)) ++ ·) ih

variable [DecidableEq K]

theorem stepAux_readUnarySlots (source : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readUnarySlots source slots next) (ambient, buffer)
        (Function.update tapes source (unaryBits slots bits ++ suffix)) =
      TM2.stepAux next (ambient, MachineFixedBlockMap.fill slots bits buffer)
        (Function.update tapes source suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readUnarySlots, unaryBits, MachineFixedBlockMap.fill]
  | cons i slots ih =>
      cases hi : bits i <;>
        simp only [readUnarySlots, unaryBits, List.flatMap_cons, hi,
          GraphTables.bitWord, Bool.false_eq_true, ite_false, ite_true, if_true, encodeWord,
          List.replicate_zero, List.replicate_succ, List.nil_append,
          List.cons_append,
          TM2.stepAux, Function.update_self, List.head?_cons, Option.getD_some,
          List.tail_cons, Function.update_idem, MachineFixedBlockMap.fill,
          List.foldl_cons]
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i false) tapes
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i true) tapes

theorem stepAux_readUnaryAll (source : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.stepAux (readUnarySlots source (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes source suffix) := by
  have h := stepAux_readUnarySlots source (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes source (unaryBits (List.ofFn id) bits ++ suffix) = tapes := by
    simpa only [← hinput] using Function.update_eq_self source tapes
  rw [hin, MachineFixedBlockMap.fill_all] at h
  exact h

end RelationReader

theorem unaryBits_relation (relation : GraphTables.RelationTable) :
    unaryBits (List.ofFn id) (fun i => relation[i]) =
      encodeWords (GraphTables.relationWords relation) := by
  have h : List.ofFn (fun i : Fin 4096 => relation[i]) = relation.toList := by
    change List.ofFn (fun i : Fin 4096 => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  rw [unaryBits_eq_encodeWords]
  unfold GraphTables.relationWords
  rw [← h]
  simp only [List.map_ofFn, Function.comp_def, id_eq]

section AmbientRelation

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_readRelationAt (source : K) (exit : Λ) (ambient : σ)
    (buffer : Buffer 4096) (unitState : Unit) (register : Option Bool)
    (relation : GraphTables.RelationTable) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = encodeWords (GraphTables.relationWords relation) ++ suffix) :
    TM2.stepAux (readRelationAt source exit) (((ambient, buffer), unitState), register) tapes =
      ⟨some exit, (((ambient, fun i => relation[i]), unitState), register),
        Function.update tapes source suffix⟩ := by
  change TM2.stepAux (MachineControl.statement id (readerStateEquiv σ 4096)
    (readUnarySlots source (List.ofFn id) (.goto fun _ => exit)))
    ((readerStateEquiv σ 4096) (((ambient, unitState), register), buffer)) tapes = _
  rw [MachineControl.stepAux_simulation]
  rw [stepAux_readUnaryAll source _ _ (fun i => relation[i]) tapes suffix
    (by simpa only [unaryBits_relation] using hinput)]
  rfl

end AmbientRelation

namespace Program

open PCP.AlphabetTable

def headPhaseInTime (headerPlan rowPlan : Plan) (base : Tape → List Bool)
    (table : GenericGraphTables.Table 64) (e : Fin table.darts)
    (hTable : base .archive = GenericGraphTables.tableBits table)
    (hReverse : base .reverseIndex = encodeWord (Lookup.headIndex table e).val)
    (hHead : base .head = []) (hScratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headTableFirst, ((ambient, ()), none), base⟩
      (some ⟨some .readRelation, ((ambient, ()), none),
        Lookup.headLookupTapes headRoles base table e⟩)
      (Lookup.headTimePolynomial.eval (GenericGraphTables.tableBits table).length) :=
  Lookup.headLookupInTime headRoles headRoles_injective
    .headTableFirst .headTableSecond .headIndexFirst .headIndexSecond
    .headHeaderVertices .headHeaderDarts Label.headLookup (some .readRelation)
    (program headerPlan rowPlan) rfl rfl rfl rfl rfl rfl (fun _ => rfl)
    base table e hTable hReverse hHead hScratch (ambient, ()) none

end Program

end DFVSGames.Foundations.Complexity.FinalCNFMachine
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFHeader
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

def relationInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (relation : GraphTables.RelationTable) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.relationWords relation) ++ rest)
    (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .readRelation, ((ambient, ()), none), base⟩
      (some ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((((), fun i => relation[i]), ()), none), Function.update base .input rest⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program headerPlan plan .readRelation) _ _) = _
    rw [program, stepAux_readRelationAt _ _ _ _ _ _ _ _ _ hinput]
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

noncomputable def rowInTime (headerPlan plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool)
    (hinput : base .input = encodeWords (GraphTables.rowWords table.rows[e]) ++ rest)
    (harchive : base .archive = GraphTables.tableBits table)
    (hn : base .vertices = encodeWord table.vertices)
    (hm : base .darts = encodeWord table.darts)
    (hrow : base .rowIndex = encodeWord e.val)
    (ht : base .tail = []) (hh : base .head = []) (hr : base .reverseIndex = [])
    (hscratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some .startTail, ((ambient, ()), none), base⟩
      (some ⟨some .guard, ((rowRelation table e, ()), none),
        rowResultTapes plan base table e rest⟩)
      (rowTime plan (GraphTables.tableBits table).length) := by
  let parsed := endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
    (rowRest table e rest)
  let ready := preparedTapes base table e rest
  let read := Function.update ready Tape.input rest
  let output := emittedTapes plan base table e rest
  let run₁ := endpointsInTime headerPlan plan base table.rows[e].tail.val
    table.rows[e].reverseIndex.val (rowRest table e rest)
    (by simpa [GraphTables.rowWords, encodeWords, List.append_assoc, rowRest] using hinput) ambient
  have parsed_archive : parsed .archive = GenericGraphTables.tableBits (genericTable table) := by
    simpa [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes] using harchive
  have parsed_reverse : parsed .reverseIndex =
      encodeWord (Lookup.headIndex (genericTable table) e).val := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hr]
  have parsed_head : parsed .head = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hh]
  have parsed_scratch : parsed .scratch = [] := by
    simp [parsed, endpointTapes, Hastad.SourceMachine.fieldTapes, hscratch]
  let run₂ := headPhaseInTime headerPlan plan parsed (genericTable table) e
    parsed_archive parsed_reverse parsed_head parsed_scratch ambient
  let run₃ := relationInTime headerPlan plan ready table.rows[e].relation rest
    (prepared_input base table e rest) ambient
  have read_operands : ∀ i, read (source i) = encodeWord (rowOperands table e i) :=
    prepared_operands base table e rest hn hm hrow ht
  have read_scratch : read .scratch = [] := by
    simp only [read, Function.update_of_ne (show Tape.scratch ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hscratch
  have read_acc : read .accumulator = base .accumulator := by
    simp only [read, Function.update_of_ne (show Tape.accumulator ≠ Tape.input by decide)]
    exact prepared_frame base table e rest .accumulator (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have run₄ : StateTransition.EvalsToInTime (TM2.step (program headerPlan plan))
      ⟨some (.row (Emitter.labelAt plan.length 36864 0 .entry)),
        ((rowRelation table e, ()), none), read⟩
      (some ⟨some .clearTail, ((rowRelation table e, ()), none), output⟩)
      (plan.length * (3 * ((GraphTables.tableBits table).length + 1) + 3) + 1) := by
    simpa only [read_acc, output, emittedTapes, read, ready] using
      emitInTime headerPlan plan read (rowOperands table e) read_operands read_scratch
        (rowRelation table e) (GraphTables.tableBits table).length (rowOperands_bounded table e)
  have output_tail : output .tail = encodeWord table.rows[e].tail.val := by
    simp [output, emittedTapes, prepared_tail, ht]
  have output_head : output .head = encodeWord table.rows[table.rows[e].reverseIndex].tail.val := by
    simp [output, emittedTapes, prepared_head]
  have output_reverse : output .reverseIndex = encodeWord table.rows[e].reverseIndex.val := by
    simp [output, emittedTapes, prepared_reverse, hr]
  have output_row : output .rowIndex = encodeWord e.val := by
    simp only [output, emittedTapes,
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.accumulator by decide),
      Function.update_of_ne (show Tape.rowIndex ≠ Tape.input by decide)]
    exact (prepared_frame base table e rest .rowIndex (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hrow
  let run₅ := finishInTime headerPlan plan output table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val table.rows[e].reverseIndex.val e.val
    output_tail output_head output_reverse output_row (rowRelation table e)
  let r₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let r₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂ run₃
  let r₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃ run₄
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ r₁₂₃₄ run₅
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have hb := run.steps_le_m
  have htbound := rowOperands_bounded table e 2
  have hhbound := rowOperands_bounded table e 3
  have hrbound := table.rows[e].reverseIndex.isLt.le.trans (GraphTables.darts_le_tableBits_length table)
  change table.rows[e].tail.val ≤ _ at htbound
  change table.rows[table.rows[e].reverseIndex].tail.val ≤ _ at hhbound
  simp only [Lookup.headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, genericTable_tableBits] at hb
  unfold rowTime
  omega

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFStream
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

theorem rowInvariant_succ (plan : Plan) (table : GraphTables.Table) (r : Nat)
    (hr : r < table.darts) (base : Tape → List Bool) (invariant : LoopInvariant table r base) :
    LoopInvariant table (r + 1)
      (rowResultTapes plan base table ⟨r, hr⟩
        (inputStream table (remainingEvents table (r + 1)))) := by
  constructor
  · exact rowResult_input _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .archive (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.archive
  · exact (rowResult_frame _ _ _ _ _ .vertices (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.vertices
  · exact (rowResult_frame _ _ _ _ _ .darts (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.darts
  · exact rowResult_index _ _ _ _ _
  · exact rowResult_tail _ _ _ _ _
  · exact rowResult_head _ _ _ _ _
  · exact rowResult_reverse _ _ _ _ _
  · exact (rowResult_frame _ _ _ _ _ .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans invariant.scratch

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end


