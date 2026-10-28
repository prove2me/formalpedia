-- Prove2me | Definitions.Def_OAIQ085D024
-- name    : OAIQ085D024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:39:50.519775+00:00
-- url     : https://prove2.me/theorems/91f30b61-e80c-44dc-8204-d2f515b6ec82
-- title:
--   Definitions bundle OAIQ085D024 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 261 declarations of OpenAI's Lean: 109 definitions, 1 inductive type or structure and 151 theorems. The definitions and types are `OAI.DFVSGames.BinaryInputReduction.computation`, `OAI.DFVSGames.BinaryRenameMachine.computableInPolyTime`, `OAI.DFVSGames.BinaryRenameMachine.outputsInTime`, `OAI.DFVSGames.BinaryRenameMachine.tokenComputation`, `OAI.DFVSGames.BinaryTotalInputMachine.computableInPolyTime`, `OAI.DFVSGames.BinaryTotalInputMachine.outputsInTime`, `OAI.DFVSGames.Decoder.ActualAdviceSampling.sampledAgreement`, `OAI.DFVSGames.Decoder.ActualEvents.targetHit`, `OAI.DFVSGames.Decoder.ActualEvents.unrestricted`, `OAI.DFVSGames.Decoder.ActualGoodRows.adviceMass`, `OAI.DFVSGames.Decoder.ActualProjectedTransfer.slopeVariation`, `OAI.DFVSGames.Decoder.ActualSeedEvents.law`, `OAI.DFVSGames.Decoder.ActualSeedEvents.targetHit`, `OAI.DFVSGames.Decoder.ActualSeedSampling.drawAgreement`, `OAI.DFVSGames.Decoder.ActualSpectral.fiberAcceptance`, `OAI.DFVSGames.Decoder.MatrixGapChoice.InverseParameters`, `OAI.DFVSGames.Decoder.SelectedPolicies.goodPredicate`, `OAI.DFVSGames.Explicit.MachineClone100.computation`, `OAI.DFVSGames.Explicit.MachineClone100Certified.certifiedFunction`, `OAI.DFVSGames.Explicit.MachineClone100Finish.finishInTime`, `OAI.DFVSGames.Explicit.MachineClone100Finish.finishTapes`, `OAI.DFVSGames.Explicit.MachineClone100Run.afterLoopTapes`, `OAI.DFVSGames.Explicit.MachineClone100Run.emptyTapes`, `OAI.DFVSGames.Explicit.MachineClone100Run.guardTapes`, `OAI.DFVSGames.Explicit.MachineClone100Run.inputTapes`, `OAI.DFVSGames.Explicit.MachineClone100Run.runInTime`, `OAI.DFVSGames.Explicit.MachineProductFinish.finishInTime`, `OAI.DFVSGames.Explicit.MachineProductHeaders.alphabetInTime`, `OAI.DFVSGames.Explicit.MachineProductHeaders.inPolynomialTime`, `OAI.DFVSGames.Explicit.MachineProductHeaders.initializeInTime`, `OAI.DFVSGames.Explicit.MachineProductHeaders.powerInTime`, `OAI.DFVSGames.Explicit.MachineProductHeaders.powersInTime`, `OAI.DFVSGames.Explicit.MachineProductHeaders.prepareInTime`, `OAI.DFVSGames.Explicit.MachineProductHeaders.seedBridge`, `OAI.DFVSGames.Explicit.MachineProductHeaders.seedInTime`, `OAI.DFVSGames.Explicit.MachineProductHeadersRead.headersInTime`, `OAI.DFVSGames.Explicit.MachineProductHeadersRead.rawHeadersInTime`, `OAI.DFVSGames.Explicit.MachineProductProgram.machine`, `OAI.DFVSGames.Explicit.MachineProductProgram.program`, `OAI.DFVSGames.Explicit.MachineProductRuntime.compose` and 70 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Encoding_ActualGoodRows`, `DirectedFeedback_Encoding_ProductTarget`, `DirectedFeedback_Encoding_SelectedPolicies`, `DirectedFeedback_Games_ActualAdviceSampling`, `DirectedFeedback_Games_AddressTupleBody`, `DirectedFeedback_Games_AddressTupleLoaded`, `DirectedFeedback_Games_PositiveMultiplier`, `DirectedFeedback_Games_RowErasureSliceUniform`, `DirectedFeedback_Games_UniformReduction`, `DirectedFeedback_Games_VisibleTransfer`, `DirectedFeedback_Machines_AddressMachineInitial`, `DirectedFeedback_Machines_FinalCNFStream`, `DirectedFeedback_Machines_MachineAddressHeaders`, `DirectedFeedback_Machines_MachineBinaryLiteralMachine`, `DirectedFeedback_Machines_MachineBinaryRenameMachine`, `DirectedFeedback_Machines_MachineBinaryTokenMachine`, `DirectedFeedback_Machines_MachineBinaryTotalInputMachine`, `DirectedFeedback_Machines_MachineLazyTable`, `DirectedFeedback_Machines_MachineOutcomeRows`, `DirectedFeedback_Machines_MachineProductFinish`, `DirectedFeedback_Machines_MachineProductProgram`, `DirectedFeedback_Machines_MachineSingleOrbitBridge`, `DirectedFeedback_Machines_MachineSingleOrbitCodec`, `DirectedFeedback_Machines_MachineSubdivisionInit`, `DirectedFeedback_Machines_MachineSubdivisionLoop`, `DirectedFeedback_Machines_MachineSubdivisionRows`, `DirectedFeedback_Machines_MachineTemplateAddress`, `DirectedFeedback_Machines_MachineTuple`, `DirectedFeedback_Machines_OutputSize`, `DirectedFeedback_Machines_RuntimeFinish`, `DirectedFeedback_RankGraph_MachineClone100Finish`.
--
--   **Imports.** It imports the bundles `OAIQ085D018`, `OAIQ085D019` and `OAIQ085D020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ085D029`; the statements `OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction` and `OAI.DFVSGames.Decoder.ActualProjectedTransfer.actual_success_lower`; the proofs of `OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction`, `OAI.DFVSGames.Decoder.ActualProjectedTransfer.actual_success_lower` and `OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ085D018
import Definitions.Def_OAIQ085D019
import Definitions.Def_OAIQ085D020

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeFinish
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

def finishInTime (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (canonical : σ) (labels : Label clearKeys → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ label,
      program (labels label) = statement clearKeys accumulator output canonical labels exit label)
    (base : Tapes K) (outputEmpty : base output = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩)
      (finishCost clearKeys accumulator base) := by
  let cleared := MachineDrainMany.finalTapes clearKeys base
  let afterRegister := MachineDrainMany.finalRegister clearKeys register
  let drain : StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩)
      (MachineDrainMany.steps clearKeys base) := {
    steps := MachineDrainMany.steps clearKeys base
    evals_in_steps := MachineDrainMany.trace clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) program (fun l => atLabels (.inl l)) base ambient register
    steps_le_m := Nat.le_refl _ }
  have acc : cleared accumulator = base accumulator := cleared_frame _ _ _ keepAccumulator
  have out : cleared output = [] := (cleared_frame _ _ _ keepOutput).trans outputEmpty
  let reverse : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩
      (some ⟨some (labels (.inr true)), (ambient, none),
        canonicalTapes output (base accumulator).reverse⟩) ((base accumulator).length + 1) := {
    steps := (base accumulator).length + 1
    evals_in_steps := by
      change (Reduction.MachineTransfer.nextAt output program)^[(base accumulator).length + 1]
        (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩) = _
      have run := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
        accumulator output distinct id false (labels (.inr false))
        (some (labels (.inr true))) program
        (by simpa only [statement] using atLabels (.inr false)) cleared ambient afterRegister
      simpa only [acc, out, List.map_id, List.append_nil,
        cleared, reversed_tapes clearKeys accumulator output distinct covers base] using run
    steps_le_m := Nat.le_refl _ }
  let reset : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr true)), (ambient, none), canonicalTapes output (base accumulator).reverse⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (labels (.inr true))) _ _) = _
      rw [atLabels]
      cases exit <;> rfl
    steps_le_m := Nat.le_refl _ }
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ drain reverse
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first reset
  have hsteps : run.steps = finishCost clearKeys accumulator base := by
    change 1 + ((base accumulator).length + 1 + MachineDrainMany.steps clearKeys base) = _
    unfold finishCost
    omega
  exact {
    steps := finishCost clearKeys accumulator base
    evals_in_steps := by simpa only [hsteps] using run.evals_in_steps
    steps_le_m := Nat.le_refl _ }

open scoped BigOperators


end DFVSGames.Foundations.Hastad.SourceRuntimeFinish


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionRows
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionProgram

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction

def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .initialize_ i 0 =>
      match (initOp i).seed with
      | some offset => MachineUnaryAffineAt.seed (initOp i).destination offset (.initialize_ i 1)
      | none => .goto (fun _ => .initialize_ i 1)
  | .initialize_ i 1 => MachineUnaryAffineAt.scan (initOp i).source .affineScratch
      (initOp i).destination (initOp i).coefficient (.initialize_ i 1) (.initialize_ i 2)
  | .initialize_ i 2 => MachineTransfer.loopAt .affineScratch (initOp i).source
      id false (.initialize_ i 2) (some (initNext i))
  | .emitHeader label => MachineFieldTemplate.instruction (headerTokens q)
      newHeaderField .copyScratch .accumulator Label.emitHeader (some .guard) label
  | .guard => MachineUnaryCounter.guard .remaining .startU .finishStart
  | .startU => SourceMachine.fieldStart .u .readU
  | .readU => SourceMachine.fieldLoop .input .u .readU (some .startV)
  | .startV => SourceMachine.fieldStart .v .readV
  | .readV => SourceMachine.fieldLoop .input .v .readV (some (.readTable 0))
  | .readTable completed =>
      if h : completed.val < q then
        .pop .input (fun state head => (state.1, head))
          (.push .permutationReverse (fun state => state.2.getD false)
            (.branch (fun state => state.2.getD false)
              (.goto fun _ => .readTable completed)
              (.load (fun state => (state.1, none))
                (.goto fun _ => .readTable ⟨completed.val + 1, by omega⟩))))
      else .load (fun state => (state.1, none)) (.goto fun _ => .reverseTable)
  | .reverseTable => MachineTransfer.loopAt .permutationReverse .permutation
      id false .reverseTable (some (rowEntry q))
  | .emitRows label => MachineFieldTemplate.instruction (rowTokens q)
      rowField .copyScratch .accumulator Label.emitRows (some .drainU) label
  | .drainU => MachineDrain.drain .u .drainU (some .drainV)
  | .drainV => MachineDrain.drain .v .drainV (some .drainPermutation)
  | .drainPermutation => MachineDrain.drain .permutation .drainPermutation (some .increment)
  | .increment => .push .middle (fun _ => true)
      (.push .first (fun _ => true) (.push .first (fun _ => true)
        (.push .last (fun _ => true) (.push .last (fun _ => true)
          (.load (fun _ => initialState) (.goto fun _ => .guard))))))
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program q

end DFVSGames.Explicit.MachineSubdivisionProgram


namespace DFVSGames.Explicit.MachineSubdivisionHeaders

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineSubdivisionProgram

theorem initList_eq (q : Nat) (bits : List Bool) :
    initList (machine q) bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1

def headersInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.initialize_ 0 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label q) (.headerRead 0) (some (.headerStart 1))
    (program q) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabetHeader (by decide)
    (.headerStart 1 : Label q) (.headerRead 1) (some (.headerStart 2))
    (program q) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label q) (.headerRead 2) (some (.initialize_ 0 0))
    (program q) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  change StateTransition.EvalsToInTime (TM2.step (program q))
    ⟨some (.headerStart 0), initialState, inputTapes (encodeWords [n, q, Q] ++ body)⟩
    (some ⟨some (.initialize_ 0 0), initialState, resultTapes n q Q body⟩)
    (n + q + Q + 6)
  simpa only [encodeWords, List.nil_append, List.append_assoc]
    using ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program q))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.initialize_ 0 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

end DFVSGames.Explicit.MachineSubdivisionHeaders

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionInit
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionInit

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

theorem operationTrace (q : Nat) (i : Fin 9) (base : Tape → List Bool) (a b : Nat)
    (sourceWord : base (initOp i).source = encodeWord a)
    (scratchEmpty : base .affineScratch = [])
    (destinationWord : base (initOp i).destination = priorWord (initOp i).seed b) :
    (MachineComposition.advance (machine q).step)^[2 * (a + 1) + 1]
      (some ⟨some (.initialize_ i 0), initialState, base⟩) =
      some ⟨some (initNext i), initialState,
        Function.update base (initOp i).destination
          (encodeWord ((initOp i).coefficient * a + (initOp i).seed.getD b))⟩ := by
  cases seedValue : (initOp i).seed with
  | some offset =>
    have run := MachineUnaryAffineAt.seededAffineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient offset
      (.initialize_ i 0 : Label q) (.initialize_ i 1) (.initialize_ i 2)
      (some (initNext i)) (program q)
      (by simp [program, seedValue]) rfl rfl base a []
      (by simpa using sourceWord) scratchEmpty ((), ()) none
    have hd : base (initOp i).destination = [] := by
      simpa [priorWord, seedValue] using destinationWord
    simp only [initialState, hd, List.append_nil, Option.getD_some] at run ⊢
    exact run
  | none =>
    have hd : base (initOp i).destination = encodeWord b := by
      simpa [priorWord, seedValue] using destinationWord
    have frame (word : List Bool) :
        MachineUnaryAffineAt.tapes (initOp i).source Tape.affineScratch
          (initOp i).destination base (encodeWord a ++ []) [] word =
        Function.update base (initOp i).destination word := by
      simp only [List.append_nil]
      rw [← sourceWord, ← scratchEmpty]
      simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes,
        Function.update_eq_self]
    have run := MachineUnaryAffineAt.affineTrace
      (initOp i).source Tape.affineScratch (initOp i).destination
      (source_ne_scratch i) (source_ne_destination i) (scratch_ne_destination i)
      (initOp i).coefficient (.initialize_ i 1 : Label q) (.initialize_ i 2)
      (some (initNext i)) (program q) rfl rfl base a b [] [] ((), ()) none
    rw [frame, frame] at run
    simp only [List.append_nil, ← hd, Function.update_eq_self] at run
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (machine q).step)^[2 * (a + 1)]
      (some (TM2.stepAux (program q (.initialize_ i 0)) initialState base)) = _
    simp only [program, seedValue, TM2.stepAux]
    simp only [initialState, Option.getD_none] at run ⊢
    exact run

def prefixInTime (q n Q : Nat) (body : List Bool) (r : Nat) (hr : r ≤ 9) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize_ 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (atStage q r), initialState, frame n q Q body r⟩)
      (r * stageCost n Q) := by
  induction r with
  | zero =>
    refine { steps := 0, evals_in_steps := ?_, steps_le_m := ?_ }
    · simp [atStage, frame]
    · simp
  | succ r ih =>
    have hlt : r < 9 := by omega
    let i : Fin 9 := ⟨r, hlt⟩
    have before := ih (by omega)
    have opTrace := operationTrace q i (frame n q Q body r)
      (sourceValue n Q i) (beforeValue n i)
      (frame_source n q Q body i) (frame_scratch n q Q body i)
      (frame_destination n q Q body i)
    have op : StateTransition.EvalsToInTime (machine q).step
        ⟨some (atStage q r), initialState, frame n q Q body r⟩
        (some ⟨some (atStage q (r + 1)), initialState, frame n q Q body (r + 1)⟩)
        (stageCost n Q) := {
      steps := 2 * (sourceValue n Q i + 1) + 1
      evals_in_steps := by
        change (MachineComposition.advance (TM2.step (program q)))^[_] _ = _
        simp only [atStage, hlt, ↓reduceDIte, i, initNext_eq_atStage, frame, afterValue]
          at opTrace ⊢
        exact opTrace
      steps_le_m := by
        have bound := sourceValue_le n Q i
        dsimp [stageCost]
        omega }
    have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ before op
    exact {
      toEvalsTo := joined.toEvalsTo
      steps_le_m := by
        calc
          joined.steps ≤ stageCost n Q + r * stageCost n Q := joined.steps_le_m
          _ = (r + 1) * stageCost n Q := by
            rw [Nat.add_mul, Nat.one_mul]
            omega
    }

def initializeInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.initialize_ 0 0), initialState, MachineSubdivisionHeaders.resultTapes n q Q body⟩
      (some ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, resultTapes n q Q body⟩)
      (9 * stageCost n Q) := by
  simpa only [atStage, show ¬ (9 < 9) by omega, ↓reduceDIte, final_frame]
    using prefixInTime q n Q body 9 (by omega)

end DFVSGames.Explicit.MachineSubdivisionInit


namespace DFVSGames.Explicit.MachineSubdivisionEmission

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

def headerInTime (q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)),
        initialState, MachineSubdivisionInit.resultTapes n q Q body⟩
      (some ⟨some .guard, initialState, resultTapes n q Q body⟩)
      (3 * (n + 7 * Q + 2) + 10) := by
  have run := MachineFieldTemplate.phaseInTime (headerTokens q) newHeaderField
    Tape.copyScratch Tape.accumulator
    (by intro j; fin_cases j <;> decide) (by intro j; fin_cases j <;> decide) (by decide)
    (Label.emitHeader : MachineFieldTemplate.Label (headerTokens q).length → Label q)
    (some .guard) (program q) (fun _ => rfl)
    (MachineSubdivisionInit.resultTapes n q Q body) rfl initialState
  rw [header_template, header_copiedLength, header_result] at run
  simp only [MachineFieldTemplate.reset, initialState,
    headerTokens, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
    at run ⊢
  exact run

end DFVSGames.Explicit.MachineSubdivisionEmission


namespace DFVSGames.Explicit.MachineSubdivisionTableRead

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

theorem step_true (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (true :: input) reversed⟩ =
      some ⟨some (.readTable completed), (ambient, some true),
        tapes base input (true :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input_inline_MachineSubdivisionTableRead, update_reverse_inline_MachineSubdivisionTableRead]

theorem step_false (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (false :: input) reversed⟩ =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input (false :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input_inline_MachineSubdivisionTableRead, update_reverse_inline_MachineSubdivisionTableRead]

theorem readWordTrace (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (value : Nat) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[value + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWord value ++ input) reversed⟩) =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input ((encodeWord value).reverse ++ reversed)⟩ := by
  induction value generalizing reversed register with
  | zero =>
    simpa [encodeWord, MachineComposition.advance] using
      step_false q completed valid base input reversed ambient register
  | succ value ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append,
      MachineComposition.advance_some]
    rw [step_true q completed valid]
    have h := ih (true :: reversed) (some true)
    simpa only [encodeWord, List.reverse_cons, List.reverse_append,
      List.append_assoc, List.singleton_append] using h

theorem readWordsTrace (q : Nat) (words : List Nat) (completed : Fin (q + 1))
    (complete : completed.val + words.length = q) (base : Tape → List Bool)
    (suffix reversed : List Bool) (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWords words ++ suffix) reversed⟩) =
      some ⟨some .reverseTable, (ambient, none),
        tapes base suffix ((encodeWords words).reverse ++ reversed)⟩ := by
  induction words generalizing completed reversed register with
  | nil =>
    have hc : ¬ completed.val < q := by simpa using complete.ge
    simp [encodeWords, MachineComposition.advance, TM2.step, program, hc, TM2.stepAux]
  | cons value words ih =>
    have valid : completed.val < q := by simp only [List.length_cons] at complete; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at complete
      dsimp [next]
      omega
    have first := readWordTrace q completed valid base value (encodeWords words ++ suffix)
      reversed ambient register
    have second := ih next hn ((encodeWord value).reverse ++ reversed) none
    rw [encodeWords, List.length_append, encodeWord_length,
      show value + 1 + (encodeWords words).length + 1 =
        ((encodeWords words).length + 1) + (value + 1) by omega,
      Function.iterate_add_apply]
    simp only [List.append_assoc]
    rw [first]
    simpa only [next, List.reverse_append, List.append_assoc] using second

theorem tableTrace (q : Nat) (words : List Nat) (length : words.length = q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[2 * (encodeWords words).length + 2]
      (some ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords words ++ suffix) []⟩) =
      some ⟨some (rowEntry q), (ambient, none), finalTapes base suffix (encodeWords words)⟩ := by
  have read := readWordsTrace q words 0 (by simpa using length) base suffix [] ambient register
  simp only [List.append_nil] at read
  have reverse := MachineTransfer.transferAt_fromTapes
    Tape.permutationReverse Tape.permutation (by decide) id false
    Label.reverseTable (some (rowEntry q)) (program q) rfl
    (tapes base suffix (encodeWords words).reverse) ambient none
  have finish : MachineTransfer.tapesAt Tape.permutationReverse Tape.permutation
      (tapes base suffix (encodeWords words).reverse) []
      (((tapes base suffix (encodeWords words).reverse) .permutationReverse).reverse.map id ++
        (tapes base suffix (encodeWords words).reverse) .permutation) =
      finalTapes base suffix (encodeWords words) := by
    funext k
    cases k <;> simp [MachineTransfer.tapesAt, tapes, finalTapes]
  rw [finish] at reverse
  simp only [tapes_reverse, List.length_reverse] at reverse
  rw [show 2 * (encodeWords words).length + 2 =
      ((encodeWords words).length + 1) + ((encodeWords words).length + 1) by omega,
    Function.iterate_add_apply, read]
  exact reverse

def tableInTime {q : Nat} (table : Target.PermutationTable q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords (tableWords table) ++ suffix) []⟩
      (some ⟨some (rowEntry q), (ambient, none),
        finalTapes base suffix (encodeWords (tableWords table))⟩)
      (2 * (q * (q + 1)) + 2) where
  steps := 2 * (encodeWords (tableWords table)).length + 2
  evals_in_steps := tableTrace q (tableWords table) (tableWords_length table)
    base suffix ambient register
  steps_le_m := by
    have h := GameEncodingSize.tableBits_length_le table
    omega

end DFVSGames.Explicit.MachineSubdivisionTableRead


namespace DFVSGames.Explicit.MachineSubdivisionBody

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction
open MachineSubdivisionProgram

def incrementInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .increment, initialState, base⟩
      (some ⟨some .guard, initialState, incrementTapes base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .increment) initialState base) = _
    simp [program, TM2.stepAux, incrementTapes, initialState]
  steps_le_m := Nat.le_refl _

def bodyInTime {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .startU, initialState, base⟩
      (some ⟨some .guard, initialState, bodyResult base u v table suffix⟩)
      (bodyBudget base u v table suffix) := by
  have hu : base .input = encodeWord u ++ (encodeWord v ++ tableBits table ++ suffix) := by
    simpa only [List.append_assoc] using ready.input
  let p₀ := SourceMachine.fieldInTime Tape.input Tape.u (by decide)
    Label.startU Label.readU (some .startV) (program q) rfl rfl base u
    (encodeWord v ++ tableBits table ++ suffix) hu ((), ()) none
  have hv : afterU base u v table suffix .input =
      encodeWord v ++ (tableBits table ++ suffix) := by
    simp [afterU, SourceMachine.afterField, SourceMachine.fieldTapes, List.append_assoc]
  let p₁ := SourceMachine.fieldInTime Tape.input Tape.v (by decide)
    Label.startV Label.readV (some (.readTable 0)) (program q) rfl rfl
    (afterU base u v table suffix) v (tableBits table ++ suffix) hv ((), ()) none
  have tableStart : MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
      (tableBits table ++ suffix) [] = afterV base u v table suffix := by
    funext k
    cases k <;> simp [MachineSubdivisionTableRead.tapes, afterV, afterU,
      SourceMachine.afterField, SourceMachine.fieldTapes, ready.reverseEmpty]
  have p₂ : StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), initialState, afterV base u v table suffix⟩
      (some ⟨some (rowEntry q), initialState, afterTable base u v table suffix⟩)
      (2 * (q * (q + 1)) + 2) := by
    have h := MachineSubdivisionTableRead.tableInTime table
      (afterV base u v table suffix) suffix ((), ()) none
    change StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨_, _, MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
        (tableBits table ++ suffix) []⟩ _ _ at h
    rw [tableStart] at h
    exact h
  have scratch : afterTable base u v table suffix .copyScratch = [] := by
    simp [afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
      afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, ready.scratchEmpty]
  let p₃ := MachineFieldTemplate.phaseInTime (rowTokens q) rowField
    Tape.copyScratch Tape.accumulator rowField_ne_scratch_inline_MachineSubdivisionBody rowField_ne_accumulator_inline_MachineSubdivisionBody (by decide)
    Label.emitRows (some .drainU) (program q) (fun _ => rfl)
    (afterTable base u v table suffix) scratch initialState
  let p₄ := MachineDrain.drainInTime Tape.u Label.drainU (some .drainV)
    (program q) rfl (afterRows base u v table suffix) ((), ()) none
  let p₅ := MachineDrain.drainInTime Tape.v Label.drainV (some .drainPermutation)
    (program q) rfl (afterDrainU base u v table suffix) ((), ()) none
  let p₆ := MachineDrain.drainInTime Tape.permutation Label.drainPermutation (some .increment)
    (program q) rfl (afterDrainV base u v table suffix) ((), ()) none
  let p₇ := incrementInTime q (afterDrainTable base u v table suffix)
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅
  let p₀₁₂₃₄₅₆ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆
  let full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅₆ p₇
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      have h := full.steps_le_m
      have tokens_length : (rowTokens q).length = 12 := rfl
      unfold bodyBudget
      omega
  }

end DFVSGames.Explicit.MachineSubdivisionBody


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionLoop
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionFinish

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineSubdivisionProgram

noncomputable def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

theorem haltList_eq (q : Nat) (bits : List Bool) :
    haltList (machine q) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes, Function.update]
  rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .finishStart) initialState base) = _
    simp only [program, TM2.stepAux]
    rfl
  steps_le_m := Nat.le_refl _

noncomputable def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (q := q)) none (program q) (fun _ => rfl)
    base outputEmpty ((), ()) none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q)
    input (prefixTime + 1) prefixRun clearKeys Tape.accumulator Tape.output
    accumulator_not_mem_clearKeys output_not_mem_clearKeys covers base outputEmpty
    (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end DFVSGames.Explicit.MachineSubdivisionFinish


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ProductTarget
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionRuntime

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame
open MachineSubdivisionCorrespondence

noncomputable section

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSubdivisionFinish.timePolynomial q (prefixPolynomial q)

end
end DFVSGames.Explicit.MachineSubdivisionRuntime


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductProgram
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineProductProgram

open Turing
open DFVSGames.Foundations
open Complexity Hastad
open DFVSGames.Reduction.MachineTransfer

noncomputable section

def program (q t : Nat) : Label q t → TM2.Stmt (fun _ : Tape t => Bool) (Label q t) State
  | .headerStart i => SourceMachine.fieldStart (headerDestination t i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .formula (headerDestination t i)
      (.headerRead i) (some (headerNext q t i))
  | .seedStart => exitAt .formula (MachineProductSeed.entry (seedCommands t) Label.seed
      (some (.power false (.inl .start))))
  | .seed inner => MachineProductSeed.instruction (seedCommands t) Label.seed
      (some (.power false (.inl .start))) inner
  | .power false inner => MachineProductPower.instruction (powerSlots t false) (accumulator t)
      (Label.power false) (some .alphabetHeader) inner
  | .power true inner => MachineProductPower.instruction (powerSlots t true) (accumulator t)
      (Label.power true) (some (MachineOdometerInit.labelAt Label.initialize_ 0)) inner
  | .alphabetHeader => DFVSGames.Reduction.MachineSubstitution.pushWord (accumulator t)
      (encodeWord (q ^ t)) (.goto fun _ => .power true (.inl .start))
  | .initialize_ inner => MachineOdometerInit.statement (initRole t) Label.initialize_
      (some (rowMain q t)) inner
  | .row inner => MachineProductRow.instruction (rowSlots t) (q + 2)
      (ProductMachineSemantics.commands q t) Label.row (some (nextCheck q t 0)) inner
  | .check i => MachineTupleOdometer.increment (.current i) (.remaining i)
      (rowMain q t) (.reset i)
  | .reset i => MachineTupleOdometer.reset (.current i) (.remaining i)
      (.reset i) (nextCheck q t (i.val + 1))
  | .finishStart => exitAt .formula (SourceRuntimeFinish.entry (clearKeys t) Label.finish)
  | .finish inner => SourceRuntimeFinish.statement (clearKeys t) (accumulator t) (output t)
      ((), ()) Label.finish none inner

def machine (q t : Nat) : FinTM2 where
  K := Tape t
  k₀ := .formula
  k₁ := output t
  Γ _ := Bool
  Λ := Label q t
  main := .headerStart 0
  σ := State
  initialState := (((), ()), none)
  m := program q t

end

end DFVSGames.Explicit.MachineProductProgram


namespace DFVSGames.Explicit.MachineProductHeadersRead

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineProductProgram

noncomputable section

theorem initList_eq (q t : Nat) (bits : List Bool) :
    initList (machine q t) bits =
      ⟨some (.headerStart 0), (((), ()), none), inputTapes t bits⟩ := by
  unfold initList
  congr 1
  funext k
  cases k <;> simp [inputTapes, machine]
  rfl

def rawHeadersInTime (q t n m : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (encodeWords [n, q, m] ++ body))
      (some ⟨some .seedStart, (((), ()), none), rawResultTapes t n q m body⟩)
      (n + q + m + 6) := by
  have first := SourceMachine.fieldInTime
    (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 0) (by simp [auxiliary])
    (.headerStart 0 : Label q t) (.headerRead 0) (some (.headerStart 1))
    (program q t) rfl rfl
    (inputTapes t (encodeWord n ++ (encodeWord q ++ (encodeWord m ++ body)))) n
    (encodeWord q ++ (encodeWord m ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime
    (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 7) (by simp [auxiliary])
    (.headerStart 1 : Label q t) (.headerRead 1) (some (.headerStart 2))
    (program q t) rfl rfl (afterVertices t n (encodeWord q ++ (encodeWord m ++ body))) q
    (encodeWord m ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime
    (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 8) (by simp [auxiliary])
    (.headerStart 2 : Label q t) (.headerRead 2) (some .seedStart)
    (program q t) rfl rfl (afterAlphabet t n q (encodeWord m ++ body)) m body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  have timed : StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some (.headerStart 0), (((), ()), none),
        inputTapes t (encodeWord n ++ (encodeWord q ++ (encodeWord m ++ body)))⟩
      (some ⟨some .seedStart, (((), ()), none), rawResultTapes t n q m body⟩)
      (n + q + m + 6) := {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have bound := whole.steps_le_m; omega
  }
  convert timed using 1
  all_goals try with_reducible_and_instances rfl
  simp only [FinTM2.step, FinTM2.Cfg, machine, encodeWords,
    List.nil_append, List.append_assoc]
  rfl

def headersInTime {q : Nat} (H : Target.Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some ⟨some .seedStart, (((), ()), none), resultTapes H t⟩)
      (H.vertices + q + H.constraints.length + 6) := by
  have input : gameBits H = encodeWords [H.vertices, q, H.constraints.length] ++
      encodeWords (ProductMachineSemantics.inputTable H) := by
    simp only [gameBits, gameWords, ProductMachineSemantics.inputTable, encodeWords_append]
  have result : rawResultTapes t H.vertices q H.constraints.length
      (encodeWords (ProductMachineSemantics.inputTable H)) = resultTapes H t := rfl
  rw [input]
  simpa only [result] using rawHeadersInTime q t H.vertices H.constraints.length
    (encodeWords (ProductMachineSemantics.inputTable H))

end
end DFVSGames.Explicit.MachineProductHeadersRead


namespace DFVSGames.Explicit.MachineProductHeaders

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def seedBridge {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some .seedStart, (((), ()), none), MachineProductHeadersRead.resultTapes H t⟩
      (some ⟨MachineProductSeed.entry (seedCommands t) Label.seed
        (some (.power false (.inl .start))), (((), ()), none),
        MachineProductHeadersRead.resultTapes H t⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q t .seedStart) _ _) =
      some (⟨MachineProductSeed.entry (seedCommands t) Label.seed
        (some (.power false (.inl .start))), (((), ()), none),
        MachineProductHeadersRead.resultTapes H t⟩ : TM2.Cfg (fun _ : Tape t => Bool) (Label q t) State)
    simp only [program]
    cases MachineProductSeed.entry (seedCommands t) (Label.seed (q := q))
      (some (.power false (.inl .start))) <;> rfl
  steps_le_m := Nat.le_refl _

def seedInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some .seedStart, (((), ()), none), MachineProductHeadersRead.resultTapes H t⟩
      (some ⟨some (.power false (.inl .start)), (((), ()), none), frame H t []⟩)
      (t + 2) := by
  have trace := MachineProductSeed.seedTrace (seedCommands t) (Label.seed (q := q))
    (some (.power false (.inl .start))) (program q t) (fun _ => rfl)
    (MachineProductHeadersRead.resultTapes H t) ((), ()) none
  rw [seed_result] at trace
  have seed : StateTransition.EvalsToInTime (machine q t).step
      ⟨MachineProductSeed.entry (seedCommands t) Label.seed
        (some (.power false (.inl .start))), (((), ()), none),
        MachineProductHeadersRead.resultTapes H t⟩
      (some ⟨some (.power false (.inl .start)), (((), ()), none), frame H t []⟩)
      (t + 1) := {
    steps := (seedCommands t).length
    evals_in_steps := trace
    steps_le_m := by simp [seedCommands] }
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ (seedBridge H t) seed
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have h := whole.steps_le_m; omega }

end
end DFVSGames.Explicit.MachineProductHeaders


namespace DFVSGames.Explicit.MachineProductHeaders

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def powerInTime {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) (edgeCount : Bool) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some (.power edgeCount (.inl .start)), (((), ()), none), frame H t emitted⟩
      (some ⟨some (powerExit q t edgeCount), (((), ()), none),
        frame H t (emitted ++ encodeWord
          ((if edgeCount then H.constraints.length else H.vertices) ^ t))⟩)
      (MachineProductPower.steps (if edgeCount then H.constraints.length else H.vertices) t) := by
  have trace := MachineProductPower.powerTrace (powerSlots t edgeCount) (accumulator t)
    (power_outside t edgeCount) (Label.power edgeCount) (some (powerExit q t edgeCount))
    (program q t) (by intro inner; cases edgeCount <;> rfl) (frame H t emitted)
    (if edgeCount then H.constraints.length else H.vertices)
    (frame_radix H t emitted edgeCount) (frame_digit H t emitted edgeCount)
    (frame_power_clean H t emitted edgeCount) (frame_power_output H t emitted edgeCount) () none
  rw [frame_append] at trace
  exact { steps := _, evals_in_steps := trace, steps_le_m := Nat.le_refl _ }

def alphabetInTime {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some .alphabetHeader, (((), ()), none), frame H t emitted⟩
      (some ⟨some (.power true (.inl .start)), (((), ()), none),
        frame H t (emitted ++ encodeWord (q ^ t))⟩) 1 := by
  have trace := MachineInitialHeaders.literalTrace (accumulator t) (encodeWord (q ^ t))
    (.alphabetHeader : Label q t) (some (.power true (.inl .start)))
    (program q t) rfl (frame H t emitted) ((), ()) none
  rw [frame_append] at trace
  exact { steps := 1, evals_in_steps := trace, steps_le_m := Nat.le_refl _ }

def powersInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some (.power false (.inl .start)), (((), ()), none), frame H t []⟩
      (some ⟨some (MachineOdometerInit.labelAt Label.initialize_ 0), (((), ()), none), baseTapes H t⟩)
      (MachineProductPower.steps H.vertices t + 1 + MachineProductPower.steps H.constraints.length t) := by
  have first := powerInTime H t [] false
  have second := alphabetInTime H t (encodeWord (H.vertices ^ t))
  have third := powerInTime H t (encodeWord (H.vertices ^ t) ++ encodeWord (q ^ t)) true
  simp only [Bool.false_eq_true, ↓reduceIte, powerExit, List.nil_append] at first
  simp only [↓reduceIte, powerExit] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  have finalFrame : frame H t
      ((encodeWord (H.vertices ^ t) ++ encodeWord (q ^ t)) ++
        encodeWord (H.constraints.length ^ t)) = baseTapes H t := by
    simp only [baseTapes, headerBits, encodeWords, List.append_nil, List.append_assoc]
  rw [finalFrame] at whole
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have h := whole.steps_le_m; omega }

end
end DFVSGames.Explicit.MachineProductHeaders


namespace DFVSGames.Explicit.MachineProductHeaders

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def initializeInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      ⟨some (MachineOdometerInit.labelAt Label.initialize_ 0), (((), ()), none), baseTapes H t⟩
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t)))
      (t * (2 * H.constraints.length + 6) + 1) := by
  have run := MachineOdometerInit.initializeInTime (initRole t) (initRole_injective t)
    Label.initialize_ (some (rowMain q t)) (program q t) (fun _ => rfl)
    H.constraints.length H.constraintCount_positive (baseTapes H t)
    (by simp [baseTapes, frame, initRole, auxiliary])
    (by intro j; rfl) (by intro j; rfl) rfl ((), ())
  rw [initialized_eq] at run
  exact run

def prepareInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t))) (steps H t) := by
  have headers := MachineProductHeadersRead.headersInTime H t
  have seeds := seedInTime H t
  have powers := powersInTime H t
  have initialized := initializeInTime H t
  have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ headers seeds
  have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first powers
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second initialized
  exact {
    toEvalsTo := whole.toEvalsTo
    steps_le_m := by have h := whole.steps_le_m; unfold steps; omega }

def inPolynomialTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t)))
      ((timePolynomial t).eval (gameBits H).length) :=
  { toEvalsTo := (prepareInTime H t).toEvalsTo
    steps_le_m := (prepareInTime H t).steps_le_m.trans (steps_le H t) }

end
end DFVSGames.Explicit.MachineProductHeaders


namespace DFVSGames.Explicit.MachineProductLoop

open Turing
open DFVSGames.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram

variable {q t : Nat}

noncomputable section

theorem bodyTrace (H : Target.Instance q) (base : Tape t → List Bool) (ready : BaseReady H base) :
    SourceOdometerSchedule.BodyTrace (program q t) (rowMain q t) (nextCheck q t 0)
      ((), ()) (Sum.inl (6 : Fin 10)) base (rowBits (t := t) H) (bodyBound H t) := by
  intro edges out
  let indices := fun i => (edges i).val
  let radices := fun b : Bool => if b then q else H.vertices
  let fields := ProductMachineSemantics.fields H edges
  let digits := fun c => ProductMachineSemantics.reverseDigits (fields c)
  let frame := tupleTapes H base edges out
  have hready := tupleTapes_ready H base ready edges out
  have selected := ProductMachineSemantics.selected H edges
  have reversed : ∀ c ∈ ProductMachineSemantics.commands q t, ∀ i : Fin t,
      digits c i.val = fields c i.rev := by
    intro c hc i
    exact ProductMachineSemantics.reverseDigits_at _ _
  have run := MachineProductRow.rowTrace (rowSlots t) (ProductMachineSemantics.inputTable H)
    (q + 2) indices radices (ProductMachineSemantics.commands q t) fields digits selected reversed
    Label.row (some (nextCheck q t 0)) (program q t) (fun _ => rfl) frame hready ()
  have len := input_length H
  have tableBound : (encodeWords (ProductMachineSemantics.inputTable H)).length ≤ (gameBits H).length := by omega
  have indexBound (i : Fin t) : indices i ≤ (gameBits H).length := by
    have h := (edges i).isLt; dsimp [indices]; omega
  have radixBound (b : Bool) : radices b ≤ (gameBits H).length := by
    cases b <;> dsimp [radices] <;> omega
  have digitBound (c : MachineProductRow.Command t) (hc : c ∈ ProductMachineSemantics.commands q t)
      (i : Nat) (hi : i < t) : digits c i ≤ (gameBits H).length := by
    rw [show digits c i = fields c (Fin.rev ⟨i, hi⟩) from
      ProductMachineSemantics.reverseDigits_at _ ⟨i, hi⟩]
    have h := ProductMachineSemantics.fields_lt H edges c hc (Fin.rev ⟨i, hi⟩)
    have hr := radixBound c.1
    dsimp [radices, fields] at hr ⊢
    omega
  have bound := MachineProductBounds.row_steps_le (rowSlots t) (ProductMachineSemantics.inputTable H)
    (q + 2) indices radices (ProductMachineSemantics.commands q t) fields digits selected
    frame hready (gameBits H).length tableBound indexBound radixBound digitBound
  rw [ProductMachineSemantics.commands_length] at bound
  refine ⟨_, bound, ?_⟩
  have hframe : Function.update frame (MachineProductRow.outputTape (rowSlots t))
      ((rowBits H edges).reverse ++ frame (MachineProductRow.outputTape (rowSlots t))) =
      tupleTapes H base edges ((rowBits H edges).reverse ++ out) := by
    change Function.update frame (accumulator t)
      ((rowBits H edges).reverse ++ frame (accumulator t)) = _
    rw [show frame (accumulator t) = out from tupleTapes_accumulator H base edges out]
    simp only [frame, tupleTapes, SourceOdometerSchedule.setDigits_setAcc]
    simp [SourceOdometerSchedule.setAcc, accumulator, auxiliary]
  dsimp only at run
  change _ = some (⟨some (nextCheck q t 0), (((), ()), none),
    Function.update frame (MachineProductRow.outputTape (rowSlots t))
      ((rowBits H edges).reverse ++ frame (MachineProductRow.outputTape (rowSlots t)))⟩ :
      TM2.Cfg (fun _ : Tape t => Bool) (Label q t) State) at run
  rw [hframe] at run
  exact run

theorem traversalInTime (H : Target.Instance q) (base : Tape t → List Bool) (ready : BaseReady H base) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (program q t))
      (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length) t (rowMain q t) ((), ()) base)
      (some (SourceOdometerSchedule.finalConfiguration (nextCheck q t t) ((), ())
        (Sum.inl (6 : Fin 10)) base (rowBits (t := t) H)))
      ((bodyBound H t + 2 * t) * H.constraints.length ^ t)) := by
  apply SourceOdometerSchedule.traversalInTime (program q t) (rowMain q t)
    (nextCheck q t) (resetAt q t) ((), ()) (Sum.inl (6 : Fin 10))
    (List.length_pos_iff.mpr H.nonempty) (bodyBound H t) base (rowBits (t := t) H)
  · intro i hi
    simp [nextCheck, resetAt, hi, program, SourceOdometerSchedule.currentAt,
      SourceOdometerSchedule.remainingAt]
  · intro i hi
    simp [nextCheck, resetAt, hi, program, SourceOdometerSchedule.currentAt,
      SourceOdometerSchedule.remainingAt]
  · exact bodyTrace H base ready

end

end DFVSGames.Explicit.MachineProductLoop

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductFinish
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineProductFinish

open Turing
open DFVSGames.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram

variable {q t : Nat}

noncomputable section

def finishInTime (base : Tape t → List Bool) (emptyOutput : base (output t) = []) :
    StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some .finishStart, (((), ()), none), base⟩
      (some ⟨none, (((), ()), none),
        SourceRuntimeFinish.canonicalTapes (output t) (base (accumulator t)).reverse⟩)
      (1 + SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) base) := by
  have enter : StateTransition.EvalsToInTime (TM2.step (program q t))
      ⟨some .finishStart, (((), ()), none), base⟩
      (some ⟨SourceRuntimeFinish.entry (clearKeys t) Label.finish, (((), ()), none), base⟩) 1 := by
    refine ⟨⟨1, ?_⟩, Nat.le_refl _⟩
    change some (TM2.stepAux (program q t .finishStart) _ _) = _
    simp only [program, DFVSGames.Reduction.MachineTransfer.exitAt]
    split <;> simp_all [TM2.stepAux]
  have finish := SourceRuntimeFinish.finishInTime (clearKeys t) (accumulator t) (output t)
    (by simp [accumulator, output, auxiliary])
    (by simp) (by simp) (by intro k h1 h2; simp [h1, h2])
    ((), ()) Label.finish none (program q t) (fun _ => rfl) base emptyOutput ((), ()) none
  have joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ enter finish
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := by simpa only [Nat.add_comm] using joined.steps_le_m }

theorem finish_afterRows (H : Target.Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    Nonempty (StateTransition.EvalsToInTime (machine q t).step (afterRows H t)
      (some (haltList (machine q t) (gameBits (ProductPaddedOutput.output H presentation t ht))))
      (1 + SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t) (afterRows H t).stk)) := by
  have run := finishInTime (q := q) (afterRows H t).stk (afterRows_output H t)
  rw [afterRows_accumulator H presentation t ht] at run
  have hstart : (afterRows H t).l = some .finishStart := by simp [afterRows,
    SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration, nextCheck]
  have hstate : (afterRows H t).var = (((), ()), none) := rfl
  have halt : (⟨none, (((), ()), none), SourceRuntimeFinish.canonicalTapes (output t)
      (gameBits (ProductPaddedOutput.output H presentation t ht))⟩ :
      TM2.Cfg (fun _ : Tape t => Bool) (Label q t) State) =
      haltList (machine q t) (gameBits (ProductPaddedOutput.output H presentation t ht)) := by
    unfold haltList SourceRuntimeFinish.canonicalTapes
    congr 1
    funext k
    by_cases hk : k = output t <;> simp [machine, hk]
    rfl
  rw [halt] at run
  have hcfg : (⟨some .finishStart, (((), ()), none), (afterRows H t).stk⟩ :
      TM2.Cfg (fun _ : Tape t => Bool) (Label q t) State) =
      afterRows H t := by cases h : afterRows H t; simp_all
  rw [hcfg] at run
  exact ⟨run⟩

end

end DFVSGames.Explicit.MachineProductFinish


namespace DFVSGames.Explicit.MachineProductRuntime

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def prefixInTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (MachineProductFinish.afterRows H t))
      ((prefixPolynomial q t).eval (gameBits H).length) := by
  let first := MachineProductHeaders.inPolynomialTime H t
  let loop := Classical.choice (MachineProductLoop.traversalInTime H
    (MachineProductHeaders.baseTapes H t) (MachineProductFinish.base_ready H t))
  let second : StateTransition.EvalsToInTime (machine q t).step
      (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (MachineProductHeaders.baseTapes H t))
      (some (MachineProductFinish.afterRows H t))
      ((loopPolynomial q t).eval (gameBits H).length) := {
    toEvalsTo := loop.toEvalsTo
    steps_le_m := loop.steps_le_m.trans (loop_budget H t) }
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  exact {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm]
        using joined.steps_le_m }

def timePolynomial (q t : Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q t) (clearKeys t).length
    (prefixPolynomial q t) + 1

def outputInTime {q : Nat} (H : Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    TM2OutputsInTime (machine q t) (gameBits H)
      (some (gameBits (ProductPaddedOutput.output H presentation t ht)))
      ((timePolynomial q t).eval (gameBits H).length) := by
  let initialRun := prefixInTime H t
  let finish := Classical.choice (MachineProductFinish.finish_afterRows H presentation t ht)
  let whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initialRun finish
  have keepAccumulator : accumulator t ∉ clearKeys t := by simp
  have keepOutput : output t ∉ clearKeys t := by simp
  have covers (k : Tape t) (ha : k ≠ accumulator t) (ho : k ≠ output t) :
      k ∈ clearKeys t := (mem_clearKeys t k).mpr ⟨ha, ho⟩
  have bound := SourceRuntimeSpace.finishCost_le_of_prefix (machine q t) (gameBits H)
    initialRun (clearKeys t) (accumulator t) (output t)
    keepAccumulator keepOutput covers
    (MachineProductFinish.afterRows H t).stk (MachineProductFinish.afterRows_output H t)
    (fun _ => rfl)
  change StateTransition.EvalsToInTime (machine q t).step _
    (some (haltList (machine q t) _)) _
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one,
    SourceRuntimeSpace.completedTime_eval]
  simp only [machine] at bound ⊢
  change SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t)
    (MachineProductFinish.afterRows H t).stk ≤ _ at bound
  omega

def computation (q t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime (fun H : Input q => gameBits H.1) gameBits
      (construct t ht) where
  tm := machine q t
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q t
  outputsFun H := by
    change TM2OutputsInTime (machine q t) ((gameBits H.1).map id)
      (some ((gameBits (construct t ht H)).map id)) _
    convert outputInTime H.1 H.2 t ht using 1
    all_goals try with_reducible_and_instances rfl
    simp only [machine, List.map_id, construct]

theorem finiteAlphabet (q t : Nat) (ht : 0 < t) :
    MachineFiniteAlphabet.FiniteAlphabet (computation q t ht).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

variable {A : Type} {q : Nat} {encode : A → List Bool} {f : A → Instance q}

def compose (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) :
    TM2ComputableInPolyTime encode gameBits
      (fun a => ProductPaddedOutput.output (f a) (presentation a) t ht) :=
  MachineSequential.composeBits (certify upstream presentation) (computation q t ht)

theorem compose_finiteAlphabet (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a))
    (t : Nat) (ht : 0 < t) (finite : MachineFiniteAlphabet.FiniteAlphabet upstream.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (compose upstream presentation t ht).tm :=
  MachineFiniteAlphabet.composeBits (certify upstream presentation) (computation q t ht)
    finite (finiteAlphabet q t ht)

end

end DFVSGames.Explicit.MachineProductRuntime


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLazyTable
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

namespace DFVSGames.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

abbrev State (d : Nat) := MachineLazyRows.StreamState Unit d

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFStream
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

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

theorem rowWords_nonempty (table : GraphTables.Table) (e : Fin table.darts) :
    encodeWords (GraphTables.rowWords table.rows[e]) ≠ [] := by
  simp [GraphTables.rowWords, encodeWords, encodeWord]

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_MachineClone100Finish
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

namespace DFVSGames.Explicit.MachineClone100Finish

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

def finishTapes (base : Tape → List Bool) : Tape → List Bool :=
  MachineTransfer.tapesAt .reversed .output (Function.update base .counter []) []
    ((base .reversed).reverse ++ base .output)

@[simp] theorem finishTapes_counter (base : Tape → List Bool) :
    finishTapes base .counter = [] := by simp [finishTapes, MachineTransfer.tapesAt]

@[simp] theorem finishTapes_reversed (base : Tape → List Bool) :
    finishTapes base .reversed = [] := by simp [finishTapes, MachineTransfer.tapesAt]

@[simp] theorem finishTapes_output (base : Tape → List Bool) :
    finishTapes base .output = (base .reversed).reverse ++ base .output := by
  simp [finishTapes, MachineTransfer.tapesAt]

theorem counterStep (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    TM2.step (program triples hne)
      ⟨some .finalCounter, initialState _, base⟩ =
        some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩ := by
  simp [TM2.step, TM2.stepAux, program, initialState, hcounter]

theorem finishTrace (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 2]
      (some ⟨some .finalCounter, initialState _, base⟩) =
        some ⟨none, initialState _, finishTapes base⟩ := by
  have first := counterStep triples hne base hcounter
  have rest := MachineTransfer.transferAt_fromTapes Tape.reversed Tape.output
    (by decide) id false (Label.finalReverse : Label triples.length) none
    (program triples hne) rfl (Function.update base Tape.counter [])
    ((), defaultControl triples.length) none
  change (MachineComposition.advance (TM2.step (program triples hne)))^[
      ((Function.update base Tape.counter []) Tape.reversed).length + 1]
    (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) = _ at rest
  have rest' :
      (MachineComposition.advance (TM2.step (program triples hne)))^[(base .reversed).length + 1]
        (some ⟨some .finalReverse, initialState _, Function.update base .counter []⟩) =
          some ⟨none, initialState _, finishTapes base⟩ := by
    simpa only [finishTapes, initialState,
      Function.update_of_ne (by decide : Tape.reversed ≠ Tape.counter),
      Function.update_of_ne (by decide : Tape.output ≠ Tape.counter), List.map_id] using rest
  rw [show (base .reversed).length + 2 = ((base .reversed).length + 1) + 1 by omega,
    Function.iterate_succ_apply, MachineComposition.advance_some, first]
  exact rest'

def finishInTime (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    StateTransition.EvalsToInTime (TM2.step (program triples hne))
      ⟨some .finalCounter, initialState _, base⟩
      (some ⟨none, initialState _, finishTapes base⟩) ((base .reversed).length + 2) where
  steps := (base .reversed).length + 2
  evals_in_steps := finishTrace triples hne base hcounter
  steps_le_m := Nat.le_refl _

theorem finish_eq_haltList (triples : List (Nat × Nat × Nat)) (hne : triples ≠ [])
    (base : Tape → List Bool)
    (emptyOther : ∀ tape, tape ≠ .counter → tape ≠ .reversed → base tape = []) :
    (⟨none, initialState _, finishTapes base⟩ : (machine triples hne).Cfg) =
      haltList (machine triples hne) ((base .reversed).reverse) := by
  have hout := emptyOther .output (by decide) (by decide)
  have ht : finishTapes base =
      (haltList (machine triples hne) ((base .reversed).reverse)).stk := by
    funext tape
    cases tape <;> simp [finishTapes, MachineTransfer.tapesAt, haltList, machine, hout,
      emptyOther]
    rfl
  exact congrArg
    (fun tapes => (⟨none, initialState triples.length, tapes⟩ : (machine triples hne).Cfg)) ht

end DFVSGames.Explicit.MachineClone100Finish
end

section

namespace DFVSGames.Explicit.MachineClone100Run

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

def emptyTapes : Tape → List Bool := fun _ => []

def inputTapes (input : SourceEncoding.Input) : Tape → List Bool :=
  fun tape => if tape = .input then SourceEncoding.inputBits input else []

def guardTapes (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    Tape → List Bool :=
  MachineClone100Loop.tapes emptyTapes (sourceBody input) (encodeWord input.equations.length)
    (outputHeaders triples input).reverse (fun _ => [])

def afterLoopTapes (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    Tape → List Bool :=
  MachineClone100Loop.tapes emptyTapes [] (encodeWord 0)
    ((outputBody triples input).reverse ++ (outputHeaders triples input).reverse) (fun _ => [])

theorem initList_eq (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    initList (tm triples nonempty) (SourceEncoding.inputBits input) =
      ⟨some (.headerStart 0), initialState triples.length, inputTapes input⟩ := by
  change (⟨some (.headerStart 0), initialState triples.length,
    (initList (tm triples nonempty) (SourceEncoding.inputBits input)).stk⟩ :
    (tm triples nonempty).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨some (.headerStart 0), initialState triples.length, tapes⟩ : (tm triples nonempty).Cfg))
  funext tape
  cases tape <;> simp [initList, tm, machine, inputTapes]
  rfl

theorem headers_result_eq (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    MachineClone100Headers.resultTapes triples (inputTapes input)
      input.«variables» input.equations.length (sourceBody input) = guardTapes triples input := by
  funext tape
  cases tape <;> simp [MachineClone100Headers.resultTapes, inputTapes, guardTapes,
    MachineClone100Loop.tapes, emptyTapes, outputHeaders]

theorem afterLoop_reversed (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    (afterLoopTapes triples input .reversed).reverse = outputBits triples input := by
  simp only [afterLoopTapes, MachineClone100Loop.tapes, List.reverse_append,
    List.reverse_reverse, outputBits]

theorem afterLoop_length (triples : List (Nat × Nat × Nat)) (input : SourceEncoding.Input) :
    (afterLoopTapes triples input .reversed).length = (outputBits triples input).length := by
  calc
    _ = ((afterLoopTapes triples input .reversed).reverse).length := List.length_reverse.symm
    _ = _ := congrArg List.length (afterLoop_reversed triples input)

theorem finish_eq (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    (⟨none, initialState triples.length,
      MachineClone100Finish.finishTapes (afterLoopTapes triples input)⟩ :
      (tm triples nonempty).Cfg) =
        haltList (tm triples nonempty) (outputBits triples input) := by
  have finished := MachineClone100Finish.finish_eq_haltList triples nonempty
    (afterLoopTapes triples input) (by
      intro tape counter reversed
      cases tape <;> simp_all [afterLoopTapes, MachineClone100Loop.tapes, emptyTapes])
  simpa only [afterLoop_reversed, tm] using finished

def runInTime (triples : List (Nat × Nat × Nat)) (nonempty : triples ≠ [])
    (input : SourceEncoding.Input) :
    TM2OutputsInTime (tm triples nonempty) (SourceEncoding.inputBits input)
      (some (outputBits triples input))
      (((outputBits triples input).length + 2) +
        (((2 + 3 * triples.length) * (sourceBody input).length +
            (9 + 12 * triples.length) * input.equations.length + 1) +
          (5 * input.«variables» + 4 * input.equations.length + 18))) := by
  let first := MachineClone100Headers.headersInTime triples nonempty
    (inputTapes input) input.«variables» input.equations.length (sourceBody input)
    (by simpa only [inputTapes, ite_true, if_true] using inputBits_eq input) rfl rfl rfl rfl
  have first' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      (initList (tm triples nonempty) (SourceEncoding.inputBits input))
      (some ⟨some .guard, initialState _, guardTapes triples input⟩)
      (5 * input.«variables» + 4 * input.equations.length + 18) := by
    rw [initList_eq, ← headers_result_eq]
    exact first
  let middle := MachineClone100Loop.sourceLoopInTime_table triples nonempty
    (n := input.«variables») input.equations emptyTapes [] (outputHeaders triples input).reverse
  have middle' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .guard, initialState _, guardTapes triples input⟩
      (some ⟨some .finalCounter, initialState _, afterLoopTapes triples input⟩)
      ((2 + 3 * triples.length) * (sourceBody input).length +
        (9 + 12 * triples.length) * input.equations.length + 1) := by
    simpa only [List.append_nil, guardTapes, afterLoopTapes, sourceBody, outputBody] using middle
  let last := MachineClone100Finish.finishInTime triples nonempty (afterLoopTapes triples input) rfl
  have last' : StateTransition.EvalsToInTime (TM2.step (program triples nonempty))
      ⟨some .finalCounter, initialState _, afterLoopTapes triples input⟩
      (some (haltList (tm triples nonempty) (outputBits triples input)))
      ((outputBits triples input).length + 2) := by
    rw [← afterLoop_length, ← finish_eq]
    exact last
  let firstTwo := StateTransition.EvalsToInTime.trans
    (TM2.step (program triples nonempty)) _ _ _ _ _ first' middle'
  let allThree := StateTransition.EvalsToInTime.trans
    (TM2.step (program triples nonempty)) _ _ _ _ _ firstTwo last'
  exact { toEvalsTo := allThree.toEvalsTo, steps_le_m := allThree.steps_le_m }

end DFVSGames.Explicit.MachineClone100Run
end

section

namespace DFVSGames.Explicit.MachineClone100Certified

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity

noncomputable def certifiedFunction (triples : List (CloneGap.Index × CloneGap.Index × CloneGap.Index))
    (nonempty : triples ≠ []) (f : SourceEncoding.Input → SourceEncoding.Input)
    (output_eq : ∀ input, SourceEncoding.inputBits (f input) =
      MachineClone100Run.outputBits triples input)
    (size_bound : ∀ input,
      (SourceEncoding.inputBits (f input)).length ≤
        (300 * triples.length) * (SourceEncoding.inputBits input).length *
            (SourceEncoding.inputBits input).length +
          (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2) :
    TM2ComputableInPolyTime SourceEncoding.inputBits SourceEncoding.inputBits f where
  tm := MachineClone100Run.tm triples nonempty
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial triples.length
  outputsFun input := by
    change TM2OutputsInTime (MachineClone100Run.tm triples nonempty)
      ((SourceEncoding.inputBits input).map id)
      (some ((SourceEncoding.inputBits (f input)).map id))
      ((timePolynomial triples.length).eval (SourceEncoding.inputBits input).length)
    rw [@List.map_id ((MachineClone100Run.tm triples nonempty).Γ
      (MachineClone100Run.tm triples nonempty).k₀) (SourceEncoding.inputBits input),
      @List.map_id ((MachineClone100Run.tm triples nonempty).Γ
        (MachineClone100Run.tm triples nonempty).k₁) (SourceEncoding.inputBits (f input)),
      output_eq input, timePolynomial_eval]
    let actual := MachineClone100Run.runInTime triples nonempty input
    refine { toEvalsTo := actual.toEvalsTo, steps_le_m := actual.steps_le_m.trans ?_ }
    apply numericalBudget_inline_MachineClone100Certified
    · exact SourceEncoding.inputBits_length_ge_variables input
    · exact SourceEncoding.inputBits_length_ge_equations input
    · have h := SourceEncoding.inputBits_length input
      change (SourceEncoding.inputBits input).length =
        input.«variables» + input.equations.length + 2 +
          (MachineClone100Run.sourceBody input).length at h
      omega
    · rw [← output_eq input]
      exact size_bound input

end DFVSGames.Explicit.MachineClone100Certified
end

section

namespace DFVSGames.Explicit.MachineClone100

open Turing DFVSGames.Reduction
open DFVSGames.Foundations.Complexity

noncomputable section

def computation : TM2ComputableInPolyTime SourceEncoding.inputBits
    SourceEncoding.inputBits Outer.Clone100.clonedInput :=
  MachineClone100Certified.certifiedFunction triples triples_nonempty
    Outer.Clone100.clonedInput input_bits_eq size_bound

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

end

end DFVSGames.Explicit.MachineClone100
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryTotalInputMachine
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

namespace DFVSGames.BinaryTotalInputMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer
open DFVSGames.Reduction.MachineSubstitution
open BinaryValidatorMachine (Mode nextMode run)

theorem restoreTrace (saved output : List Bool) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .restore) [] output saved .clause register)) =
      some (cfg none [] (saved.reverse ++ output) []) := by
  change (nextAt (1 : Fin 3) instruction)^[saved.length + 1]
    (some ⟨some .restore, (Mode.clause, register), tapes [] output saved⟩) =
    some ⟨none, (Mode.clause, none), tapes [] (saved.reverse ++ output) []⟩
  have trace := transferAt_steps (2 : Fin 3) 1 (by decide) id false .restore none
    instruction rfl (tapes [] [] []) saved output Mode.clause register
  simpa only [tapesAt, update_saved_inline_MachineBinaryTotalInputMachine, update_output_inline_MachineBinaryTotalInputMachine,
    List.map_id_fun, id_eq] using trace

theorem acceptedTrace (input : List Bool) (accepted : run .clause input = .done) :
    (advance machine.step)^[2 * input.length + 2]
      (some (cfg (some .scan) input [] [])) = some (cfg none [] input []) := by
  have first := scanTrace input [] [] .clause none
  simp only [afterScan, accepted, ↓reduceIte, List.append_nil] at first
  have second := restoreTrace input.reverse [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at second
  have time : 2 * input.length + 2 = (input.length + 1) + (input.length + 1) := by omega
  rw [time]
  exact joinTrace_inline_MachineBinaryTotalInputMachine first second

theorem totalTrace (input : List Bool) :
    (advance machine.step)^[steps input] (some (initList machine input)) =
      some (haltList machine (BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input))) := by
  rw [initList_eq, haltList_eq]
  cases parsed : BinaryEncoding.decodeFormula input with
  | none =>
      have rejected : run .clause input ≠ .done := by
        intro accepted
        obtain ⟨formula, encoded⟩ := (BinaryValidatorMachine.run_clause_iff input).mp accepted
        have roundtrip := BinaryEncoding.decodeFormula_encoded formula
        rw [← encoded, parsed] at roundtrip
        cases roundtrip
      simpa only [steps, rejected, ↓reduceIte, BinaryLanguage.totalParsed, parsed,
        Option.getD_none, rejectedWord] using rejectedTrace input rejected
  | some formula =>
      have encoded := BinaryParsing.decodeFormula_sound input formula parsed
      have accepted := (BinaryValidatorMachine.run_clause_iff input).mpr ⟨formula, encoded⟩
      simp only [steps, accepted, ↓reduceIte, BinaryLanguage.totalParsed, parsed,
        Option.getD_some]
      rw [← encoded]
      exact acceptedTrace input accepted

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input
      (some (BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input)))
      (2 * input.length + 3) where
  steps := steps input
  evals_in_steps := totalTrace input
  steps_le_m := steps_le input

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) BinaryEncoding.formulaBits
      BinaryLanguage.totalParsed where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id)
      (some ((BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input)).map id))
      ((2 * Polynomial.X + 3 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat] using outputsInTime input

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  machine_finiteAlphabet

end DFVSGames.BinaryTotalInputMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryLiteralMachine
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

namespace DFVSGames.BinaryRenameLoop

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

theorem payload_length_le_stream (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    bits.length ≤ (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp at present
  | cons token tokens ih =>
      rcases List.mem_cons.mp present with equal | remaining
      · rw [equal]
        simp only [BinaryNameSearch.stream_cons, List.length_append,
          BinaryNameSearch.tokenBits, List.length_cons, BinaryNameMachine.frame_length]
        omega
      · have tail := ih remaining
        simp only [BinaryNameSearch.stream_cons, List.length_append]
        omega

theorem literal_steps_le (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    BinaryLiteralMachine.steps tokens bits + 2 ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length := by
  have body := BinaryLiteralMachine.steps_le tokens bits present
  have size := payload_length_le_stream tokens bits present
  have sumBound : (BinaryNameSearch.stream tokens).length + bits.length ≤
      2 * (BinaryNameSearch.stream tokens).length := by omega
  have sq := Nat.mul_self_le_mul_self sumBound
  unfold perLiteralBound
  nlinarith

theorem steps_le (tokens input : List Token) (included : ∀ token ∈ input, token ∈ tokens) :
    steps tokens input ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length * input.length + 1 := by
  induction input with
  | nil => simp [steps]
  | cons token input ih =>
      have present : token.2 ∈ BinaryNameSearch.payloads tokens :=
        List.mem_map.mpr ⟨token, included token (by simp), rfl⟩
      have head := literal_steps_le tokens token.2 present
      have tail := ih (fun t ht => included t (by simp [ht]))
      simp only [steps, List.length_cons]
      nlinarith

end DFVSGames.BinaryRenameLoop

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryTokenMachine
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

namespace DFVSGames.BinaryRenameWords

open BinaryFormula DFVSGames.Foundations

theorem encoded_body (F : Formula) :
    Complexity.encodeWords ((BinaryOccurrenceRename.renamed F).clauses.flatMap
      Complexity.clauseWords) = body F := by
  rw [encodeWords_flatMap_inline_MachineBinaryRenameWords]
  change (F.clauses.attach.map (fun c => BinaryOccurrenceRename.clause F c.val c.property)).flatMap
    (fun c => Complexity.encodeWords (Complexity.clauseWords c)) = body F
  rw [List.flatMap_map]
  simp only [encoded_clause]
  have h := congrArg (fun cs : List Clause =>
    cs.flatMap (fun c => (clauseLiterals c).flatMap (outputLiteral (sourceNames F))))
    (List.attach_map_subtype_val F.clauses)
  simpa only [List.flatMap_map, body, literals, List.flatMap_assoc] using h

theorem encoded_renamed (F : Formula) :
    Complexity.formulaBits (BinaryOccurrenceRename.renamed F) =
      Complexity.encodeWord (3 * F.clauses.length) ++
        Complexity.encodeWord F.clauses.length ++ body F := by
  simp only [Complexity.formulaBits, Complexity.formulaWords, Complexity.encodeWords_append,
    Complexity.encodeWords, List.append_nil,
    BinaryOccurrenceRename.renamed_variable_count,
    BinaryOccurrenceRename.renamed_clause_count, encoded_body, List.append_assoc]

end DFVSGames.BinaryRenameWords

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryRenameMachine
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

namespace DFVSGames.BinaryRenameMachine

open Turing DFVSGames.Foundations
open Complexity Complexity.MachineComposition
open DFVSGames.Reduction.MachineTransfer

theorem renameTrace (formula : BinaryFormula.Formula) :
    (advance machine.step)^[steps formula]
      (some (initList machine (BinaryTokenMachine.tokens formula.clauses))) =
      some (haltList machine (formulaBits (BinaryOccurrenceRename.renamed formula))) := by
  have first := copyTrace (BinaryTokenMachine.tokens formula.clauses)
  have second := loopTrace formula
  have third := restoreTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (List.replicate (3 * formula.clauses.length) true)
    (List.replicate formula.clauses.length true)
  have fourth := headerTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (3 * formula.clauses.length) formula.clauses.length
  have fifth := cleanupTrace (BinaryTokenMachine.tokens formula.clauses)
    (encodeWord (3 * formula.clauses.length) ++ encodeWord formula.clauses.length ++
      BinaryRenameWords.body formula)
  have full := joinTrace_inline_MachineBinaryRenameMachine (joinTrace_inline_MachineBinaryRenameMachine (joinTrace_inline_MachineBinaryRenameMachine (joinTrace_inline_MachineBinaryRenameMachine first second) third) fourth) fifth
  have count : 3 * formula.clauses.length + formula.clauses.length + 4 =
      4 * formula.clauses.length + 4 := by omega
  simpa only [steps, initList_eq, haltList_eq, BinaryRenameWords.encoded_renamed, count] using full

theorem body_length_le (formula : BinaryFormula.Formula) :
    (BinaryRenameWords.body formula).length ≤
      9 * (BinaryTokenMachine.tokens formula.clauses).length ^ 2 +
        10 * (BinaryTokenMachine.tokens formula.clauses).length + 2 := by
  have initial := BinaryOccurrenceRename.renamed_encoding_bound formula
  rw [BinaryRenameWords.encoded_renamed] at initial
  simp only [List.length_append] at initial
  have count := clause_count_le_stream formula
  have square := Nat.mul_self_le_mul_self count
  nlinarith

theorem steps_le (formula : BinaryFormula.Formula) :
    steps formula ≤ timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length := by
  have loopBound := BinaryRenameLoop.steps_le
    (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)
    (fun _ h => h)
  rw [BinaryRenameWords.tokens_stream, BinaryRenameWords.tokens_length] at loopBound
  have literalCount : 3 * formula.clauses.length ≤
      (BinaryTokenMachine.tokens formula.clauses).length := by
    rw [BinaryTokenMachine.tokens_length]
    omega
  have product := Nat.mul_le_mul_left
    (BinaryRenameLoop.perLiteralBound (BinaryTokenMachine.tokens formula.clauses).length)
    literalCount
  have output := body_length_le formula
  have count := clause_count_le_stream formula
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold steps BinaryRenameLoop.perLiteralBound at *
  nlinarith

def outputsInTime (formula : BinaryFormula.Formula) :
    TM2OutputsInTime machine (BinaryTokenMachine.tokens formula.clauses)
      (some (formulaBits (BinaryOccurrenceRename.renamed formula)))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length) where
  steps := steps formula
  evals_in_steps := renameTrace formula
  steps_le_m := steps_le formula

noncomputable def tokenComputation :
    TM2ComputableInPolyTime (fun formula : BinaryFormula.Formula =>
      BinaryTokenMachine.tokens formula.clauses) formulaBits BinaryOccurrenceRename.renamed where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun formula := by
    change TM2OutputsInTime machine ((BinaryTokenMachine.tokens formula.clauses).map id)
      (some ((formulaBits (BinaryOccurrenceRename.renamed formula)).map id))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length)
    simpa only [List.map_id_fun, id_eq] using outputsInTime formula

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits formulaBits
      BinaryOccurrenceRename.renamed :=
  MachineSequential.composeBits preprocessing tokenComputation

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  MachineFiniteAlphabet.composeBits preprocessing tokenComputation
    BinaryTokenMachine.machine_finiteAlphabet machine_finiteAlphabet

end DFVSGames.BinaryRenameMachine

end

section

namespace DFVSGames.BinaryInputReduction

open Turing DFVSGames.Foundations.Complexity

noncomputable def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits BinaryLanguage.totalRename := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => BinaryOccurrenceRename.renamed (BinaryLanguage.totalParsed input))
  exact MachineSequential.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime
    BinaryTotalInputMachine.computation_finiteAlphabet
    BinaryRenameMachine.computation_finiteAlphabet

end DFVSGames.BinaryInputReduction

end

section

namespace DFVSGames.Explicit.MachineSingleOrbitProgram

open Turing
open DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad
open DFVSGames.Reduction

def program (q : Nat) : Label q → TM2.Stmt (fun _ : Tape => Bool) (Label q) State
  | .start => .push .capacity (fun _ => false)
      (.push .remaining (fun _ => false) (.goto fun _ => .halfFirst))
  | .halfFirst => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.goto fun _ => .halfSecond)
        (.push .accumulator (fun _ => false)
          (.load (fun _ => initialState) (.goto fun _ => .alphabet))))
  | .halfSecond => .pop .input (fun state _ => state)
      (.push .capacity (fun _ => true)
        (.push .accumulator (fun _ => true) (.goto fun _ => .halfFirst)))
  | .alphabet => copyField .alphabet .count
  | .count => .pop .input (fun state head => (state.1, head))
      (.push .accumulator (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (.push .remaining (fun _ => true) (.goto fun _ => .count))
          (.load (fun _ => initialState) (.goto fun _ => .guard))))
  | .guard => MachineUnaryCounter.guard .remaining .source .finishStart
  | .source => copyField .source .subtract
  | .subtract => .peek .capacity (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.pop .capacity (fun state _ => state)
          (.pop .input (fun state _ => state)
            (.push .saved (fun _ => true) (.goto fun _ => .subtract))))
        (.load (fun _ => initialState) (.goto fun _ => .restore)))
  | .restore => MachineTransfer.loopAt .saved .capacity id false .restore (some .target)
  | .target => copyField .target (.table 0)
  | .table completed =>
      if h : completed.val < q then
        copyField (.table completed) (.table ⟨completed.val + 1, by omega⟩)
      else .load (fun _ => initialState) (.goto fun _ => .guard)
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      () Label.finish none label

def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label q
  main := .start
  σ := State
  initialState := initialState
  m := program q

end DFVSGames.Explicit.MachineSingleOrbitProgram
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitStreams

open Turing DFVSGames.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram

theorem copyStep_true {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (true :: i) c s r a o) =
      some (cfg loopLabel (some true) i c s r (true :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg]

theorem copyStep_false {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg loopLabel register (false :: i) c s r a o) =
      some (cfg exitLabel none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q loopLabel) _ _) = _
  rw [atLoop]
  simp [copyField, TM2.stepAux, cfg, initialState]

theorem copyFieldTrace {q : Nat} (loopLabel exitLabel : Label q)
    (atLoop : program q loopLabel = copyField loopLabel exitLabel)
    (n : Nat) (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg loopLabel register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg exitLabel none suffix c s r ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing a register with
  | zero =>
    simpa [encodeWord] using copyStep_false loopLabel exitLabel atLoop suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some,
      copyStep_true loopLabel exitLabel atLoop, ih]
    congr 2
    simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem tableTrace {q : Nat} (completed : Fin (q + 1)) (words : List Nat)
    (hcount : completed.val + words.length = q)
    (suffix c s r a o : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some (cfg (.table completed) register (encodeWords words ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s r ((encodeWords words).reverse ++ a) o) := by
  induction words generalizing completed a register with
  | nil =>
    have hc : ¬ completed.val < q := by simp only [List.length_nil] at hcount; omega
    change some (TM2.stepAux (program q (.table completed)) _ _) = _
    simp [program, hc, TM2.stepAux, cfg, initialState, encodeWords]
  | cons n words ih =>
    have hc : completed.val < q := by simp only [List.length_cons] at hcount; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at hcount
      dsimp [next]
      omega
    have hp : program q (.table completed) = copyField (.table completed) (.table next) := by
      simp [program, hc, next]
    have first := copyFieldTrace (.table completed) (.table next) hp n
      (encodeWords words ++ suffix) c s r a o register
    have rest := ih next hn ((encodeWord n).reverse ++ a) none
    have ht : (encodeWords (n :: words)).length + 1 =
        ((encodeWords words).length + 1) + (n + 1) := by
      simp only [encodeWords, List.length_append, encodeWord_length]
      omega
    rw [ht, Function.iterate_add_apply]
    simp only [encodeWords, List.append_assoc]
    rw [first, rest]
    simp only [List.reverse_append, List.append_assoc]

end DFVSGames.Explicit.MachineSingleOrbitStreams
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitCodec
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

namespace DFVSGames.Explicit.MachineSingleOrbitHeader

open Turing DFVSGames.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem halfStep_first {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (true :: i) c s r a o) =
      some (cfg .halfSecond (some true) i c s r a o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_second {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfSecond register (true :: i) c s r a o) =
      some (cfg .halfFirst register i (true :: c) s r (true :: a) o) := by
  change some (TM2.stepAux (program q .halfSecond) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem halfStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .halfFirst register (false :: i) c s r a o) =
      some (cfg .alphabet none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .halfFirst) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

theorem halfTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * n + 1]
      (some (cfg .halfFirst register (encodeWord (2 * n) ++ suffix) c s r a o)) =
      some (cfg .alphabet none suffix (List.replicate n true ++ c) s r
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing c a register with
  | zero =>
    simpa [encodeWord] using halfStep_false suffix c s r a o register
  | succ n ih =>
    have ht : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by omega
    have hw : encodeWord (2 * (n + 1)) ++ suffix =
        true :: true :: (encodeWord (2 * n) ++ suffix) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, ht, Function.iterate_succ_apply, advance_some, halfStep_first,
      Function.iterate_succ_apply, advance_some, halfStep_second, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem countStep_true {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (true :: i) c s r a o) =
      some (cfg .count (some true) i c s (true :: r) (true :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem countStep_false {q : Nat} (i c s r a o : List Bool) (register : Option Bool) :
    TM2.step (program q) (cfg .count register (false :: i) c s r a o) =
      some (cfg .guard none i c s r (false :: a) o) := by
  change some (TM2.stepAux (program q .count) _ _) = _
  simp [program, TM2.stepAux, cfg, initialState]

theorem countTrace {q : Nat} (n : Nat) (suffix c s r a o : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .count register (encodeWord n ++ suffix) c s r a o)) =
      some (cfg .guard none suffix c s (List.replicate n true ++ r)
        ((encodeWord n).reverse ++ a) o) := by
  induction n generalizing r a register with
  | zero =>
    simpa [encodeWord] using countStep_false suffix c s r a o register
  | succ n ih =>
    have hw : encodeWord (n + 1) ++ suffix = true :: (encodeWord n ++ suffix) := by
      simp [encodeWord, List.replicate_succ, List.append_assoc]
    rw [hw, Function.iterate_succ_apply, advance_some, countStep_true, ih]
    congr 2
    · simp only [List.replicate_succ', List.append_assoc, List.singleton_append]
    · simp [encodeWord, List.replicate_succ, List.reverse_cons, List.append_assoc]

theorem initial_configuration (q : Nat) (input : List Bool) :
    initList (machine q) input = cfg .start none input [] [] [] [] [] := by
  have ht : (initList (machine q) input).stk = tapes input [] [] [] [] [] := by
    dsimp only [machine]
    funext t
    cases t <;> simp [initList, tapes]
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem initialStep (q : Nat) (input : List Bool) :
    TM2.step (program q) (initList (machine q) input) =
      some (cfg .halfFirst none input [false] [] [false] [] []) := by
  rw [initial_configuration]
  change some (TM2.stepAux (program q .start) _ _) = _
  simp [program, TM2.stepAux, cfg]

theorem headerTrace (q C m : Nat) (suffix : List Bool) :
    (advance (TM2.step (program q)))^[2 * C + q + m + 4]
      (some (initList (machine q)
        (encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix))) =
      some (cfg .guard none suffix (encodeWord C) [] (encodeWord m)
        (encodeWords [C, q, m]).reverse []) := by
  let input := encodeWord (2 * C) ++ encodeWord q ++ encodeWord m ++ suffix
  have hfirst :
      (advance (TM2.step (program q)))^[(2 * C + 1) + 1]
        (some (initList (machine q) input)) =
        some (cfg .alphabet none (encodeWord q ++ encodeWord m ++ suffix)
          (encodeWord C) [] [false] (encodeWord C).reverse []) := by
    rw [Function.iterate_add_apply _ (2 * C + 1) 1, Function.iterate_one]
    have first := congrArg ((advance (TM2.step (program q)))^[2 * C + 1])
      (initialStep q input)
    have rest := halfTrace (q := q) C (encodeWord q ++ encodeWord m ++ suffix)
      [false] [] [false] [] [] none
    refine first.trans ?_
    simpa only [input, encodeWord, List.append_nil, List.append_assoc] using rest
  have hsecond :
      (advance (TM2.step (program q)))^[(q + 1) + ((2 * C + 1) + 1)]
        (some (initList (machine q) input)) =
        some (cfg .count none (encodeWord m ++ suffix) (encodeWord C) [] [false]
          ((encodeWord q).reverse ++ (encodeWord C).reverse) []) := by
    rw [Function.iterate_add_apply _ (q + 1) ((2 * C + 1) + 1), hfirst]
    simpa only [List.append_assoc] using
      copyFieldTrace (q := q) .alphabet .count rfl q (encodeWord m ++ suffix)
        (encodeWord C) [] [false] (encodeWord C).reverse [] none
  have ht : 2 * C + q + m + 4 = (m + 1) + ((q + 1) + ((2 * C + 1) + 1)) := by omega
  change (advance (TM2.step (program q)))^[2 * C + q + m + 4]
    (some (initList (machine q) input)) = _
  rw [ht, Function.iterate_add_apply _ (m + 1) ((q + 1) + ((2 * C + 1) + 1)), hsecond]
  have hlast := countTrace (q := q) m suffix (encodeWord C) [] [false]
    ((encodeWord q).reverse ++ (encodeWord C).reverse) [] none
  simpa [encodeWord, encodeWords, List.reverse_append, List.append_assoc] using hlast

end DFVSGames.Explicit.MachineSingleOrbitHeader
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitSubtract

open Turing DFVSGames.Foundations.Complexity DFVSGames.Reduction
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

theorem subtractStep_zero (q : Nat) (suffix saved remaining accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register suffix (encodeWord 0) saved remaining accumulator output) =
      some (cfg .restore none suffix (encodeWord 0) saved remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, initialState]

theorem subtractStep_succ (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    TM2.step (program q)
      (cfg .subtract register (List.replicate (n + 1) true ++ suffix)
        (encodeWord (n + 1)) saved remaining accumulator output) =
      some (cfg .subtract (some true) (List.replicate n true ++ suffix)
        (encodeWord n) (true :: saved) remaining accumulator output) := by
  change some (TM2.stepAux (program q .subtract) _ _) = _
  simp [program, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

theorem subtractTrace (q n : Nat)
    (suffix saved remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .subtract register (List.replicate n true ++ suffix)
        (encodeWord n) saved remaining accumulator output)) =
      some (cfg .restore none suffix (encodeWord 0)
        (List.replicate n true ++ saved) remaining accumulator output) := by
  induction n generalizing saved register with
  | zero =>
    simpa using subtractStep_zero q suffix saved remaining accumulator output register
  | succ n ih =>
    rw [Function.iterate_succ_apply, advance_some, subtractStep_succ, ih]
    congr 2
    simp [List.replicate_add, List.append_assoc]

theorem restore_tapes (suffix capacity saved remaining accumulator output newSaved newCapacity : List Bool) :
    MachineTransfer.tapesAt Tape.saved Tape.capacity
      (tapes suffix capacity saved remaining accumulator output) newSaved newCapacity =
      tapes suffix newCapacity newSaved remaining accumulator output := by
  simp [MachineTransfer.tapesAt]

theorem restoreTrace (q n : Nat) (suffix remaining accumulator output : List Bool) :
    (advance (TM2.step (program q)))^[n + 1]
      (some (cfg .restore none suffix (encodeWord 0) (List.replicate n true)
        remaining accumulator output)) =
      some (cfg .target none suffix (encodeWord n) [] remaining accumulator output) := by
  have h := MachineTransfer.transferAt_fromTapes (Γ := fun _ : Tape => Bool) (σ := Unit)
    Tape.saved Tape.capacity (by decide) id false (Label.restore : Label q) (some .target)
    (program q) rfl (tapes suffix (encodeWord 0) (List.replicate n true)
      remaining accumulator output) () none
  have next_eq : MachineTransfer.nextAt Tape.capacity (program q) =
      advance (TM2.step (program q)) := rfl
  rw [next_eq] at h
  simpa only [cfg, restore_tapes,
    tapes_saved, tapes_capacity, List.length_replicate,
    List.reverse_replicate, List.map_id, encodeWord, List.replicate_zero,
    List.nil_append] using h

theorem removeOffsetTrace (q C v : Nat) (suffix remaining accumulator output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step (program q)))^[2 * (C + 1)]
      (some (cfg .subtract register (encodeWord (C + v) ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .target none (encodeWord v ++ suffix) (encodeWord C)
        [] remaining accumulator output) := by
  have hw : encodeWord (C + v) ++ suffix =
      List.replicate C true ++ (encodeWord v ++ suffix) := by
    simp only [encodeWord, List.replicate_add, List.append_assoc]
  rw [hw, show 2 * (C + 1) = (C + 1) + (C + 1) by omega,
    Function.iterate_add_apply, subtractTrace]
  simp only [List.append_nil]
  exact restoreTrace q C (encodeWord v ++ suffix) remaining accumulator output

end DFVSGames.Explicit.MachineSingleOrbitSubtract
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitRows

open Turing DFVSGames.Foundations.Complexity DFVSGames.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitSubtract MachineSingleOrbitCodec

theorem rowTrace {C q : Nat} (c : Constraint C q)
    (suffix remaining accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowCost c]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .guard none suffix (encodeWord C) [] remaining
        ((rowBits c).reverse ++ accumulator) output) := by
  let table := encodeWords (tableWords c.permutation)
  let afterSource := (encodeWord c.source.val).reverse ++ accumulator
  let afterTarget := (encodeWord c.target.val).reverse ++ afterSource
  have hs := copyFieldTrace (q := q) .source .subtract rfl c.source.val
    (encodeWord (C + c.target.val) ++ table ++ suffix)
    (encodeWord C) [] remaining accumulator output register
  have hd := removeOffsetTrace q C c.target.val (table ++ suffix)
    remaining afterSource output none
  have ht := copyFieldTrace (q := q) .target (.table 0) rfl c.target.val
    (table ++ suffix) (encodeWord C) [] remaining afterSource output none
  have hp := tableTrace (q := q) 0 (tableWords c.permutation)
    (by simp) suffix (encodeWord C) [] remaining afterTarget output none
  have hs' : (advance (TM2.step (program q)))^[c.source.val + 1]
      (some (cfg .source register (doubledRowBits c ++ suffix)
        (encodeWord C) [] remaining accumulator output)) =
      some (cfg .subtract none (encodeWord (C + c.target.val) ++ (table ++ suffix))
        (encodeWord C) [] remaining afterSource output) := by
    simpa only [doubledRowBits_eq, List.append_assoc, afterSource, table] using hs
  have hsd := joinTrace hs' hd
  have hsdt := joinTrace hsd ht
  have hall := joinTrace hsdt hp
  have hcost : (encodeWords (tableWords c.permutation)).length + 1 +
        (c.target.val + 1 + (2 * (C + 1) + (c.source.val + 1))) = rowCost c := by
    simp only [rowCost, doubledRowBits_eq, List.length_append, encodeWord_length]
    omega
  rw [hcost] at hall
  simpa only [rowBits_eq, List.reverse_append, List.append_assoc,
    afterTarget, afterSource, table] using hall

theorem guardStep_succ (q n : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord (n + 1)) accumulator output) =
      some (cfg .source none input capacity saved (encodeWord n) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord, List.replicate_succ]

theorem guardStep_zero (q : Nat) (input capacity saved accumulator output : List Bool)
    (register : Option Bool) :
    TM2.step (program q)
      (cfg .guard register input capacity saved (encodeWord 0) accumulator output) =
      some (cfg .finishStart none input capacity saved (encodeWord 0) accumulator output) := by
  change some (TM2.stepAux (program q .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux, cfg, encodeWord]

theorem rowsTrace {C q : Nat} (cs : List (Constraint C q))
    (suffix accumulator output : List Bool) (register : Option Bool) :
    (advance (TM2.step (program q)))^[rowsCost cs]
      (some (cfg .guard register (doubledRowsBits cs ++ suffix)
        (encodeWord C) [] (encodeWord cs.length) accumulator output)) =
      some (cfg .finishStart none suffix (encodeWord C) [] (encodeWord 0)
        ((rowsBits cs).reverse ++ accumulator) output) := by
  induction cs generalizing accumulator register with
  | nil =>
    simpa [rowsCost] using guardStep_zero q suffix (encodeWord C) [] accumulator output register
  | cons c cs ih =>
    have hg : (advance (TM2.step (program q)))^[1]
        (some (cfg .guard register (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] (encodeWord (c :: cs).length) accumulator output)) =
        some (cfg .source none (doubledRowBits c ++ (doubledRowsBits cs ++ suffix))
          (encodeWord C) [] (encodeWord cs.length) accumulator output) := by
      simpa only [Function.iterate_one, advance_some, List.length_cons,
        doubledRowsBits_cons, List.append_assoc] using
        guardStep_succ q cs.length (doubledRowsBits (c :: cs) ++ suffix)
          (encodeWord C) [] accumulator output register
    have hr := rowTrace c (doubledRowsBits cs ++ suffix) (encodeWord cs.length)
      accumulator output none
    have ht := ih ((rowBits c).reverse ++ accumulator) none
    have hall := joinTrace (joinTrace hg hr) ht
    have hcost : rowsCost cs + (rowCost c + 1) = rowsCost (c :: cs) := by
      rw [rowsCost_cons]
      omega
    rw [hcost] at hall
    simpa only [rowsBits_cons, List.reverse_append, List.append_assoc] using hall

end DFVSGames.Explicit.MachineSingleOrbitRows
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitFinish

open Turing DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams

noncomputable section

theorem haltList_eq (q : Nat) (bits : List Bool) : haltList (machine q) bits =
    ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  change (⟨none, initialState, (haltList (machine q) bits).stk⟩ : (machine q).Cfg) = _
  apply congrArg (fun base => (⟨none, initialState, base⟩ : (machine q).Cfg))
  dsimp only [machine]
  funext tape
  cases tape <;> simp [haltList, SourceRuntimeFinish.canonicalTapes] <;> rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩) 1 where
  steps := 1
  evals_in_steps := by rfl
  steps_le_m := Nat.le_refl _

def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys Label.finish, initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using
        joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys clearKeys_covers
    () Label.finish none (program q) (fun _ => rfl) base outputEmpty () none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q) input (prefixTime + 1)
    prefixRun clearKeys Tape.accumulator Tape.output accumulator_not_mem_clearKeys
    output_not_mem_clearKeys clearKeys_covers base outputEmpty (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end

end DFVSGames.Explicit.MachineSingleOrbitFinish
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitRuntime

open Turing DFVSGames.Foundations.Complexity DFVSGames.Foundations.Target
open MachineComposition MachineSingleOrbitProgram MachineSingleOrbitStreams
open MachineSingleOrbitCodec MachineSingleOrbitRows

noncomputable section

theorem prefixTrace {q : Nat} (I : Instance q) :
    (advance (TM2.step (program q)))^[prefixCost I]
      (some (initList (machine q) (gameBits (doubleInstance I)))) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
  have hh := MachineSingleOrbitHeader.headerTrace q I.vertices I.constraints.length
    (doubledRowsBits I.constraints)
  have hr := rowsTrace I.constraints []
    (encodeWords [I.vertices, q, I.constraints.length]).reverse [] none
  have hbits : gameBits I =
      encodeWords [I.vertices, q, I.constraints.length] ++ rowsBits I.constraints := by
    simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc] using gameBits_eq I
  have hr' : (advance (TM2.step (program q)))^[rowsCost I.constraints]
      (some (cfg .guard none (doubledRowsBits I.constraints) (encodeWord I.vertices) []
        (encodeWord I.constraints.length)
        (encodeWords [I.vertices, q, I.constraints.length]).reverse [])) =
      some ⟨some .finishStart, initialState, finalTapes I⟩ := by
    simpa only [List.append_nil, cfg, finalTapes, hbits, List.reverse_append, initialState]
      using hr
  have run := joinTrace hh hr'
  have hcost : rowsCost I.constraints +
      (2 * I.vertices + q + I.constraints.length + 4) = prefixCost I := by
    rw [prefixCost, input_length_eq]
    unfold rowsCost
    omega
  rw [hcost] at run
  simpa only [doubled_gameBits_eq] using run

def prefixInTime {q : Nat} (I : Instance q) :
    StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) (gameBits (doubleInstance I)))
      (some ⟨some .finishStart, initialState, finalTapes I⟩)
      (prefixPolynomial.eval (gameBits (doubleInstance I)).length) where
  steps := prefixCost I
  evals_in_steps := prefixTrace I
  steps_le_m := prefixCost_le I

def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineSingleOrbitFinish.timePolynomial q prefixPolynomial

def fullRunInTime {q : Nat} (I : Instance q) :
    TM2OutputsInTime (machine q) (gameBits (doubleInstance I))
      (some (gameBits I)) ((timePolynomial q).eval (gameBits (doubleInstance I)).length) := by
  let run := MachineSingleOrbitFinish.completePrefix q (gameBits (doubleInstance I))
    prefixPolynomial (finalTapes I) (prefixInTime I) rfl
  simpa only [finalTapes, tapes_accumulator, List.reverse_reverse, timePolynomial] using run

def computableInPolyTime (q : Nat) :
    TM2ComputableInPolyTime (fun I : Instance q => gameBits (doubleInstance I)) gameBits id where
  tm := machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial q
  outputsFun I := by
    change TM2OutputsInTime (machine q) ((gameBits (doubleInstance I)).map id)
      (some ((gameBits I).map id))
      ((timePolynomial q).eval (gameBits (doubleInstance I)).length)
    dsimp only [machine]
    rw [List.map_id, List.map_id]
    exact fullRunInTime I

end

end DFVSGames.Explicit.MachineSingleOrbitRuntime
end

section

namespace DFVSGames.Reduction.SourceEquationLookup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
open SourceClauseLookup (discardFieldsTrace)

variable {σ : Type}

theorem atSkip (r : Nat) (hr : r < 4) :
    program (σ := σ) (skipLabel r) = MachineLookup.discard .work (skipLabel r) (skipLabel (r + 1)) := by
  simp [skipLabel, hr, program]

theorem atReadStart (r : Nat) (hr : r < 4) :
    program (σ := σ) (readStart r) = fieldStart (fieldDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 4) :
    program (σ := σ) (readLoop r) = fieldLoop .work (fieldDestination r) (readLoop r)
      (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (σ := σ) (readStart 4) = SourceFieldArray.finish .work none := by
  simp [program, readStart, SourceFieldArray.boundedIndex]

theorem discardHeadersTrace (base : Tape → List Bool) (variableCount equations : Nat)
    (suffix : List Bool) (hinput : base .work = encodeWords [variableCount, equations] ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[variableCount + equations + 2]
      (some ⟨some .headerFirst, (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work headerLabel program base 0 [variableCount, equations]
    suffix (by
      intro r hr
      have he : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases he with rfl | rfl <;> rfl) hinput ambient
  simpa [encodeWords_length, headerLabel] using ht

theorem discardFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (skipLabel 0), (ambient, none), base⟩) =
      some ⟨some .guard, (ambient, none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work skipLabel program base 0 values suffix
    (by intro r hr; simpa only [Nat.zero_add] using atSkip r (by omega)) hinput ambient
  simpa [hlen, skipLabel] using ht

theorem readFourTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 4) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length + 5]
      (some ⟨some (readStart 0), (ambient, none), base⟩) =
      some ⟨none, (ambient, none),
        SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix⟩ := by
  have ht := SourceFieldArray.sequenceTrace .work fieldDestination readStart readLoop none
    program base 0 values suffix (by intro r hr; simp [fieldDestination])
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart r (by omega))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop r (by omega))
    (by simpa [hlen] using atReadDone) hinput ambient none
  have htime : values.sum + 2 * values.length + 1 = (encodeWords values).length + 5 := by
    rw [encodeWords_length, hlen]
  simpa only [Nat.zero_add, htime] using ht

theorem skipEquationsTrace {n : Nat} (base : Tape → List Bool)
    (prior : List (CloneGap.Equation (Fin n))) (indexSuffix suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      (some ⟨some .guard, (ambient, register), scanTapes base prior.length indexSuffix
        (encodeWords (prior.flatMap equationWords) ++ suffix)⟩) =
      some ⟨some (readStart 0), (ambient, none), scanTapes base 0 indexSuffix suffix⟩ := by
  induction prior generalizing register with
  | nil =>
    simpa only [List.flatMap_nil, List.length_nil, encodeWords, List.nil_append,
      Nat.zero_add, Function.iterate_one, advance_some, scanTapes] using
      MachineUnaryCounter.guardStep_zero .index .guard (skipLabel 0) (readStart 0)
        program rfl (Function.update base .work suffix) indexSuffix ambient register
  | cons equation prior ih =>
    have hencoding : encodeWords ((equation :: prior).flatMap equationWords) ++ suffix =
        encodeWords (equationWords equation) ++ (encodeWords (prior.flatMap equationWords) ++ suffix) := by
      simp only [List.flatMap_cons, encodeWords_append, List.append_assoc]
    have htime : (encodeWords ((equation :: prior).flatMap equationWords)).length +
        (equation :: prior).length + 1 =
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
          (encodeWords (equationWords equation)).length) + 1 := by
      simp only [List.flatMap_cons, encodeWords_append, List.length_append, List.length_cons]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1 +
        (encodeWords (equationWords equation)).length]
      (TM2.step program ⟨some .guard, (ambient, register),
        MachineUnaryCounter.counterTapes .index
          (Function.update base .work (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
          (prior.length + 1) indexSuffix⟩) = _
    rw [MachineUnaryCounter.guardStep_succ .index .guard (skipLabel 0) (readStart 0)
      program rfl]
    rw [Function.iterate_add_apply]
    have hd := discardFourTrace
      (scanTapes base prior.length indexSuffix
        (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix))
      (equationWords equation) (equationWords_length equation)
      (encodeWords (prior.flatMap equationWords) ++ suffix) (by
        rw [scanTapes_work, hencoding]) ambient
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap equationWords)).length + prior.length + 1]
      ((advance (TM2.step program))^[(encodeWords (equationWords equation)).length]
        (some ⟨some (skipLabel 0), (ambient, none), scanTapes base prior.length indexSuffix
          (encodeWords ((equation :: prior).flatMap equationWords) ++ suffix)⟩)) = _
    rw [hd, update_scanTapes_work]
    exact ih none

theorem scanReadTrace {n : Nat} (base : Tape → List Bool) (variableCount declaredEquations : Nat)
    (prior : List (CloneGap.Equation (Fin n))) (equation : CloneGap.Equation (Fin n))
    (indexSuffix suffix : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[scanSteps variableCount declaredEquations prior equation]
      (some ⟨some .headerFirst, (ambient, none), scanTapes base prior.length indexSuffix
        (encodeWords [variableCount, declaredEquations] ++
          (encodeWords (prior.flatMap equationWords) ++
            (encodeWords (equationWords equation) ++ suffix)))⟩) =
      some ⟨none, (ambient, none), outputTapes base equation indexSuffix suffix⟩ := by
  have hh := discardHeadersTrace
    (scanTapes base prior.length indexSuffix
      (encodeWords [variableCount, declaredEquations] ++
        (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))))
    variableCount declaredEquations
    (encodeWords (prior.flatMap equationWords) ++ (encodeWords (equationWords equation) ++ suffix))
    (by simp) ambient
  have hs := skipEquationsTrace base prior indexSuffix (encodeWords (equationWords equation) ++ suffix) ambient none
  have hr := readFourTrace
    (scanTapes base 0 indexSuffix (encodeWords (equationWords equation) ++ suffix))
    (equationWords equation) (equationWords_length equation) suffix (by simp) ambient
  rw [show scanSteps variableCount declaredEquations prior equation =
      ((encodeWords (equationWords equation)).length + 5 +
        ((encodeWords (prior.flatMap equationWords)).length + prior.length + 1)) +
        (variableCount + declaredEquations + 2) by unfold scanSteps; omega]
  rw [Function.iterate_add_apply, hh, update_scanTapes_work,
    Function.iterate_add_apply, hs]
  exact hr

theorem lookupWithSplitTrace (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.«variables»)))
    (equation : CloneGap.Equation (Fin F.«variables»)) (after : List (CloneGap.Equation (Fin F.«variables»)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[lookupSteps F prior equation]
      (some ⟨some .copyOut, (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩ := by
  have hbits : inputBits F = encodeWords [F.«variables», F.equations.length] ++
      (encodeWords (prior.flatMap equationWords) ++
        (encodeWords (equationWords equation) ++ encodeWords (after.flatMap equationWords))) := by
    simp only [inputBits, inputWords, encodeWords_append]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append]
  have hc := MachineCopy.copyTrace .source .work .scratch (by decide) (by decide)
    (by decide) false .copyOut .copyBack (some .headerFirst) program rfl rfl
    base hscratch ambient register
  have htapes : Function.update base .work (base .source ++ base .work) =
      scanTapes base prior.length indexSuffix (inputBits F) := by
    funext p
    cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes, hsource, hindex, hwork]
  rw [htapes, hsource] at hc
  rw [lookupSteps, Nat.add_comm, Function.iterate_add_apply, hc, hbits]
  exact scanReadTrace base F.«variables» F.equations.length prior equation indexSuffix
    (encodeWords (after.flatMap equationWords)) ambient

def lookupWithSplitInTime (F : SourceEncoding.Input) (prior : List (CloneGap.Equation (Fin F.«variables»)))
    (equation : CloneGap.Equation (Fin F.«variables»)) (after : List (CloneGap.Equation (Fin F.«variables»)))
    (hsplit : F.equations = prior ++ equation :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none),
        outputTapes base equation indexSuffix (encodeWords (after.flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) where
  steps := lookupSteps F prior equation
  evals_in_steps := lookupWithSplitTrace F prior equation after hsplit base indexSuffix
    hsource hindex hwork hscratch ambient register
  steps_le_m := by
    rw [timePolynomial_eval]
    exact lookupSteps_le_input F prior equation after hsplit

def lookupInTime (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), base⟩
      (some ⟨none, (ambient, none), outputTapes base F.equations[i.val] indexSuffix
        (encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords))⟩)
      (timePolynomial.eval (inputBits F).length) := by
  have hp : (F.equations.take i.val).length = i.val := by
    rw [List.length_take, Nat.min_eq_left i.isLt.le]
  have hs : F.equations = F.equations.take i.val ++ F.equations[i.val] :: F.equations.drop (i.val + 1) := by
    rw [List.getElem_cons_drop i.isLt, List.take_append_drop]
  apply lookupWithSplitInTime F (F.equations.take i.val) F.equations[i.val]
    (F.equations.drop (i.val + 1)) hs base indexSuffix hsource
    (by simpa only [hp] using hindex) hwork hscratch ambient register

end DFVSGames.Reduction.SourceEquationLookup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTuple
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

namespace DFVSGames.Reduction.MachineSourceTuple

open Turing DFVSGames.Foundations.Complexity
open SourceEncoding
open MachineComposition

variable {width : Nat} {Extra σ : Type}

variable [DecidableEq Extra]

theorem placed_stepAux (j : Fin width) (base : Tape width Extra → List Bool)
    (q : TM2.Stmt (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool))
    (state : (σ × Unit) × Option Bool) (localTapes : SourceEquationLookup.Tape → List Bool) :
    TM2.stepAux (placedStatement j q) state (fill j base localTapes) =
      placedConfiguration j base (TM2.stepAux q state localTapes) := by
  induction q generalizing state localTapes with
  | push k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih state _
  | peek k f next ih =>
    simpa only [placedStatement, TM2.stepAux, fill_place] using ih (f state _) localTapes
  | pop k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih (f state _) _
  | load f next ih => simpa only [placedStatement, TM2.stepAux] using ih (f state) localTapes
  | branch f yes no ihYes ihNo =>
    cases h : f state
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state localTapes
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state localTapes
  | goto f => rfl
  | halt => rfl

theorem placed_step (j : Fin width) (base : Tape width Extra → List Bool)
    (a b : TM2.Cfg (fun _ : SourceEquationLookup.Tape => Bool)
      SourceEquationLookup.Label ((σ × Unit) × Option Bool))
    (h : TM2.step SourceEquationLookup.program a = some b) :
    TM2.step program (placedConfiguration j base a) =
      some (placedConfiguration j base b) := by
  cases a with
  | mk l state localTapes =>
    cases l with
    | none => contradiction
    | some l =>
      change some (TM2.stepAux (SourceEquationLookup.program l) state localTapes) = some b at h
      cases Option.some.inj h
      change some (TM2.stepAux (placedStatement j (SourceEquationLookup.program l))
        state (fill j base localTapes)) = _
      rw [placed_stepAux]

noncomputable def placedLookupInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hindex : base .index = encodeWord i.val ++ suffix)
    (hwork : base .work = []) (hscratch : base .scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.lookup j .copyOut), ((ambient, ()), register), base⟩
      (some ⟨some (.clearWork j), ((ambient, ()), none), lookupOutput j F i base suffix⟩)
      (4 * (inputBits F).length + 8) := by
  have h := SourceEquationLookup.lookupInTime F i (base ∘ place j) suffix
    hsource hindex hwork hscratch (ambient, ()) register
  have lifted := liftExecutionInTime (TM2.step SourceEquationLookup.program) (TM2.step program)
    (placedConfiguration j base) (placed_step j base) h
  simpa only [placedConfiguration, placedLabel, fill_self,
    SourceEquationLookup.timePolynomial_eval, lookupOutput] using lifted

noncomputable def coordinateInTime (j : Fin width) (F : SourceEncoding.Input) (i : Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : base (.savedIndex j) = encodeWord i.val ++ suffix)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.copyOut j), ((ambient, ()), register), base⟩
      (some ⟨some (nextLabel j), ((ambient, ()), none), coordinateOutput j F.equations[i.val] base⟩)
      (6 * (inputBits F).length + 4 * (base (.savedIndex j)).length + 20) := by
  let copied := copiedTapes j base
  let loaded := lookupOutput j F i copied suffix
  have copyRun := MachineCopy.copyInTime (.savedIndex j) .index .copyScratch
    (by simp) (by simp) (by simp) false (.copyOut j) (.copyBack j)
    (some (.lookup j .copyOut)) program rfl rfl base hcopy (ambient, ()) register
  have copied_eq : Function.update base .index (base (.savedIndex j) ++ base .index) = copied := by
    simp [copied, copiedTapes, hindex]
  rw [copied_eq] at copyRun
  have lookupRun := placedLookupInTime j F i copied suffix
    (by simpa [copied, copiedTapes] using hsource)
    (by simpa [copied, copiedTapes] using hsavedIndex)
    (by simpa [copied, copiedTapes] using hwork)
    (by simpa [copied, copiedTapes] using hscratch) ambient none
  have workRun := MachineDrain.drainInTime .work (.clearWork j) (some (.clearIndex j))
    program rfl loaded (ambient, ()) none
  have indexRun := MachineDrain.drainInTime .index (.clearIndex j) (some (nextLabel j))
    program rfl (Function.update loaded .work []) (ambient, ()) none
  have hrun := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copyRun lookupRun)
      workRun) indexRun
  have hw : loaded .work = encodeWords ((F.equations.drop (i.val + 1)).flatMap equationWords) := by
    simp [loaded, lookupOutput, fill, SourceEquationLookup.output_work]
  have hi : (Function.update loaded .work []) .index = encodeWord 0 ++ suffix := by
    simp [loaded, lookupOutput, fill, SourceEquationLookup.output_index]
  have hc : suffix.length ≤ (base (.savedIndex j)).length := by
    rw [hsavedIndex, List.length_append]
    omega
  refine { steps := hrun.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [loaded, copied, cleanup_lookupOutput] using hrun.evals_in_steps
  · apply Nat.le_trans hrun.steps_le_m
    rw [hw, hi, List.length_append, encodeWord_length]
    have hs := suffix_length_le_input F (i.val + 1)
    omega

noncomputable def prefixInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (r : Nat) (hr : r ≤ width) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨some (labelAt r), ((ambient, ()), none), stageTapes F tuple base r⟩)
      (r * (6 * (inputBits F).length + 4 * C + 20)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < width := by omega
    let j : Fin width := ⟨r, hru⟩
    let before := stageTapes F tuple base r
    have hf (p : Tape width Extra) (hi : p ≠ .index) (hw : p ≠ .work)
        (hh : ∀ j s, p ≠ .field j s) : before p = base p :=
      stageTapes_frame F tuple base r p hi hw hh
    have hd := stageTapes_clean F tuple base r hindex hwork
    have hc : before (.savedIndex j) = base (.savedIndex j) := hf _ (by simp) (by simp) (by simp)
    have one := coordinateInTime j F (tuple j) before (suffix j)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hsource)
      (by rw [hc]; exact hsavedIndex j) hd.1 hd.2
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hscratch)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hcopy) ambient none
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((ambient, ()), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((ambient, ()), none), stageTapes F tuple base (r + 1)⟩)
        (6 * (inputBits F).length + 4 * C + 20) := by
      refine { steps := one.steps, evals_in_steps := ?_, steps_le_m := ?_ }
      · simpa only [labelAt, dite_eq_left hru, nextLabel_eq, j, stageTapes, before] using
          one.evals_in_steps
      · apply Nat.le_trans one.steps_le_m
        rw [hc]
        have hs := hsize j
        omega
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

noncomputable def loadInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool) (suffix : Fin width → List Bool) (C : Nat)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.savedIndex j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (6 * (inputBits F).length + 4 * C + 20) + 1) := by
  have prefixRun := prefixInTime F tuple base suffix C hsource hsavedIndex hsize
    hindex hwork hscratch hcopy width (Nat.le_refl _) ambient
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt width), ((ambient, ()), none), stageTapes F tuple base width⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ prefixRun doneRun

noncomputable def loadUnaryInTime (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsavedIndex : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((ambient, ()), none), base⟩
      (some ⟨none, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) := by
  have run := loadInTime F tuple base (fun _ => []) (inputBits F).length hsource
    (by simpa only [List.append_nil] using hsavedIndex)
    (by
      intro j
      rw [hsavedIndex j, encodeWord_length]
      have h := (tuple j).isLt
      have hm := equations_length_le_input F
      omega)
    hindex hwork hscratch hcopy ambient
  have he : 6 * (inputBits F).length + 4 * (inputBits F).length + 20 =
      10 * (inputBits F).length + 20 := by omega
  simpa only [he] using run

noncomputable def placedLoadUnaryInTime {Λ : Type}
    (labels : Label width → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape width Extra => Bool) Λ ((σ × Unit) × Option Bool))
    (atLabels : ∀ l, target (labels l) = MachineSubroutine.statement labels exit (program l))
    (F : SourceEncoding.Input) (tuple : Fin width → Fin F.equations.length)
    (base : Tape width Extra → List Bool)
    (hsource : base .source = inputBits F)
    (hsaved : ∀ j, base (.savedIndex j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (labelAt 0)), ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none), stageTapes F tuple base width⟩)
      (width * (10 * (inputBits F).length + 20) + 1) :=
  MachineSubroutine.execution labels exit program target atLabels
    (loadUnaryInTime F tuple base hsource hsaved hindex hwork hscratch hcopy ambient)

end DFVSGames.Reduction.MachineSourceTuple
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAddressHeaders
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
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

namespace DFVSGames.Reduction.CloneMachineAffine

open DFVSGames.Foundations.Complexity
open CloneMachineModel

theorem affineEmit_replicate_true (scale offset v : Nat) :
    (List.replicate v true).flatMap (affineEmit scale offset) =
      List.replicate (scale * v) true := by
  rw [List.flatMap_replicate]
  change (List.replicate v (List.replicate scale true)).flatten = _
  rw [List.flatten_replicate_replicate, Nat.mul_comm v scale]

theorem affineEmit_word (scale offset v : Nat) :
    (encodeWord v).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) := by
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, affineEmit_replicate_true, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * v) offset]

end DFVSGames.Reduction.CloneMachineAffine
end

section

namespace DFVSGames.Reduction.MachineAddressHeaders

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition

noncomputable section

namespace Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem evalPhaseTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (kind : Kind) (base : K → List Bool) (value : Nat)
    (hinput : base (control slots (inputControl kind)) = encodeWord value)
    (hdest : base (control slots (outputControl kind)) = [])
    (clean : WorkClean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount kind) value]
      (some ⟨some (labels (evalStart kind)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (afterEval kind)), ((ambient, ()), none),
        Function.update base (control slots (outputControl kind))
          (encodeWord ((polynomial k s d noiseCount kind).eval value))⟩ := by
  have evaluated := SourceHeaderCounts.Eval.trace (polynomial k s d noiseCount kind)
    (evalSlots slots kind) (fun label => labels (.evaluate kind label))
    (some (labels (afterEval kind))) program (fun label => atLabels (.evaluate kind label))
    base value (by simpa using hinput)
    (fun i => by simpa using clean.coefficients (coefficientBlock k s d noiseCount kind i))
    ⟨by simpa using clean.accA, by simpa using clean.accB,
      by simpa using clean.counter, by simpa using clean.scratch⟩ ambient register
  simpa only [evalStart, MachineHorner.resultTapes, evalSlots_destination, hdest, List.append_nil]
    using evaluated

theorem prepareBaseTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * n + 3 * m + 10]
      (some ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none),
        preparedBase slots base n m⟩ := by
  let t1 := Function.update base (control slots .baseValue) (encodeWord n)
  let t2 := Function.update t1 (control slots .temporary) (encodeWord m)
  let t3 := Function.update (Function.update t2 (control slots .temporary) [false])
    (control slots .baseValue) (encodeWord (m + n))
  let t4 := Function.update (Function.update t3 (control slots .temporary) [])
    (control slots .baseValue) (encodeWord (radix s d n m))
  have copyingN := MachineCopy.copyTrace (control slots .variableCount)
    (control slots .baseValue) (control slots .scratch) (by simp) (by simp) (by simp)
    false (labels .copyNOut) (labels .copyNBack) (some (labels .copyMOut)) program
    (atLabels .copyNOut) (atLabels .copyNBack) base clean.scratch (ambient, ()) register
  rw [hn, clean.baseValue, List.append_nil, encodeWord_length] at copyingN
  have copyingM := MachineCopy.copyTrace (control slots .occurrenceCount)
    (control slots .temporary) (control slots .scratch) (by simp) (by simp) (by simp)
    false (labels .copyMOut) (labels .copyMBack) (some (labels .addM)) program
    (atLabels .copyMOut) (atLabels .copyMBack) t1
    (by simpa [t1] using clean.scratch) (ambient, ()) none
  have hm1 : t1 (control slots .occurrenceCount) = encodeWord m := by simpa [t1] using hm
  have ht1 : t1 (control slots .temporary) = [] := by simpa [t1] using clean.temporary
  rw [hm1, ht1, List.append_nil, encodeWord_length] at copyingM
  have adding := MachineUnaryAddAt.addFromTapes (control slots .temporary)
    (control slots .baseValue) (by simp) (labels .addM) (some (labels .seedBase)) program
    (atLabels .addM) t2 m n [] [] (by simp [t2]) (by simp [t2, t1]) (ambient, ()) none
  have added : MachineUnaryAddAt.unaryTapes (control slots .temporary)
      (control slots .baseValue) t2 0 (m + n) [] [] = t3 := by
    simp [MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, t3, encodeWord]
  rw [added] at adding
  have seeding : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seedBase), ((ambient, ()), none), t3⟩) =
      some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none), t4⟩ := by
    change some (TM2.stepAux (program (labels .seedBase)) _ _) = _
    rw [atLabels]
    simp only [statement, TM2.stepAux]
    have htemp : t3 (control slots .temporary) = [false] := by simp [t3]
    rw [htemp]
    simp only [List.tail_cons]
    rw [MachineSubstitution.stepAux_pushWord]
    simp only [TM2.stepAux]
    have different : control slots .baseValue ≠ control slots .temporary := by simp
    rw [Function.update_of_ne different]
    have hbase : t3 (control slots .baseValue) = encodeWord (m + n) := by simp [t3]
    rw [hbase]
    have wordEq : (List.replicate (baseConstant s d) true).reverse ++ encodeWord (m + n) =
        encodeWord (radix s d n m) := by
      simp [encodeWord, List.reverse_replicate, ← List.append_assoc,
        List.replicate_append_replicate, radix, Nat.add_comm, Nat.add_assoc]
    rw [wordEq]
  have combined := trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ copyingN copyingM) adding) seeding
  have timeEq : 2 * (n + 1 + 1) + 2 * (m + 1 + 1) + (m + 1) + 1 =
      2 * n + 3 * m + 10 := by omega
  rw [timeEq] at combined
  have frame : t4 = preparedBase slots base n m := by
    funext tape
    by_cases ht : tape = control slots .temporary
    · subst tape
      simp [t4, t3, t2, t1, preparedBase, clean.temporary]
    · simp [t4, t3, t2, t1, preparedBase, Function.update_apply, ht]
      split_ifs <;> rfl
  rw [frame] at combined
  exact combined

theorem doubleTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (value : Nat)
    (hcap : base (control slots .capacity) = encodeWord value)
    (hscratch : base (control slots .scratch) = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[3 * value + 5]
      (some ⟨some (labels .doubleScan), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .alphabet), ((ambient, ()), none),
        Function.update base (control slots .reversed)
          ((encodeWord (2 * value)).reverse ++ base (control slots .reversed))⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace (control slots .capacity)
    (control slots .scratch) (control slots .reversed) (by simp) (by simp) (by simp)
    () (fun q _ => q) (fun _ : Unit => CloneMachineModel.affineEmit 2 0)
    (labels .doubleScan) (labels .doubleRestore) (fun _ symbol => labels (.doubleEmit symbol))
    (some (labels .alphabet)) program (atLabels .doubleScan)
    (by intro q symbol; cases q; exact atLabels (.doubleEmit symbol))
    (atLabels .doubleRestore) base hscratch ambient () register
  rw [hcap, CloneMachineAffine.output_eq_flatMap, CloneMachineAffine.affineEmit_word,
    Nat.zero_add, encodeWord_length] at copied
  have timeEq : 3 * (value + 1) + 2 = 3 * value + 5 := by omega
  rw [timeEq] at copied
  exact copied

theorem trace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps k s d noiseCount n m]
      (some ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩ := by
  let t1 := preparedBase slots base n m
  let t2 := Function.update t1 (control slots .capacity) (encodeWord (capacity k s d n m))
  let t3 := Function.update t2 (control slots .reversed)
    ((encodeWord (2 * capacity k s d n m)).reverse ++ t2 (control slots .reversed))
  let t4 := Function.update t3 (control slots .reversed)
    ((encodeWord (2 ^ s)).reverse ++ t3 (control slots .reversed))
  let t5 := Function.update t4 (control slots .temporary) (encodeWord (edgeCount k s d noiseCount m))
  have prepared := prepareBaseTrace slots labels exit program atLabels base n m hn hm clean ambient register
  have cw1 : WorkClean slots t1 := clean.toWorkClean.update_control .baseValue (by decide) _
  have evaluatedCap := evalPhaseTrace slots labels exit program atLabels .capacity t1 (radix s d n m)
    (by simp [t1, preparedBase, inputControl])
    (by simpa [t1, preparedBase, outputControl] using clean.capacity) cw1 ambient none
  simp only [polynomial_capacity_eval] at evaluatedCap
  change (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps
      (polynomial k s d noiseCount .capacity) (radix s d n m)]
    (some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none), t1⟩) =
    some ⟨some (labels .doubleScan), ((ambient, ()), none), t2⟩ at evaluatedCap
  have cw2 : WorkClean slots t2 := cw1.update_control .capacity (by decide) _
  have doubled := doubleTrace slots labels exit program atLabels t2 (capacity k s d n m)
    (by simp [t2]) cw2.scratch ambient none
  have alphabetStep : (advance (TM2.step program))^[1]
      (some ⟨some (labels .alphabet), ((ambient, ()), none), t3⟩) =
      some ⟨some (labels (evalStart .edges)), ((ambient, ()), none), t4⟩ := by
    change some (TM2.stepAux (program (labels .alphabet)) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (MachineSubstitution.pushWord _ _ _) _ _) = _
    rw [MachineSubstitution.stepAux_pushWord]
    rfl
  have cw3 : WorkClean slots t3 := cw2.update_control .reversed (by decide) _
  have cw4 : WorkClean slots t4 := cw3.update_control .reversed (by decide) _
  have evaluatedEdges := evalPhaseTrace slots labels exit program atLabels .edges t4 m
    (by simpa [t4, t3, t2, t1, preparedBase, inputControl] using hm)
    (by simpa [t4, t3, t2, t1, preparedBase, outputControl] using clean.temporary)
    cw4 ambient none
  simp only [polynomial_edges_eval] at evaluatedEdges
  change (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps
      (polynomial k s d noiseCount .edges) m]
    (some ⟨some (labels (evalStart .edges)), ((ambient, ()), none), t4⟩) =
    some ⟨some (labels .edgeTransfer), ((ambient, ()), none), t5⟩ at evaluatedEdges
  have transferred := MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
    (σ := σ × Unit) (control slots .temporary)
    (control slots .reversed) (by simp) id false (labels .edgeTransfer) exit program
    (atLabels .edgeTransfer) t5 (ambient, ()) none
  change (advance (TM2.step program))^[(t5 (control slots .temporary)).length + 1]
    (some ⟨some (labels .edgeTransfer), ((ambient, ()), none), t5⟩) = _ at transferred
  have ht5 : t5 (control slots .temporary) = encodeWord (edgeCount k s d noiseCount m) := by simp [t5]
  rw [ht5, encodeWord_length] at transferred
  simp only [List.map_id] at transferred
  have combined := trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _
    (trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ prepared evaluatedCap) doubled) alphabetStep) evaluatedEdges) transferred
  have timeEq : 2 * n + 3 * m + 10 +
      SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .capacity) (radix s d n m) +
      (3 * capacity k s d n m + 5) + 1 +
      SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .edges) m +
      (edgeCount k s d noiseCount m + 1 + 1) = steps k s d noiseCount n m := by
    unfold steps
    omega
  rw [timeEq] at combined
  have frame : MachineTransfer.tapesAt (control slots .temporary) (control slots .reversed)
      t5 [] ((encodeWord (edgeCount k s d noiseCount m)).reverse ++ t5 (control slots .reversed)) =
      resultTapes slots base n m := by
    funext tape
    by_cases ht : tape = control slots .temporary
    · subst tape
      simp [MachineTransfer.tapesAt, resultTapes, clean.temporary]
    · simp [MachineTransfer.tapesAt, t5, t4, t3, t2, t1, preparedBase, resultTapes,
        headerBits, encodeWords, List.reverse_append, List.append_assoc, Function.update_apply, ht]
      split_ifs <;> rfl
  rw [frame] at combined
  exact combined

def inTime (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (steps k s d noiseCount n m) where
  steps := steps k s d noiseCount n m
  evals_in_steps := trace slots labels exit program atLabels base n m hn hm clean ambient register
  steps_le_m := Nat.le_refl _

end Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type} [DecidableEq K]

def inTime (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (input : SourceEncoding.Input)
    (hinput : base (slots (.inl 0)) = SourceEncoding.inputBits input)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inl .copyOut)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes slots base input.«variables» input.equations.length⟩)
      (Arithmetic.steps k s d noiseCount input.«variables» input.equations.length +
        (3 * (SourceEncoding.inputBits input).length + 6)) := by
  have parsed := Prefix.inTime (prefixSlots slots) (fun l => labels (.inl l))
    (some (labels (.inr .copyNOut))) program (fun l => atLabels (.inl l))
    base input.«variables» input.equations.length
    (encodeWords (input.equations.flatMap SourceEncoding.equationWords))
    (by simpa [prefixSlots_apply, SourceEncoding.inputBits,
      SourceEncoding.inputWords, encodeWords, List.append_assoc] using hinput)
    clean.readCopy clean.scratch ambient register
  have hn : Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (Arithmetic.control (arithmeticSlots slots) .variableCount) = encodeWord input.«variables» := by
    change Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (prefixSlots slots 2) = _
    rw [Prefix.resultTapes_n]
    change encodeWord input.«variables» ++
      base (Arithmetic.control (arithmeticSlots slots) .variableCount) = _
    rw [clean.variableCount, List.append_nil]
  have hm : Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) =
        encodeWord input.equations.length := by
    change Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (prefixSlots slots 3) = _
    rw [Prefix.resultTapes_m]
    change encodeWord input.equations.length ++
      base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) = _
    rw [clean.occurrenceCount, List.append_nil]
  have arithmetic := Arithmetic.inTime (arithmeticSlots slots) (fun l => labels (.inr l))
    exit program (fun l => atLabels (.inr l))
    (Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length)
    input.«variables» input.equations.length hn hm
    (clean.afterPrefix input.«variables» input.equations.length) ambient none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ parsed arithmetic
  have sourceEq : base (prefixSlots slots 0) = SourceEncoding.inputBits input := hinput
  simpa only [resultTapes, sourceEq] using joined

def inPolynomialTime (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (input : SourceEncoding.Input)
    (hinput : base (slots (.inl 0)) = SourceEncoding.inputBits input)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inl .copyOut)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes slots base input.«variables» input.equations.length⟩)
      ((timePolynomial k s d noiseCount).eval (SourceEncoding.inputBits input).length) := by
  have run := inTime slots labels exit program atLabels base input hinput clean ambient register
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans run.steps_le_m
  have bound := Arithmetic.steps_le_timePolynomial k s d noiseCount
    input.«variables» input.equations.length (SourceEncoding.inputBits input).length
    (SourceEncoding.inputBits_length_ge_variables input) (SourceEncoding.inputBits_length_ge_equations input)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

end

end DFVSGames.Reduction.MachineAddressHeaders
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTemplateAddress
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
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

namespace DFVSGames.Reduction.MachineTemplateAddress

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

section Execution

variable (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
variable (place : Label tokens.length width (chosen slots) → Λ) (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ l, P (place l) = instruction tokens slots place exit l)

include atInstruction

omit [DecidableEq K] in
theorem parse_atStart (r : Nat) (hr : r < width) :
    P (place (parseLabel (SourceFieldArray.startLabel width r))) =
      SourceMachine.fieldStart (parseDestination slots r)
        (place (parseLabel (SourceFieldArray.loopLabel width r))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel, SourceFieldArray.loopLabel,
    SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem parse_atLoop (r : Nat) (hr : r < width) :
    P (place (parseLabel (SourceFieldArray.loopLabel width r))) =
      SourceMachine.fieldLoop (slots .forward) (parseDestination slots r)
        (place (parseLabel (SourceFieldArray.loopLabel width r)))
        (some (place (parseLabel (SourceFieldArray.startLabel width (r + 1))))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel, SourceFieldArray.loopLabel,
    SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem parse_atDone :
    P (place (parseLabel (SourceFieldArray.startLabel width width))) =
      SourceFieldArray.finish (slots .forward) (some (place (hornerLabel .start))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel]

theorem phaseTrace (base : K → List Bool) (B : Nat) (values : List Nat)
    (hlen : values.length = width) (clean : Clean slots base)
    (baseField : base (slots .radix) = encodeWord B)
    (wordCorrect : MachineFieldTemplate.templateOutput tokens (fun j => base (slots (.field j))) =
      encodeWords values) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step P))^[phaseSteps tokens slots base B values]
      (some ⟨some (place (emitLabel (MachineFieldTemplate.startAt tokens.length 0))),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (CanonicalAddress.radix B values)⟩ := by
  let emitted := MachineFieldTemplate.outputTapes base (slots .reversed) (encodeWords values)
  have emitRun := MachineFieldTemplate.phaseTrace tokens (fun j => slots (.field j))
    (slots .copyScratch) (slots .reversed)
    (fun _ => slots.injective.ne (by simp)) (fun _ => slots.injective.ne (by simp))
    (slots.injective.ne (by simp)) (fun l => place (emitLabel l))
    (some (place reverseLabel)) P (fun l => atInstruction (emitLabel l))
    base clean.copyScratch ((ambient, ()), register)
  rw [wordCorrect] at emitRun
  change (MachineComposition.advance (TM2.step P))^[_] _ =
    some ⟨some (place reverseLabel), ((ambient, ()), none), emitted⟩ at emitRun
  have reverseRun := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (slots .reversed) (slots .forward) (slots.injective.ne (by simp)) id false
    (place reverseLabel) (some (place (parseLabel (SourceFieldArray.startLabel width 0))))
    P (atInstruction reverseLabel) emitted (ambient, ()) none
  have reverseResult : MachineTransfer.tapesAt (slots .reversed) (slots .forward) emitted []
      ((emitted (slots .reversed)).reverse.map id ++ emitted (slots .forward)) =
      forwardTapes slots base values := by
    funext tape
    by_cases hr : tape = slots .reversed
    · subst tape
      simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt, forwardTapes,
        slots.injective.ne (show Tape.reversed ≠ Tape.forward by simp), clean.reversed]
    · by_cases hf : tape = slots .forward
      · subst tape
        simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt, forwardTapes,
          slots.injective.ne (show Tape.forward ≠ Tape.reversed by simp),
          clean.reversed, clean.forward]
      · simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt,
          forwardTapes, hr, hf]
  rw [reverseResult] at reverseRun
  have reverseLength : (emitted (slots .reversed)).length + 1 = (encodeWords values).length + 1 := by
    simp [emitted, MachineFieldTemplate.outputTapes, clean.reversed]
  rw [reverseLength] at reverseRun
  change (MachineComposition.advance (TM2.step P))^[(encodeWords values).length + 1]
    (some ⟨some (place reverseLabel), ((ambient, ()), none), emitted⟩) =
    some ⟨some (place (parseLabel (SourceFieldArray.startLabel width 0))),
      ((ambient, ()), none), forwardTapes slots base values⟩ at reverseRun
  have parseRun := SourceFieldArray.sequenceTrace (slots .forward) (parseDestination slots)
    (fun r => place (parseLabel (SourceFieldArray.startLabel width r)))
    (fun r => place (parseLabel (SourceFieldArray.loopLabel width r)))
    (some (place (hornerLabel .start))) P (forwardTapes slots base values) 0 values []
    (by
      intro r hr
      simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
      exact slots.injective.ne (by simp))
    (by intro r hr; simpa using parse_atStart tokens slots place exit P atInstruction r (by omega))
    (by intro r hr; simpa using parse_atLoop tokens slots place exit P atInstruction r (by omega))
    (by simpa only [Nat.zero_add, hlen] using parse_atDone tokens slots place exit P atInstruction)
    (by simp [forwardTapes]) (ambient, ()) none
  change (MachineComposition.advance (TM2.step P))^[values.sum + 2 * values.length + 1]
    (some ⟨some (place (parseLabel (SourceFieldArray.startLabel width 0))),
      ((ambient, ()), none), forwardTapes slots base values⟩) =
    some ⟨some (place (hornerLabel .start)), ((ambient, ()), none),
      parsedTapes slots base values⟩ at parseRun
  have hbase : parsedTapes slots base values (hornerSlots slots (.inl 0)) = encodeWord B := by
    change parsedTapes slots base values (slots .radix) = _
    rw [parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
      (fun _ => slots.injective.ne (by simp))]
    exact baseField
  have hornerRun := MachineHorner.hornerTrace (hornerSlots slots) (fun l => place (hornerLabel l))
    (MachineDrainMany.entry (chosen slots) (fun l => place (cleanupLabel l)) exit)
    P (fun l => atInstruction (hornerLabel l)) (parsedTapes slots base values) B (digits values)
    hbase (parsedTapes_digit slots base values hlen clean)
    (parsedTapes_clean slots base values hlen clean) ambient none
  have cleanupRun := MachineDrainMany.trace (chosen slots) (fun l => place (cleanupLabel l)) exit
    P (fun l => atInstruction (cleanupLabel l)) (afterHorner slots base B values) (ambient, ()) none
  rw [MachineDrainMany.finalRegister_none, cleanup_result slots base B values hlen clean] at cleanupRun
  rw [show phaseSteps tokens slots base B values =
    MachineDrainMany.steps (chosen slots) (afterHorner slots base B values) +
      (MachineHorner.steps B (digits values) width +
      ((values.sum + 2 * values.length + 1) +
      (((encodeWords values).length + 1) +
      MachineFieldTemplate.templateSteps tokens (fun j => base (slots (.field j)))))) by
        unfold phaseSteps; omega]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := MachineHorner.steps B (digits values) width)]
  rw [Function.iterate_add_apply (m := values.sum + 2 * values.length + 1)]
  rw [Function.iterate_add_apply (m := (encodeWords values).length + 1)]
  rw [emitRun, reverseRun, parseRun, hornerRun]
  exact cleanupRun

end Execution

end DFVSGames.Reduction.MachineTemplateAddress
end

section

namespace DFVSGames.Reduction.MachineAddressEdge

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

section Execution

variable (left right : List (MachineFieldTemplate.Token q)) (permutation : List Bool)
variable (slots : Tape q width ↪ K)
variable (place : Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) → Λ)
variable (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ label,
  P (place label) = instruction left right permutation slots place exit label)

include atInstruction

theorem literalStep (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (plumbing 6)), state, base⟩ =
      some ⟨exit, MachineFieldTemplate.reset state, appended slots base permutation⟩ := by
  change some (TM2.stepAux (P (place (plumbing 6))) state base) = _
  rw [atInstruction (plumbing 6)]
  simp only [instruction, plumbing, TM2.stepAux]
  rw [stepAux_pushWord]
  cases exit <;> rfl

theorem phaseTrace (base : K → List Bool) (B C : Nat)
    (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base)
    (baseField : base (addressSlots slots .radix) = encodeWord B)
    (capacityField : base (capacityTape slots) = encodeWord C)
    (leftCorrect : MachineFieldTemplate.templateOutput left
      (fun j => base (addressSlots slots (.field j))) = encodeWords leftValues)
    (rightCorrect : MachineFieldTemplate.templateOutput right
      (fun j => base (addressSlots slots (.field j))) = encodeWords rightValues)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step P))^[phaseSteps left right slots base B C leftValues rightValues]
      (some ⟨some (place (leftLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt left.length 0)))),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        appended slots base (edgeBits B C leftValues rightValues permutation)⟩ := by
  let L := CanonicalAddress.radix B leftValues
  let R := CanonicalAddress.radix B rightValues
  let afterLeft := appended slots base (encodeWord L)
  have cleanLeft : Clean slots afterLeft := Clean.appended slots base clean (encodeWord L)
  let rightResult := MachineTemplateAddress.resultTapes (addressSlots slots) afterLeft R
  let copied := Function.update rightResult (tempTape slots) (encodeWord C)
  let added := MachineUnaryAddAt.unaryTapes (tempTape slots) (workTape slots) copied 0 (C + R) [] []
  let shifted := MachineTemplateAddress.resultTapes (addressSlots slots) afterLeft (C + R)
  have leftRun := MachineTemplateAddress.phaseTrace left (addressSlots slots) (fun l => place (leftLabel l))
    (some (place (plumbing 0))) P (fun l => atInstruction (leftLabel l))
    base B leftValues leftLength clean.address baseField leftCorrect ambient register
  have transferLeft := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (workTape slots) (outputTape slots) (work_ne_output slots) id false
    (place (plumbing 0))
    (some (place (rightLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt right.length 0)))))
    P (atInstruction (plumbing 0)) (MachineTemplateAddress.resultTapes (addressSlots slots) base L) (ambient, ()) none
  rw [transfer_result slots base L clean.work] at transferLeft
  have leftWork : MachineTemplateAddress.resultTapes (addressSlots slots) base L (workTape slots) = encodeWord L := by
    simp only [addressResult_eq, Function.update_self, clean.work, List.append_nil]
  rw [leftWork] at transferLeft
  change (MachineComposition.advance (TM2.step P))^[(encodeWord L).length + 1]
    (some ⟨some (place (plumbing 0)), ((ambient, ()), none),
      MachineTemplateAddress.resultTapes (addressSlots slots) base L⟩) =
    some ⟨some (place (rightLabel (MachineTemplateAddress.emitLabel
      (MachineFieldTemplate.startAt right.length 0)))), ((ambient, ()), none), afterLeft⟩ at transferLeft
  have rightRun := MachineTemplateAddress.phaseTrace right (addressSlots slots) (fun l => place (rightLabel l))
    (some (place (plumbing 1))) P (fun l => atInstruction (rightLabel l))
    afterLeft B rightValues rightLength cleanLeft.address
    (by simpa [afterLeft] using baseField)
    (by simpa [afterLeft] using rightCorrect) ambient none
  have rightWork : rightResult (workTape slots) = encodeWord R := by
    simp only [rightResult, addressResult_eq, Function.update_self, cleanLeft.work, List.append_nil]
  have rightTemp : rightResult (tempTape slots) = [] := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · exact cleanLeft.address.forward
    · exact temp_ne_work slots
  have rightScratch : rightResult (scratchTape slots) = [] := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · exact cleanLeft.address.copyScratch
    · exact slots.injective.ne (by simp)
  have rightCapacity : rightResult (capacityTape slots) = encodeWord C := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · simpa [afterLeft] using capacityField
    · exact slots.injective.ne (by simp)
  have copyRun := MachineCopy.copyTrace (capacityTape slots) (tempTape slots) (scratchTape slots)
    (slots.injective.ne (by simp)) (slots.injective.ne (by simp))
    (slots.injective.ne (by simp)) false (place (plumbing 1)) (place (plumbing 2))
    (some (place (plumbing 3))) P (atInstruction (plumbing 1)) (atInstruction (plumbing 2))
    rightResult rightScratch (ambient, ()) none
  rw [rightCapacity, rightTemp, List.append_nil] at copyRun
  have addRun := MachineUnaryAddAt.addFromTapes (tempTape slots) (workTape slots)
    (temp_ne_work slots) (place (plumbing 3)) (some (place (plumbing 4)))
    P (atInstruction (plumbing 3)) copied C R [] []
    (by simp [copied])
    (by simp [copied, Ne.symm (temp_ne_work slots), rightWork]) (ambient, ()) none
  have addedTemp : added (tempTape slots) = encodeWord 0 := by
    simp [added, temp_ne_work]
  have drainResult : Function.update added (tempTape slots) [] = shifted := by
    funext tape
    by_cases ht : tape = tempTape slots
    · subst tape
      simp [shifted, addressResult_eq, temp_ne_work, show afterLeft (tempTape slots) = [] from cleanLeft.address.forward]
    · by_cases hw : tape = workTape slots
      · subst tape
        simp [added, MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, shifted,
          addressResult_eq, Ne.symm (temp_ne_work slots), cleanLeft.work]
      · simp [added, MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, copied,
          rightResult, shifted, addressResult_eq, ht, hw]
  have drainRun := (MachineDrain.drainInTime (tempTape slots) (place (plumbing 4))
    (some (place (plumbing 5))) P (atInstruction (plumbing 4)) added (ambient, ()) none).evals_in_steps
  change (MachineComposition.advance (TM2.step P))^[(added (tempTape slots)).length + 1]
    (some ⟨some (place (plumbing 4)), ((ambient, ()), none), added⟩) = _ at drainRun
  rw [addedTemp, drainResult] at drainRun
  have transferRight := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (workTape slots) (outputTape slots) (work_ne_output slots) id false
    (place (plumbing 5)) (some (place (plumbing 6))) P (atInstruction (plumbing 5))
    shifted (ambient, ()) none
  rw [transfer_result slots afterLeft (C + R) cleanLeft.work] at transferRight
  have shiftedWork : shifted (workTape slots) = encodeWord (C + R) := by
    simp only [shifted, addressResult_eq, Function.update_self, cleanLeft.work, List.append_nil]
  rw [shiftedWork] at transferRight
  change (MachineComposition.advance (TM2.step P))^[(encodeWord (C + R)).length + 1]
    (some ⟨some (place (plumbing 5)), ((ambient, ()), none), shifted⟩) =
    some ⟨some (place (plumbing 6)), ((ambient, ()), none),
      appended slots afterLeft (encodeWord (C + R))⟩ at transferRight
  have finishRun := literalStep left right permutation slots place exit P atInstruction
    (appended slots afterLeft (encodeWord (C + R))) ((ambient, ()), none)
  have fullSteps : phaseSteps left right slots base B C leftValues rightValues =
      1 + (((encodeWord (C + R)).length + 1) + ((encodeWord 0).length + 1 +
      ((C + 1) + (2 * ((encodeWord C).length + 1) +
      (MachineTemplateAddress.phaseSteps right (addressSlots slots) afterLeft B rightValues +
      (((encodeWord L).length + 1) + MachineTemplateAddress.phaseSteps left (addressSlots slots) base B leftValues)))))) := by
    simp only [encodeWord_length]
    dsimp only [phaseSteps, L, R, afterLeft]
    omega
  rw [fullSteps]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (encodeWord (C + R)).length + 1)]
  rw [Function.iterate_add_apply (m := (encodeWord 0).length + 1)]
  rw [Function.iterate_add_apply (m := C + 1)]
  rw [Function.iterate_add_apply (m := 2 * ((encodeWord C).length + 1))]
  rw [Function.iterate_add_apply (m := MachineTemplateAddress.phaseSteps right (addressSlots slots)
    afterLeft B rightValues)]
  rw [Function.iterate_add_apply (m := (encodeWord L).length + 1)]
  rw [leftRun, transferLeft, rightRun, copyRun, addRun, drainRun, transferRight]
  simp only [Function.iterate_one, MachineComposition.advance_some]
  rw [finishRun]
  simp only [MachineFieldTemplate.reset, afterLeft, appended_append]
  simp [edgeBits, encodeWords, L, R, List.append_assoc]

end Execution

end DFVSGames.Reduction.MachineAddressEdge
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AddressTupleLoaded
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

namespace DFVSGames.Integration.AddressTupleCleanup

open Turing DFVSGames.Reduction DFVSGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

variable {Λ : Type}

theorem trace (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[steps k s d noiseCount base]
      (some ⟨entry k s d noiseCount labels exit, (control, register), base⟩) =
    some ⟨exit, (control, MachineDrainMany.finalRegister (loadedFields k s d noiseCount) register),
      cleared k s d noiseCount base⟩ :=
  MachineDrainMany.trace (loadedFields k s d noiseCount) labels exit program atLabels
    base control register

noncomputable def execution (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : AddressMachineSpace.Tape k s d noiseCount => Bool)
      Λ (AddressMachineSpace.State k))
    (atLabels : ∀ l, program (labels l) = instruction k s d noiseCount labels exit l)
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (control : AddressMachineSpace.Control k) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry k s d noiseCount labels exit, (control, register), base⟩
      (some ⟨exit,
        (control, MachineDrainMany.finalRegister (loadedFields k s d noiseCount) register),
        cleared k s d noiseCount base⟩) (budget k s d noiseCount base) where
  steps := steps k s d noiseCount base
  evals_in_steps := trace k s d noiseCount labels exit program atLabels base control register
  steps_le_m := steps_le k s d noiseCount base

end DFVSGames.Integration.AddressTupleCleanup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineOutcomeRows
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

namespace DFVSGames.Reduction.MachineOutcomeRows

open Turing
open DFVSGames.Foundations.Complexity

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

theorem sequenceTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ))
    (atInstruction : ∀ label, P (place label) = sequenceInstruction slots rows place exit label)
    (base : K → List Bool) (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values rows base) (ambient : σ) :
    (MachineComposition.advance (TM2.step P))^[(rowCosts slots B C values rows base).sum]
      (some ⟨MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) rows place exit,
        ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineAddressEdge.appended slots base (rows.flatMap (payload B C values))⟩ := by
  have h := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) (rowResult slots B C values) (rowCost slots B C values)
    P (Invariant slots B C values rows) (fun _ => ((ambient, ()), none)) id rows
    (by
      intro row _ frame hframe
      exact Invariant.appended slots B C values rows frame hframe (payload B C values row))
    (by
      intro row hrow labels next placement frame hframe
      exact MachineAddressEdge.phaseTrace row.left row.right row.permutation slots
        labels next P placement frame B C (values row).left (values row).right
        (values row).left_length (values row).right_length hframe.clean hframe.radix
        hframe.capacity (hframe.correct row hrow).1 (hframe.correct row hrow).2 ambient none)
    place exit atInstruction base valid
  simpa only [sequence_steps, sequence_result, id_eq] using h

def sequenceEntry (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k)
    (place : Label slots rows → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) (selected rows rhs)
    (fun label => place (.inr ⟨rhs, label⟩)) exit

theorem dispatcherStep (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atDispatcher : P (place (.inl ())) = dispatcher slots rows place exit)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool) :
    TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩ =
      some ⟨sequenceEntry slots rows rhs place exit, (((rhs, ambient), ()), none), base⟩ := by
  change some (TM2.stepAux (P (place (.inl ()))) (((rhs, ambient), ()), register) base) = _
  rw [atDispatcher]
  cases rows with
  | nil => cases exit <;> rfl
  | cons row rows => rfl

theorem phaseTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    (MachineComposition.advance (TM2.step P))^[
      (rowCosts slots B C values (selected rows rhs) base).sum + 1]
      (some ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) =
      some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩ := by
  have first := dispatcherStep slots rows place exit P (atInstruction (.inl ()))
    base rhs ambient register
  have rest := sequenceTrace slots (selected rows rhs) (fun l => place (.inr ⟨rhs, l⟩))
    exit P (fun l => atInstruction (.inr ⟨rhs, l⟩)) base B C values valid (rhs, ambient)
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[_]
    (TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) = _
  rw [first]
  exact rest

def phaseInTime (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩
      (some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩)
      ((rowCosts slots B C values (selected rows rhs) base).sum + 1) where
  steps := (rowCosts slots B C values (selected rows rhs) base).sum + 1
  evals_in_steps := phaseTrace slots rows place exit P atInstruction base rhs ambient register
    B C values valid
  steps_le_m := Nat.le_refl _

end DFVSGames.Reduction.MachineOutcomeRows
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_UniformReduction
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
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

namespace DFVSGames.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration _root_.OAI.DFVSGames.Reduction.Explicit

variable {N : Type*}

theorem indexedOutcomes_factor (m k s d : Nat) (indices : List N) :
    ActualEnumeration.indexedOutcomes m k s d indices =
      (occurrenceTuples m k).flatMap (fun U => (fixedParams k s d indices).map (assemble U)) := by
  exact pairs_associate_inline_FixedOutcomes (functions (List.finRange m) k)
    (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))

theorem outputInstance_constraints (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (AddressGame.outputInstance S k g en).constraints =
      (occurrenceTuples S.occurrences k).flatMap (fun U =>
        (fixedParams k s d en.indices).map (fun p =>
          AddressGame.addressEdge S k g (assemble U p))) := by
  change (ActualEnumeration.indexedOutcomes S.occurrences k s d en.indices).map
    (AddressGame.addressEdge S k g) = _
  rw [indexedOutcomes_factor]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

theorem tableOutput_constraints (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    (AddressGame.tableOutput S k T).constraints =
      (occurrenceTuples S.occurrences k).flatMap (fun U =>
        (tableParams k T).map (fun p => AddressGame.addressEdge S k
          (Integration.TableReduction.tableSkeleton T) (assemble U p))) :=
  outputInstance_constraints S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

end DFVSGames.Reduction.FixedOutcomes
end

section

namespace DFVSGames.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

theorem rightMap_actual (S : Source) {k s d : Nat} (T : NoiseTables.Table s d)
    (U : ActualGame.Question S k) (p : Parameter k T) :
    rightMap T p =
      (ActualGame.rightQuery S k (TableReduction.tableSkeleton T) (FixedOutcomes.assemble U p)).2 := rfl

theorem payload_row_actual (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (U : ActualGame.Question S k) (p : Parameter k T) :
    MachineOutcomeRows.payload
        (CanonicalAddress.base S.«variables» S.occurrences s d) (AddressGame.bodyCapacity S k s d)
        (values (CanonicalBodyTemplate.sourceFields U (ActualGame.names S)))
        (row T p (rhsBits S U)) =
      encodeWords (constraintWords (AddressGame.addressEdge S k (TableReduction.tableSkeleton T)
        (FixedOutcomes.assemble U p))) := by
  rw [payload_row, bitVector_rhsBits, rightMap_actual S T U p]
  exact (AddressByteSemantics.addressEdge_bits S k (TableReduction.tableSkeleton T)
    (FixedOutcomes.assemble U p)).symm

theorem tuplePayload_actual (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (U : ActualGame.Question S k) :
    (MachineOutcomeRows.selected (rows k T) (rhsBits S U)).flatMap
        (MachineOutcomeRows.payload
          (CanonicalAddress.base S.«variables» S.occurrences s d) (AddressGame.bodyCapacity S k s d)
          (values (CanonicalBodyTemplate.sourceFields U (ActualGame.names S)))) =
      tupleBits S k T U := by
  rw [selected_rows, List.flatMap_map]
  simp only [payload_row_actual, tupleBits]
  rfl

theorem gameBits_factor (S : Source) (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    gameBits (AddressGame.tableOutput S k T) =
      encodeWords [(AddressGame.tableOutput S k T).vertices, 2^s,
        (AddressGame.tableOutput S k T).constraints.length] ++
      (FixedOutcomes.occurrenceTuples S.occurrences k).flatMap (tupleBits S k T) := by
  rw [gameBits, gameWords, encodeWords_append, encodeWords_flatMap_inline_AddressOutcomeSpecs]
  congr 1
  change (AddressGame.tableOutput S k T).constraints.flatMap
    (fun edge : Foundations.Target.Constraint (AddressGame.vertexCount S k s d) (2^s) =>
      encodeWords (constraintWords edge)) = _
  rw [FixedOutcomes.tableOutput_constraints]
  dsimp only [TableReduction.tableSkeleton, NoiseTables.Table.gadget]
  simp only [List.flatMap_assoc, List.flatMap_map]
  rfl

end DFVSGames.Reduction.AddressOutcomeSpecs
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AddressTupleBody
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

namespace DFVSGames.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

variable {rows : Rows k}

noncomputable def run (rows : Rows k) (labels : Label k s d noiseCount rows → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction rows labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (oldRhs : Fin k → Bool) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (valid : MachineOutcomeRows.Invariant (Slots k s d noiseCount) B C values
      (MachineOutcomeRows.selected rows (rhs F tuple)) (loaded F tuple base)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main rows)), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, finalTapes rows B C values F tuple base⟩)
      (budget rows B C values F tuple base) := by
  have sourceRun := MachineSourceTuple.placedLoadUnaryInTime
    (sourceLabels labels) (some (rhsLabel labels)) P (fun l => atLabels (.inl l))
    F tuple base ready.source ready.saved ready.index ready.work ready.scratch ready.copy (oldRhs, ())
  have rhsRun := MachineRhsLoad.loadInTime (rhsField k s d noiseCount)
    (rhsLabel labels) (some (rowLabels labels (.inl ()))) P (atLabels (.inr (.inl ())))
    (((oldRhs, ()), ()), none) (loaded F tuple base) (rhs F tuple) (fun _ => [])
    (by
      intro j
      change loaded F tuple base (MachineSourceTuple.rhsField j) = _
      rw [loaded, MachineSourceTuple.output_rhs]
      change encodeWord (if F.equations[(tuple j).val].rhs then 1 else 0) ++
        base (.field j 3) = _
      rw [ready.fields j 3]
      rfl)
  have rowsRun := MachineOutcomeRows.phaseInTime (Slots k s d noiseCount) rows
    (rowLabels labels)
    (AddressTupleCleanup.entry k s d noiseCount (cleanupLabels labels) (some (resetLabel labels)))
    P (fun l => atLabels (.inr (.inr (.inl l))))
    (loaded F tuple base) (rhs F tuple) () none B C values valid
  have cleanupRun := AddressTupleCleanup.execution k s d noiseCount
    (cleanupLabels labels) (some (resetLabel labels)) P
    (fun l => atLabels (.inr (.inr (.inr (.inl l)))))
    (emitted rows B C values F tuple base) (((rhs F tuple), ()), ()) none
  simp only [MachineDrainMany.finalRegister_none] at cleanupRun
  have resetRun : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (resetLabel labels), ((((rhs F tuple), ()), ()), none),
        finalTapes rows B C values F tuple base⟩
      (some ⟨exit, initialState k, finalTapes rows B C values F tuple base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step P ⟨some (resetLabel labels), _, _⟩ = _
    change some (TM2.stepAux (P (resetLabel labels)) _ _) = _
    rw [show P (resetLabel labels) = reset exit from atLabels (.inr (.inr (.inr (.inr ()))))]
    cases exit <;> rfl
  have first := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ sourceRun rhsRun
  have second := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ first rowsRun
  have third := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ second cleanupRun
  have last := StateTransition.EvalsToInTime.trans (TM2.step P) _ _ _ _ _ third resetRun
  refine { steps := last.steps, evals_in_steps := last.evals_in_steps, steps_le_m := ?_ }
  exact last.steps_le_m.trans (by dsimp only [budget]; omega)

theorem tupleBits_actual (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (T : NoiseTables.Table s d) :
    tupleBits (AddressOutcomeSpecs.rows k T)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple =
      AddressOutcomeSpecs.tupleBits (source F) k T tuple := by
  unfold tupleBits
  rw [rhs_eq_actual, canonicalValues_eq_actual]
  exact AddressOutcomeSpecs.tuplePayload_actual (source F) k T tuple

noncomputable def run_fixed_rows (T : NoiseTables.Table s d)
    (labels : Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool) (B C : Nat)
    (hB : base (headerTape k s d noiseCount .baseValue) = encodeWord B)
    (hC : base (headerTape k s d noiseCount .capacity) = encodeWord C) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k,
        finalTapes (AddressOutcomeSpecs.rows k T) B C
          (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base⟩)
      (budget (AddressOutcomeSpecs.rows k T) B C
        (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base) :=
  run (AddressOutcomeSpecs.rows k T) labels exit P atLabels F tuple base ready oldRhs B C
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
    (actualInvariant F tuple T base ready clean B C hB hC)

noncomputable def run_actual (T : NoiseTables.Table s d)
    (labels : Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      (budget (AddressOutcomeSpecs.rows k T)
        (CanonicalAddress.base F.«variables» F.equations.length s d)
        (AddressGame.bodyCapacity (source F) k s d)
        (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base) := by
  have actual := run_fixed_rows T labels exit P atLabels F tuple base ready clean oldRhs
    (CanonicalAddress.base F.«variables» F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d) hB hC
  rw [finalTapes_eq _ _ _ _ F tuple base ready, tupleBits_actual] at actual
  exact actual

end DFVSGames.Integration.AddressTupleBody
end

section

namespace DFVSGames.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration
open MachineComposition

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

theorem accumulator_ne_output : accumulator k T ≠ output k T :=
  AddressMachineSpace.headerTape_ne_finalOutput k s d T.vectors.length .reversed

theorem clearKeys_covers (tape : Tape k T) (ha : tape ≠ accumulator k T)
    (ho : tape ≠ output k T) : tape ∈ clearKeys k T := (mem_clearKeys k T tape).2 ⟨ha,ho⟩

theorem finishStartStep (state : State k) (base : Tape k T → List Bool) :
    TM2.step (program k T) ⟨some (finishStart k T),state,base⟩ =
      some ⟨SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T),state,base⟩ := by
  change some (TM2.stepAux (MachineFieldTemplate.jump
    (SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T))) state base) = _
  cases SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T) <;> rfl

def finishStartInTime (state : State k) (base : Tape k T → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program k T))
      ⟨some (finishStart k T),state,base⟩
      (some ⟨SourceRuntimeFinish.entry (clearKeys k T) (finishLabels k T),state,base⟩) 1 where
  steps := 1
  evals_in_steps := finishStartStep k T state base
  steps_le_m := Nat.le_refl _

theorem initList_eq (bits : List Bool) : initList (machine k T) bits =
    ⟨some (start k T),AddressMachineSpace.initialState k,inputTapes k T bits⟩ := by
  change (⟨some (start k T),AddressMachineSpace.initialState k,
    (initList (machine k T) bits).stk⟩ : (machine k T).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨some (start k T),AddressMachineSpace.initialState k,tapes⟩ : (machine k T).Cfg))
  dsimp only [machine]
  funext tape
  by_cases h : tape = .source
  · subst tape; simp [initList,inputTapes]
  · simp [initList,inputTapes,h]

theorem haltList_eq (bits : List Bool) : haltList (machine k T) bits =
    ⟨none,AddressMachineSpace.initialState k,outputTapes k T bits⟩ := by
  change (⟨none,AddressMachineSpace.initialState k,
    (haltList (machine k T) bits).stk⟩ : (machine k T).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨none,AddressMachineSpace.initialState k,tapes⟩ : (machine k T).Cfg))
  dsimp only [machine]
  funext tape
  by_cases h : tape = output k T
  · subst tape; simp [haltList,outputTapes,SourceRuntimeFinish.canonicalTapes]
  · simp [haltList,outputTapes,SourceRuntimeFinish.canonicalTapes,h]

end
end DFVSGames.Reduction.AddressMachineProgram
end

section

namespace DFVSGames.Reduction.AddressOdometerSchedule

open Turing
open DFVSGames.Foundations.Complexity MachineTupleOdometer
open DFVSGames.Foundations.Hastad
open MachineTransfer

noncomputable section

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def currentAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then current k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

def remainingAt (k s d noiseCount i : Nat) : Tape k s d noiseCount :=
  if h : i < k then remaining k s d noiseCount ⟨i, h⟩ else accumulator k s d noiseCount

theorem setDigits_setAcc (m : Nat) {q : Nat} (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc base bits) = setAcc (setDigits m digits base) bits := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [setDigits_other m digits _ tape hc hr, setAcc, ha]

theorem putDigit_setAcc (j : Fin k) (base : Tape k s d noiseCount → List Bool)
    (a r : Nat) (bits : List Bool) :
    putDigit j (setAcc base bits) a r = setAcc (putDigit j base a r) bits := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i; simp [setAcc]
  · intro i; simp [setAcc]
  · intro tape hc hr
    by_cases ha : tape = accumulator k s d noiseCount
    · subst tape; simp
    · simp [putDigit_other j _ a r tape (hc j) (hr j), setAcc, ha]

theorem setDigits_putDigit (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (base : Tape k s d noiseCount → List Bool) (a r : Nat) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a r := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro i
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hne]
    · by_cases he : i = ⟨q, hq⟩ <;> simp [hi, he]
  · intro tape hc hr
    simp [setDigits_other m digits _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m (Fin.snoc digits a) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) a (m - 1 - a) := by
  funext tape
  apply digitCases_inline_AddressOdometerSchedule tape
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro i
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [hi, hi', hne]
  · intro tape hc hr
    simp [setDigits_other m _ _ tape hc hr, putDigit_other _ _ _ _ tape (hc _) (hr _)]

theorem setDigits_snoc_base (m q : Nat) (hq : q < k) (digits : Fin q → Nat)
    (a : Nat) (base : Tape k s d noiseCount → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base a (m - 1 - a)) =
      setDigits m (Fin.snoc digits a) base := by
  rw [setDigits_putDigit, setDigits_snoc]

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

theorem blockPrefix_all {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) :
    blockPrefix (blocks bits) m = allBits bits := by
  rw [blockPrefix_eq_ofFn]
  simp only [blocks, Fin.isLt, ↓reduceDIte, allBits, tupleOrder_snoc]
  simp only [List.flatMap_assoc, List.flatMap_map]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ)
    {q : ℕ} (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc base ((bits c).reverse ++ output))))

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (digit : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c digit i).val) =
      Fin.snoc (fun i => (c i).val) digit.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ k)
    (base : Tape k s d noiseCount → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (accumulator k s d noiseCount))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt k s d noiseCount)
      (remaining := remainingAt k s d noiseCount) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical base bits) count rfl rfl hrun
    refine ⟨tree, ?_⟩
    unfold NestedCycle.LeafBound
    exact hcount
  | succ q ih =>
    have hqu : q < k := by omega
    let schedule : CycleSchedule (Tape k s d noiseCount) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (accumulator k s d noiseCount))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
            (checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
              (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
              schedule.ambient schedule.register schedule.base), tree.LeafBound B := by
      let digit : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c digit)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (accumulator k s d noiseCount)))
        digit.val (m - 1 - digit.val)
      have hrem : m - 1 - digit.val = r.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = digit.val := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = digit.val + 1 := by
        dsimp [digit, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, digit.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c digit) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            bodyLabel (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical childBase childBits =
          checkConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
            (next q) (m - 1) r.val schedule.currentSuffix schedule.remainingSuffix
            schedule.ambient schedule.register schedule.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, schedule, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_accumulator, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) schedule children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, schedule,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
        (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base =
        finalConfiguration (next (q + 1)) canonical base bits := by
      simp only [cycleExit, finalConfiguration, configuration, schedule, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt k s d noiseCount) (remainingAt k s d noiseCount)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          bodyLabel (m - 1) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base)
        (cycleExit (currentAt k s d noiseCount q) (remainingAt k s d noiseCount q)
          (next (q + 1)) (m - 1) schedule.currentSuffix schedule.remainingSuffix schedule.ambient schedule.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape k s d noiseCount => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ)
    (positive : 0 < m) (B : ℕ) (base : Tape k s d noiseCount → List Bool)
    (bits : (Fin k → Fin m) → List Bool)
    (atCheck : ∀ i, i < k → program (next i) =
      increment (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < k → program (resetLabel i) =
      reset (currentAt k s d noiseCount i) (remainingAt k s d noiseCount i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) k bodyLabel canonical base)
      (some (finalConfiguration (next k) canonical base bits))
      ((B + 2 * k) * m ^ k)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical
    positive B k (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

end
end DFVSGames.Reduction.AddressOdometerSchedule
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_AddressMachineInitial
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
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

namespace DFVSGames.Reduction.AddressMachineInitial

open Turing DFVSGames.Foundations.Complexity

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

theorem input_headerClean (F : SourceEncoding.Input) :
    MachineAddressHeaders.Clean (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
      (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)) := by
  refine {
    accA := input_header_inline_AddressMachineInitial k T F .accA
    accB := input_header_inline_AddressMachineInitial k T F .accB
    counter := input_header_inline_AddressMachineInitial k T F .counter
    scratch := input_header_inline_AddressMachineInitial k T F .scratch
    coefficients := ?_
    baseValue := input_header_inline_AddressMachineInitial k T F .baseValue
    capacity := input_header_inline_AddressMachineInitial k T F .capacity
    temporary := input_header_inline_AddressMachineInitial k T F .temporary
    readCopy := ?_
    variableCount := input_header_inline_AddressMachineInitial k T F .variableCount
    occurrenceCount := input_header_inline_AddressMachineInitial k T F .occurrenceCount }
  · intro i
    change AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)
      (.extra (.inl (.inr i))) = []
    exact AddressMachineProgram.inputTapes_other k T _ _ (by simp)
  · exact AddressMachineProgram.inputTapes_other k T _ .work (by simp)

def inTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits F))
      (some ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k,
        initialized k T F⟩)
      ((MachineAddressHeaders.timePolynomial k s d T.vectors.length).eval
        (SourceEncoding.inputBits F).length + k * (2 * (SourceEncoding.inputBits F).length + 6) + 1) := by
  have header := MachineAddressHeaders.inPolynomialTime
    (AddressMachineSpace.fullHeaderSlots k s d T.vectors.length)
    (AddressMachineProgram.headerLabels k T) (some (AddressMachineProgram.initializeStart k T))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atHeader k T)
    (AddressMachineProgram.inputTapes k T (SourceEncoding.inputBits F)) F
    (AddressMachineProgram.inputTapes_source k T _) (input_headerClean k T F)
    (AddressMachineSpace.initialState k).1.1 none
  have digits := MachineOdometerInit.initializeInTime
    (AddressMachineSpace.odometerSlots k s d T.vectors.length)
    (AddressMachineSpace.odometerSlots k s d T.vectors.length).injective
    (AddressMachineProgram.initializeLabels k T) (some (AddressMachineProgram.bodyStart k T))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atInitialize k T)
    F.equations.length (List.length_pos_iff.mpr F.nonempty) (afterHeaders k T F)
    (afterHeaders_occurrences k T F) (afterHeaders_current k T F)
    (afterHeaders_remaining k T F) (afterHeaders_copyScratch k T F)
    (AddressMachineSpace.initialState k).1
  have run := StateTransition.EvalsToInTime.trans (AddressMachineProgram.machine k T).step
    _ _ _ _ _ header digits
  refine { steps := run.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · rw [AddressMachineProgram.initList_eq]
    exact run.evals_in_steps
  · apply Nat.le_trans run.steps_le_m
    have hm := SourceEncoding.inputBits_length_ge_equations F
    have hmul := Nat.mul_le_mul_left k (show 2 * F.equations.length + 6 ≤
      2 * (SourceEncoding.inputBits F).length + 6 by omega)
    omega

def timePolynomial : Polynomial Nat :=
  MachineAddressHeaders.timePolynomial k s d T.vectors.length +
    Polynomial.C k * (Polynomial.C 2 * Polynomial.X + Polynomial.C 6) + Polynomial.C 1

theorem timePolynomial_eval (N : Nat) :
    (timePolynomial k T).eval N =
      (MachineAddressHeaders.timePolynomial k s d T.vectors.length).eval N +
        k * (2 * N + 6) + 1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

def inPolynomialTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits F))
      (some ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k,
        initialized k T F⟩)
      ((timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  rw [timePolynomial_eval]
  exact inTime k T F

end
end DFVSGames.Reduction.AddressMachineInitial
end

section

namespace DFVSGames.Integration.AddressTupleBudget

open Reduction Foundations.Complexity
open AddressTupleBody

variable {k s d noiseCount : Nat}

theorem source_counts_le (F : SourceEncoding.Input) :
    F.«variables»+F.equations.length ≤ (SourceEncoding.inputBits F).length := by
  rw [SourceEncoding.inputBits_length]
  omega

theorem radix_le (F : SourceEncoding.Input) (s d : Nat) :
    CanonicalAddress.base F.«variables» F.equations.length s d ≤
      radixBound s d (SourceEncoding.inputBits F).length := by
  have h := source_counts_le F
  simp only [CanonicalAddress.base_eq, radixBound]
  omega

theorem radix_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    CanonicalAddress.base F.«variables» F.equations.length s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := radix_le F s d
  unfold magnitude
  omega

theorem capacity_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    AddressGame.bodyCapacity (source F) k s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := Nat.pow_le_pow_left (radix_le F s d) (1+9*k)
  change (CanonicalAddress.base F.«variables» F.equations.length s d)^(1+9*k) ≤ _
  unfold magnitude
  omega

theorem canonicalValues_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    AddressTupleLoaded.canonicalValues F tuple j slot ≤
      (SourceEncoding.inputBits F).length := by
  rw [canonicalValues_eq_actual]
  unfold CanonicalBodyTemplate.sourceFields CanonicalBodyTemplate.recordFields
  split_ifs with h
  · have hname := (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).isLt
    have hvars := SourceEncoding.inputBits_length_ge_variables F
    change _ < F.«variables» at hname
    change (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).val ≤
      (SourceEncoding.inputBits F).length
    exact (Nat.le_of_lt hname).trans hvars
  · have hocc := (tuple j).isLt
    have hcount := SourceEncoding.inputBits_length_ge_equations F
    omega

theorem loaded_fields_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (i : Fin (4*k)) :
    ((loaded F tuple base) (MachineAddressEdge.addressSlots
      (Slots k s d noiseCount) (.field i))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have fields := AddressTupleLoaded.loaded_savedFields F tuple base ready.saved ready.fields
  have atField := congrFun fields i
  change loaded F tuple base (MachineAddressEdge.addressSlots
    (Slots k s d noiseCount) (.field i)) = _ at atField
  rw [atField]
  simp only [CanonicalBodyMachine.savedFields, encodeWord_length]
  exact (Nat.add_le_add_right (canonicalValues_le F tuple _ _) 1).trans
    (field_length_le_magnitude k s d _)

theorem queryWords_lt_radix (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (w : Nat) (hw : w ∈ AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) :
    w < CanonicalAddress.base F.«variables» F.equations.length s d := by
  rw [canonicalValues_eq_actual, rhs_eq_actual] at hw
  change w ∈ AddressByteSemantics.queryWords
    (CanonicalBodyTemplate.sourceFields (m := (source F).occurrences) tuple
      (ActualGame.names (source F))) X (fun j => ActualGame.rhs (source F) (tuple j)) at hw
  rw [AddressByteSemantics.queryWords_actual (source F) (tuple,X)] at hw
  exact CanonicalAddress.bodyWords_lt_base _ w hw

theorem queryWords_encoded_length_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d) :
    (encodeWords (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hwords := encodeWords_length_le
    (AddressByteSemantics.queryWords (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))
    (radixBound s d (SourceEncoding.inputBits F).length)
    (fun w hw => (Nat.le_of_lt (queryWords_lt_radix F tuple X w hw)).trans (radix_le F s d))
  rw [AddressByteSemantics.queryWords_length] at hwords
  unfold magnitude
  omega

theorem queryWords_digits_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (i : Nat) (hi : i < 1+9*k) :
    MachineTemplateAddress.digits (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) i ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hi' : i < (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))).length := by
    simpa only [AddressByteSemantics.queryWords_length] using hi
  simp only [MachineTemplateAddress.digits, List.getElem?_eq_getElem hi', Option.getD_some]
  exact (Nat.le_of_lt (queryWords_lt_radix F tuple X _ (List.getElem_mem hi'))).trans
    (radix_le_magnitude F k s d)

theorem selected_values_bound (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d) :
    ∀ row ∈ MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple),
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) := by
  rw [AddressOutcomeSpecs.selected_rows]
  intro row member
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
  simp only [AddressOutcomeSpecs.values_row_left, AddressOutcomeSpecs.values_row_right]
  exact ⟨queryWords_encoded_length_le_magnitude F tuple p.1,
    queryWords_encoded_length_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p),
    queryWords_digits_le_magnitude F tuple p.1,
    queryWords_digits_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p)⟩

noncomputable def rowPolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  Polynomial.C (2^((2*k+1)*(s+d+1))*T.vectors.length) *
    MachineAddressEdge.timePolynomial (1+9*k) (1+9*k) (1+9*k) + 1

theorem selected_polynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (b : Fin k → Bool) (M : Nat) :
    (MachineOutcomeRows.timePolynomial
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) b)).eval M =
        (rowPolynomial k T).eval M := by
  simp only [MachineOutcomeRows.timePolynomial, AddressOutcomeSpecs.selected_rows,
    List.map_map, Function.comp_def, AddressOutcomeSpecs.row_left_length,
    AddressOutcomeSpecs.row_right_length, Polynomial.eval_add, Polynomial.eval_one,
    eval_sum_constant_inline_AddressTupleBudget, FixedOutcomes.tableParams_length, rowPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem rows_budget_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    (MachineOutcomeRows.rowCosts (Slots k s d noiseCount)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
      (loaded F tuple base)).sum+1 ≤
        (rowPolynomial k T).eval (magnitude k s d (SourceEncoding.inputBits F).length) := by
  have h := MachineOutcomeRows.phaseCost_le_timePolynomial (Slots k s d noiseCount)
    (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
    (loaded F tuple base) _ _
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
    (magnitude k s d (SourceEncoding.inputBits F).length)
    (AddressTupleLoaded.loaded_clean F tuple base clean)
    (loaded_fields_le_magnitude F tuple base ready)
    (radix_le_magnitude F k s d) (capacity_le_magnitude F k s d)
    (selected_values_bound F tuple T)
  simpa only [selected_polynomial_eval] using h

theorem physicalField_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) ≤
      (SourceEncoding.inputBits F).length := by
  have hv := SourceEncoding.inputBits_length_ge_variables F
  have hl := SourceEncoding.inputBits_length F
  have h₁ := F.equations[(tuple j).val].first.isLt
  have h₂ := F.equations[(tuple j).val].second.isLt
  have h₃ := F.equations[(tuple j).val].third.isLt
  fin_cases slot <;>
    simp only [SourceEncoding.equationWords, List.getElem_cons_zero,
      List.getElem_cons_succ] <;> (try split_ifs) <;> omega

theorem cleanup_budget_le (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base) :
    AddressTupleCleanup.budget k s d noiseCount (emitted rows B C values F tuple base) ≤
      4*k*((SourceEncoding.inputBits F).length+2) := by
  have h := lengthSum_le_of_mem_inline_AddressTupleBudget (AddressTupleCleanup.loadedFields k s d noiseCount)
    (emitted rows B C values F tuple base) ((SourceEncoding.inputBits F).length+1) (by
      intro tape member
      obtain ⟨j, slot, rfl⟩ :=
        (AddressTupleCleanup.mem_loadedFields k s d noiseCount tape).mp member
      rw [emitted, MachineAddressEdge.appended_other]
      · rw [loaded, AddressTupleLoaded.loaded_field F tuple base ready.fields, encodeWord_length]
        exact Nat.add_le_add_right (physicalField_le F tuple j slot) 1
      · rw [AddressMachineSpace.addressSlots_output]
        simp [AddressMachineSpace.headerTape])
  rw [AddressTupleCleanup.loadedFields_length] at h
  change MachineDrainMany.lengthSum _ _ + 4*k ≤ _
  calc
    _ ≤ 4*k*((SourceEncoding.inputBits F).length+1)+4*k := Nat.add_le_add_right h _
    _ = 4*k*((SourceEncoding.inputBits F).length+2) := by ring

noncomputable def timePolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  (Polynomial.C k*(Polynomial.C 10*Polynomial.X+Polynomial.C 20)+1)+1+
    (rowPolynomial k T).comp (magnitudePolynomial k s d)+
    Polynomial.C (4*k)*(Polynomial.X+Polynomial.C 2)+1

theorem timePolynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) (L : Nat) :
    (timePolynomial k T).eval L =
      (k*(10*L+20)+1)+1+(rowPolynomial k T).eval (magnitude k s d L)+4*k*(L+2)+1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, magnitudePolynomial_eval]

theorem budget_le_timePolynomial (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    AddressTupleBody.budget (AddressOutcomeSpecs.rows k T)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ≤
        (timePolynomial k T).eval (SourceEncoding.inputBits F).length := by
  have rowsBound := rows_budget_le F tuple T base ready clean
  have cleanupBound := cleanup_budget_le (AddressOutcomeSpecs.rows k T)
    (CanonicalAddress.base F.«variables» F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d)
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ready
  rw [AddressTupleBody.budget, timePolynomial_eval]
  omega

end DFVSGames.Integration.AddressTupleBudget
end

section

namespace DFVSGames.Integration.AddressTuplePolynomial

open Turing Reduction Foundations.Complexity
open AddressTupleBody AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

noncomputable def run_actual (T : NoiseTables.Table s d)
    (labels : AddressTupleBody.Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : AddressTupleBody.Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀ l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : AddressTupleBody.Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have actual := AddressTupleBody.run_actual T labels exit P atLabels F tuple base
    ready clean oldRhs hB hC
  exact {
    steps := actual.steps
    evals_in_steps := actual.evals_in_steps
    steps_le_m := actual.steps_le_m.trans
      (AddressTupleBudget.budget_le_timePolynomial F tuple T base ready clean)
  }

end DFVSGames.Integration.AddressTuplePolynomial
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_OutputSize
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
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

namespace DFVSGames.Reduction.AddressOutputSize

open ActualSource
open DFVSGames.Integration
open DFVSGames.Foundations

variable {s d : Nat}

theorem table_constraints_eq (S : Source) (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput S k T).constraints.length =
      Explicit.edgeCount S.occurrences k (s + d) T.vectors.length := by
  unfold AddressGame.tableOutput
  erw [AddressGame.outputInstance_length]
  simp only [TableReduction.tableEnumeration]
  erw [List.length_finRange]

end DFVSGames.Reduction.AddressOutputSize
end

section

namespace DFVSGames.Reduction.AddressMachineLoop

open Turing Foundations.Complexity Integration

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

theorem stateTapes_ready (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    AddressTupleBody.Ready F (OccurrenceTupleOrder.readCoordinates digits)
      (stateTapes k T F digits output) := by
  constructor
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_source k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j
    exact stateTapes_savedIndex k T F digits output j
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_index k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_work k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_scratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_copyScratch k T F
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]
  · intro j slot
    rw [stateTapes_frame]
    · exact AddressMachineInitial.initialized_field k T F j slot
    all_goals simp [AddressMachineSpace.current, AddressMachineSpace.remaining, AddressMachineSpace.headerTape]

theorem stateTapes_clean (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    MachineAddressEdge.Clean (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) := by
  constructor
  · constructor
    · exact stateTapes_private k T F digits output .reversed
    · exact stateTapes_private k T F digits output .forward
    · exact stateTapes_private k T F digits output .copyScratch
    · exact stateTapes_private k T F digits output .accA
    · exact stateTapes_private k T F digits output .accB
    · exact stateTapes_private k T F digits output .counter
    · exact stateTapes_private k T F digits output .hornerScratch
    · intro j; exact stateTapes_private k T F digits output (.digit j)
  · exact stateTapes_private k T F digits output .output

theorem stateTapes_base (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_base]
  congr 1
  simp [MachineAddressHeaders.radix, MachineAddressHeaders.baseConstant,
    CanonicalAddress.base_eq, Nat.add_assoc]

theorem stateTapes_capacity (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output : List Bool) :
    stateTapes k T F digits output (AddressMachineSpace.headerTape k s d T.vectors.length .capacity) =
      encodeWord (AddressGame.bodyCapacity (AddressTupleBody.source F) k s d) := by
  rw [stateTapes_header _ _ _ _ _ _ (by decide), AddressMachineInitial.initialized_capacity]
  congr 1
  change MachineAddressHeaders.capacity k s d F.«variables» F.equations.length =
    CanonicalAddress.capacity F.«variables» F.equations.length k s d
  simp [MachineAddressHeaders.capacity, MachineAddressHeaders.radix,
    MachineAddressHeaders.baseConstant, CanonicalAddress.capacity,
    CanonicalAddress.base_eq, Nat.add_assoc]

theorem appended_stateTapes (F : SourceEncoding.Input)
    (digits : Fin k → Fin F.equations.length) (output payload : List Bool) :
    MachineAddressEdge.appended (AddressMachineSpace.addressEdgeSlots k s d T.vectors.length)
      (stateTapes k T F digits output) payload =
      stateTapes k T F digits (payload.reverse ++ output) := by
  change AddressOdometerSchedule.setAcc (stateTapes k T F digits output)
    (payload.reverse ++ stateTapes k T F digits output
      (AddressOdometerSchedule.accumulator k s d T.vectors.length)) = _
  simp only [stateTapes, AddressOdometerSchedule.setDigits_accumulator, AddressOdometerSchedule.setAcc_apply]
  rw [AddressOdometerSchedule.setDigits_setAcc, AddressOdometerSchedule.setAcc_setAcc,
    ← AddressOdometerSchedule.setDigits_setAcc]

theorem bodyTrace (F : SourceEncoding.Input) :
    AddressOdometerSchedule.BodyTrace (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F)
      (bits k T F) ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  intro digits output
  let base := stateTapes k T F digits output
  have ready := stateTapes_ready k T F digits output
  have clean := stateTapes_clean k T F digits output
  have actual := AddressTuplePolynomial.run_actual T (AddressMachineProgram.bodyLabels k T) (some (AddressMachineProgram.next k T 0))
    (AddressMachineProgram.program k T) (AddressMachineProgram.atBody k T) F
    (OccurrenceTupleOrder.readCoordinates digits) base ready clean (fun _ => false)
    (stateTapes_base k T F digits output) (stateTapes_capacity k T F digits output)
  refine ⟨actual.steps, actual.steps_le_m, ?_⟩
  have hemit : MachineAddressEdge.appended (AddressTupleBody.Slots k s d T.vectors.length)
      base (AddressOutcomeSpecs.tupleBits (AddressTupleBody.source F) k T
        (OccurrenceTupleOrder.readCoordinates digits)) =
      stateTapes k T F digits ((bits k T F digits).reverse ++ output) :=
    appended_stateTapes k T F digits output _
  exact actual.evals_in_steps.trans (congrArg
    (fun tapes => some (AddressOdometerSchedule.configuration
      (AddressMachineProgram.next k T 0) (AddressMachineSpace.initialState k).1 tapes)) hemit)

theorem setDigits_initialized_zero (F : SourceEncoding.Input) :
    AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
      (AddressMachineInitial.initialized k T F) = AddressMachineInitial.initialized k T F := by
  funext tape
  cases tape with
  | savedIndex j =>
    rw [AddressOdometerSchedule.setDigits_savedIndex, AddressMachineInitial.initialized_savedIndex]
  | extra e =>
    rcases e with e | e
    · rfl
    · rcases e with e | e
      · rfl
      · rcases e with j | e
        · change AddressOdometerSchedule.setDigits F.equations.length (fun _ : Fin k => 0)
            (AddressMachineInitial.initialized k T F) (AddressOdometerSchedule.remaining k s d T.vectors.length j) = _
          simp only [AddressOdometerSchedule.setDigits_remaining, Fin.isLt, dite_eq_left, Nat.sub_zero]
          exact (AddressMachineInitial.initialized_remaining k T F j).symm
        · rfl
  | _ => rfl

def traversal (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      (((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length + 2*k) *
        F.equations.length^k) := by
  have actual := AddressOdometerSchedule.traversalInTime (AddressMachineProgram.program k T) (AddressMachineProgram.bodyStart k T)
    (AddressMachineProgram.next k T) (AddressMachineProgram.resetAt k T) (AddressMachineSpace.initialState k).1
    (List.length_pos_iff.mpr F.nonempty)
    ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length)
    (AddressMachineInitial.initialized k T F) (bits k T F)
    (by
      intro i hi
      simp only [AddressMachineProgram.next_lt k T i hi, AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atCheck k T ⟨i,hi⟩)
    (by
      intro i hi
      simp only [AddressMachineProgram.resetAt_lt k T i hi,
        AddressOdometerSchedule.currentAt, AddressOdometerSchedule.remainingAt, hi, dite_eq_left]
      exact AddressMachineProgram.atReset k T ⟨i,hi⟩)
    (bodyTrace k T F)
  have run := Classical.choice actual
  have hstart : AddressOdometerSchedule.initialConfiguration (m := F.equations.length) k
      (AddressMachineProgram.bodyStart k T) (AddressMachineSpace.initialState k).1 (AddressMachineInitial.initialized k T F) =
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩ := by
    simp only [AddressOdometerSchedule.initialConfiguration, AddressOdometerSchedule.configuration,
      setDigits_initialized_zero, AddressMachineSpace.initialState]
  have hfinish : AddressOdometerSchedule.finalConfiguration (AddressMachineProgram.next k T k) (AddressMachineSpace.initialState k).1
      (AddressMachineInitial.initialized k T F) (bits k T F) =
      ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩ := by
    simp only [AddressOdometerSchedule.finalConfiguration, AddressOdometerSchedule.configuration, finalTapes,
      AddressMachineProgram.next_ge k T k (Nat.le_refl _), AddressMachineSpace.initialState]
  rw [hstart, hfinish] at run
  exact run

theorem headerBits_eq (F : SourceEncoding.Input) :
    MachineAddressHeaders.Arithmetic.headerBits k s d T.vectors.length
      F.«variables» F.equations.length =
      encodeWords [(AddressGame.tableOutput (AddressTupleBody.source F) k T).vertices, 2^s,
        (AddressGame.tableOutput (AddressTupleBody.source F) k T).constraints.length] := by
  have hcap : MachineAddressHeaders.capacity k s d F.«variables» F.equations.length =
      AddressGame.bodyCapacity (AddressTupleBody.source F) k s d := by
    change MachineAddressHeaders.capacity k s d F.«variables» F.equations.length =
      CanonicalAddress.capacity F.«variables» F.equations.length k s d
    simp [MachineAddressHeaders.capacity, MachineAddressHeaders.radix,
      MachineAddressHeaders.baseConstant, CanonicalAddress.capacity,
      CanonicalAddress.base_eq, Nat.add_assoc]
  have hedge : MachineAddressHeaders.edgeCount k s d T.vectors.length F.equations.length =
      (AddressGame.tableOutput (AddressTupleBody.source F) k T).constraints.length := by
    rw [AddressOutputSize.table_constraints_eq]
    change MachineAddressHeaders.edgeCount k s d T.vectors.length F.equations.length =
      Explicit.edgeCount F.equations.length k (s+d) T.vectors.length
    unfold MachineAddressHeaders.edgeCount MachineAddressHeaders.edgeFactor Explicit.edgeCount
    ring
  rw [MachineAddressHeaders.Arithmetic.headerBits, hcap, hedge]
  rfl

theorem final_accumulator (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineProgram.accumulator k T) =
      (gameBits (AddressGame.tableOutput (AddressTupleBody.source F) k T)).reverse := by
  rw [AddressOutcomeSpecs.gameBits_factor, ← headerBits_eq k T F, List.reverse_append]
  exact final_reversed k T F

def timePolynomial : Polynomial Nat :=
  (AddressTupleBudget.timePolynomial k T + Polynomial.C (2*k)) * Polynomial.X^k

@[simp] theorem timePolynomial_eval (N : Nat) :
    (timePolynomial k T).eval N = ((AddressTupleBudget.timePolynomial k T).eval N + 2*k)*N^k := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

def inPolynomialTime (F : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (TM2.step (AddressMachineProgram.program k T))
      ⟨some (AddressMachineProgram.bodyStart k T), AddressMachineSpace.initialState k, AddressMachineInitial.initialized k T F⟩
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k, finalTapes k T F⟩)
      ((timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have run := traversal k T F
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  apply run.steps_le_m.trans
  rw [timePolynomial_eval]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (SourceEncoding.inputBits_length_ge_equations F) k)

end
end DFVSGames.Reduction.AddressMachineLoop
end

section

namespace DFVSGames.Reduction.AddressMachineFinish

open Turing Foundations.Complexity Foundations.Hastad

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def timePolynomial (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (AddressMachineProgram.machine k T)
    (AddressMachineProgram.clearKeys k T).length (prefixTime + 1)

def completePrefix (input : List Bool) (prefixTime : Polynomial Nat)
    (base : AddressMachineProgram.Tape k T → List Bool)
    (execution : StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) input)
      (some ⟨some (AddressMachineProgram.finishStart k T),
        AddressMachineSpace.initialState k, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base (AddressMachineProgram.output k T) = []) :
    TM2OutputsInTime (AddressMachineProgram.machine k T) input
      (some (base (AddressMachineProgram.accumulator k T)).reverse)
      ((timePolynomial k T prefixTime).eval input.length) := by
  let bridge := AddressMachineProgram.finishStartInTime k T
    (AddressMachineSpace.initialState k) base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) input)
      (some ⟨SourceRuntimeFinish.entry (AddressMachineProgram.clearKeys k T)
          (AddressMachineProgram.finishLabels k T), AddressMachineSpace.initialState k, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using
        joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime
    (AddressMachineProgram.clearKeys k T)
    (AddressMachineProgram.accumulator k T) (AddressMachineProgram.output k T)
    (AddressMachineProgram.accumulator_ne_output k T)
    (AddressMachineProgram.accumulator_not_mem_clearKeys k T)
    (AddressMachineProgram.output_not_mem_clearKeys k T)
    (AddressMachineProgram.clearKeys_covers k T)
    (AddressMachineSpace.initialState k).1 (AddressMachineProgram.finishLabels k T) none
    (AddressMachineProgram.program k T) (AddressMachineProgram.atFinish k T)
    base outputEmpty (AddressMachineSpace.initialState k).1 none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (AddressMachineProgram.machine k T)
    input (prefixTime + 1) prefixRun
    (AddressMachineProgram.clearKeys k T)
    (AddressMachineProgram.accumulator k T) (AddressMachineProgram.output k T)
    (AddressMachineProgram.accumulator_not_mem_clearKeys k T)
    (AddressMachineProgram.output_not_mem_clearKeys k T)
    (AddressMachineProgram.clearKeys_covers k T) base outputEmpty (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
    (initList (AddressMachineProgram.machine k T) input)
    (some (haltList (AddressMachineProgram.machine k T)
      (base (AddressMachineProgram.accumulator k T)).reverse)) _
  rw [AddressMachineProgram.haltList_eq]
  exact run

end
end DFVSGames.Reduction.AddressMachineFinish
end

section

namespace DFVSGames.Reduction.MachineAddressGame

open Turing Foundations.Complexity

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def output (input : SourceEncoding.Input) : Foundations.Target.Instance (2 ^ s) :=
  AddressGame.tableOutput
    (ActualSource.Source.ofList input.equations input.nonempty) k T

def prefixPolynomial : Polynomial Nat :=
  AddressMachineInitial.timePolynomial k T + AddressMachineLoop.timePolynomial k T

def timePolynomial : Polynomial Nat :=
  AddressMachineFinish.timePolynomial k T (prefixPolynomial k T)

def prefixInTime (input : SourceEncoding.Input) :
    StateTransition.EvalsToInTime (AddressMachineProgram.machine k T).step
      (initList (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input))
      (some ⟨some (AddressMachineProgram.finishStart k T), AddressMachineSpace.initialState k,
        AddressMachineLoop.finalTapes k T input⟩)
      ((prefixPolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let initial := AddressMachineInitial.inPolynomialTime k T input
  let loop := AddressMachineLoop.inPolynomialTime k T input
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ initial loop
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  simpa only [prefixPolynomial, Polynomial.eval_add, Nat.add_comm] using run.steps_le_m

def fullRunInTime (input : SourceEncoding.Input) :
    TM2OutputsInTime (AddressMachineProgram.machine k T) (SourceEncoding.inputBits input)
      (some (gameBits (output k T input)))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length) := by
  let run := AddressMachineFinish.completePrefix k T (SourceEncoding.inputBits input)
    (prefixPolynomial k T) (AddressMachineLoop.finalTapes k T input)
    (prefixInTime k T input) (AddressMachineLoop.final_outputEmpty k T input)
  simpa only [AddressMachineLoop.final_accumulator, List.reverse_reverse, output,
    Integration.AddressTupleBody.source, timePolynomial] using run

def computableInPolyTime :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) where
  tm := AddressMachineProgram.machine k T
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial k T
  outputsFun input := by
    change TM2OutputsInTime (AddressMachineProgram.machine k T)
      ((SourceEncoding.inputBits input).map id)
      (some ((gameBits (output k T input)).map id))
      ((timePolynomial k T).eval (SourceEncoding.inputBits input).length)
    dsimp only [AddressMachineProgram.machine]
    rw [List.map_id, List.map_id]
    exact fullRunInTime k T input

end
end DFVSGames.Reduction.MachineAddressGame
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitBridge
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Explicit.MachineSingleOrbitBridge

open Turing DFVSGames.Reduction DFVSGames.Foundations.Complexity
open ActualSource MachineSingleOrbitCodec

namespace SingleAddress

abbrev tableOutput := Decoder.TableKeysAddressGame.tableOutput

end SingleAddress

theorem old_tableOutput_eq_double (S : Source) (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d) :
    AddressGame.tableOutput S k T = doubleInstance (SingleAddress.tableOutput S k T) :=
  old_outputInstance_eq_double S k _ _

def output (k : Nat) {s d : Nat} (T : DFVSGames.Integration.NoiseTables.Table s d)
    (input : SourceEncoding.Input) : DFVSGames.Foundations.Target.Instance (2 ^ s) :=
  SingleAddress.tableOutput (Source.ofList input.equations input.nonempty) k T

theorem old_output_eq_double (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d) (input : SourceEncoding.Input) :
    MachineAddressGame.output k T input = doubleInstance (output k T input) :=
  old_tableOutput_eq_double _ k T

noncomputable section

def doubledComputableInPolyTime (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits
      (fun I => gameBits (doubleInstance I)) (output k T) := by
  let old := MachineAddressGame.computableInPolyTime k T
  refine {
    tm := old.tm
    inputAlphabet := old.inputAlphabet
    outputAlphabet := old.outputAlphabet
    time := old.time
    outputsFun := ?_ }
  intro input
  rw [← old_output_eq_double k T input]
  exact old.outputsFun input

def computableInPolyTime (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) :=
  MachineSequential.composeBits (f := output k T) (g := id) (doubledComputableInPolyTime k T)
    (MachineSingleOrbitRuntime.computableInPolyTime (2 ^ s))

end

end DFVSGames.Explicit.MachineSingleOrbitBridge

namespace DFVSGames.Explicit.MachineSingleOrbitBridge

theorem workAlphabetFinite (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d)
    (tape : (computableInPolyTime k T).tm.K) :
    Finite ((computableInPolyTime k T).tm.Γ tape) := by
  rcases tape with first | second
  · change Finite Bool
    infer_instance
  · rcases second with localTape | bridgeTape
    · change Finite Bool
      infer_instance
    · change Finite Bool
      infer_instance

end DFVSGames.Explicit.MachineSingleOrbitBridge

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PositiveMultiplier
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Reduction.ActualSource
open DFVSGames.Fourier.MatrixNoise

namespace DFVSGames.Decoder.ActualSpectral

open TableKeysGame PositiveMultiplier NoiseSampler SurrogateFibers

attribute [local instance] OAI.DFVSGames.Decoder.ActualSpectral.homFintype
def fiberAcceptance (S : Source) (k s d : Nat)
    (label : Fin (vertexCount S k s d) → Fin (2 ^ s))
    (U : Question S k) (T : ActualHomogeneous.E k →ₗ[F2] Vector d) : ℝ :=
  shortcodeAcceptance (fun M : ActualHomogeneous.E k →ₗ[F2] Alphabet s =>
    unfolded S k s d label (U, M.prod T))

end DFVSGames.Decoder.ActualSpectral
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ActualGoodRows
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualGoodRows

open Integration.BinaryLinear Reduction ActualSource
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat HasAffineSlice)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] OAI.DFVSGames.Decoder.ActualGoodRows.homFintype
def adviceMass (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) : ℝ :=
  𝔼 U : ActualGame.Question S k,
    𝔼 T : ActualHomogeneous.E k →ₗ[F2] Vector d,
      RowErasure.adviceMass
        ((RowErasureMatrix.family s (1 + 2 * k) r).goodAt (table S k s d labeling U T) α)

end
end DFVSGames.Decoder.ActualGoodRows

namespace DFVSGames.Decoder.MatrixGapChoice

open Integration.BinaryLinear Reduction ActualSource
open Inverse.Shortcode (Mat HasAffineSlice InversePrinciple equalityAcceptance)

noncomputable section

structure InverseParameters (rstar : ℕ) where
  α : ℝ
  positive : 0 < α
  bounded : α ≤ 1
  r : ℕ
  s : ℕ
  s_large : rstar ≤ s
  r_small : r < s
  trivial_small : 1 / (2 : ℝ) ^ (s - r) < α / 8
  tupleThreshold : ℕ
  inverse : ∀ k : ℕ, tupleThreshold ≤ k →
    ∀ f : Mat s (1 + 2 * k) → Vector s,
      ActualSpectral.eta rstar ≤ equalityAcceptance f → HasAffineSlice f α r
  advice : ∀ k : ℕ, tupleThreshold ≤ k →
    ∀ (S : Source) (d : ℕ) (g : SplitGadget s d)
      (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)),
      (∀ L : Ambient s d →ₗ[F2] ActualHomogeneous.E k,
        rstar ≤ Module.finrank F2 (L.comp (alphabetEmbedding s d)).range →
        Integration.SplitGadget.kernelProbability g L ≤ 7 / 8) →
      (99 : ℚ) / 100 ≤ TableKeysGame.acceptanceProbability S k g labeling →
      ActualGoodRows.goodRowMass rstar s r ≤ ActualGoodRows.adviceMass S k s d r labeling α

end
end DFVSGames.Decoder.MatrixGapChoice

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSliceUniform
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Inverse Inverse.RowErasure
open Inverse.Shortcode (Mat)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] OAI.DFVSGames.Decoder.ActualEvents.homFintype
def unrestricted (S : Source) (k s d r : ℕ) : FiniteDistribution (Sample S k s d r) :=
  FiniteDistribution.uniform _

def targetHit (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (p : Sample S k s d r) : Bool :=
  decide ((RowErasureMatrix.family s (1 + 2 * k) r).selectedMatch
    (ActualGoodRows.table S k s d labeling p.1.1 p.1.2) α p.2.1 p.2.2)

end
end DFVSGames.Decoder.ActualEvents

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_SelectedPolicies
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Decoder.SelectedPolicies

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction
open DFVSGames.Inverse
open ActualSource VisiblePolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

def goodPredicate (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (w : ResponseWitness k) : Prop :=
  ∃ hgood : GoodAdvice S labeling α q,
    w = normalizedResponse S labeling α hα hsmall q hgood

end DFVSGames.Decoder.SelectedPolicies
end

namespace DFVSGames.Decoder.ActualSeedEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype_rd85017_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def law (S : Source) (k s d r : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (Seed S k s d r) :=
  AdviceLaw.fullSeedLaw (V := Ambient s d)
    (FiniteDistribution.uniform (ActualGame.Question S k))
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ'

def targetHit (S : Source) (k s d r : ℕ)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) (α : ℝ) :
    Seed S k s d r → Bool :=
  fun x => ActualEvents.targetHit S k s d r labeling α (pad S k s d r x)

end
end DFVSGames.Decoder.ActualSeedEvents

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_VisibleTransfer
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualProjectedTransfer

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

local instance homFintype_rd85017_2 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def slopeVariation (k s d : ℕ) (β : ℝ) : ℝ :=
  Foundations.Information.totalVariation
    (SparseLaw.independentWeights
      (SparseLaw.mixture β (SparseLaw.singletonPairWeights (Ambient s d))) k)
    (SparseLaw.uniformWeights (Fin k → Ambient s d × Ambient s d))

end
end DFVSGames.Decoder.ActualProjectedTransfer

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualAdviceSampling
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualAdviceSampling

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource ActualAdviceUpper

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

def sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) : ℝ :=
  ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
    (FiniteDistribution.uniform
      ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
        (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
      fun TM => (FiniteDistribution.table (fun _ : Fin k => μ)).expectation fun draw =>
        VisiblePolicies.observedAgreement S labeling good
          (actualDraw S A (Clean.NativeExperiment.maskSet mask) (fun j => (draw j).1)
            (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) TM.1 TM.2)

end

end DFVSGames.Decoder.ActualAdviceSampling

namespace DFVSGames.Decoder.ActualSeedSampling

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource ActualAdviceUpper ActualAdviceSampling

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

def drawAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) (mask : Fin k → Bool)
    (occ : Fin k → Fin S.occurrences) (slots : Fin k → Fin 3)
    (TM :
      (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
      (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s)) : ℝ :=
  VisiblePolicies.observedAgreement S labeling good
    (actualDraw S A (Clean.NativeExperiment.maskSet mask) occ
      (fun j => Clean.ActualAdviceBridge.indexSlot (slots j)) TM.1 TM.2)

end

end DFVSGames.Decoder.ActualSeedSampling

namespace DFVSGames.Gadget

universe u v

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

end DFVSGames.Gadget

end OAI
end


