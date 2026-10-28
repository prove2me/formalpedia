-- Prove2me | Definitions.Def_OAIQ087A021
-- name    : OAIQ087A021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:31:59.120846+00:00
-- url     : https://prove2.me/theorems/c0da0505-1ddd-4bb5-98c2-fd0e206d4c6a
-- title:
--   Definitions bundle OAIQ087A021 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 332 declarations of OpenAI's Lean: 145 definitions, 7 inductive types or structures, 4 instances and 176 theorems. The definitions and types are `OAI.MaxCutGames.Decoder.MatrixCoordinates.homFintype`, `OAI.MaxCutGames.Decoder.MatrixGap.Parameters`, `OAI.MaxCutGames.Decoder.MatrixGap.Parameters.output`, `OAI.MaxCutGames.Decoder.MatrixGapChoice.InverseParameters`, `OAI.MaxCutGames.Decoder.PaddedLaw.paddedMapWeights`, `OAI.MaxCutGames.Decoder.PaddedLaw.paddedWeights`, `OAI.MaxCutGames.Decoder.PositiveMultiplier.equalityAcceptance`, `OAI.MaxCutGames.Decoder.PositiveMultiplier.subspaceLaw`, `OAI.MaxCutGames.Decoder.PrivateFourier.frequencyCoset`, `OAI.MaxCutGames.Decoder.PrivateFourier.sliceCorrelation`, `OAI.MaxCutGames.Decoder.PrivateStrategy.conditionalAgreement`, `OAI.MaxCutGames.Decoder.PrivateStrategy.goodCosetMass`, `OAI.MaxCutGames.Decoder.SelectedDecoding.homFintype`, `OAI.MaxCutGames.Decoder.SelectedDecoding.transferredAgreement`, `OAI.MaxCutGames.Decoder.SelectedFiberLaw.homFintype`, `OAI.MaxCutGames.Decoder.SelectedPolicies.goodPredicate`, `OAI.MaxCutGames.Decoder.TableKeysAddressGame.tableOutput`, `OAI.MaxCutGames.Explicit.MachineClone100.computation`, `OAI.MaxCutGames.Explicit.MachineClone100Certified.certifiedFunction`, `OAI.MaxCutGames.Explicit.MachineClone100Run.inputTapes`, `OAI.MaxCutGames.Explicit.MachineClone100Run.runInTime`, `OAI.MaxCutGames.Explicit.MachineProductField.instruction`, `OAI.MaxCutGames.Explicit.MachineProductFinish.afterRows`, `OAI.MaxCutGames.Explicit.MachineProductFinish.finishInTime`, `OAI.MaxCutGames.Explicit.MachineProductGather.instruction`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.alphabetInTime`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.baseTapes`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.frame`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.inPolynomialTime`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.initializeInTime`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.powerExit`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.powerInTime`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.powersInTime`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.prepareInTime`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.seedBridge`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.seedInTime`, `OAI.MaxCutGames.Explicit.MachineProductHeaders.steps`, `OAI.MaxCutGames.Explicit.MachineProductHeadersRead.afterAlphabet`, `OAI.MaxCutGames.Explicit.MachineProductHeadersRead.afterVertices`, `OAI.MaxCutGames.Explicit.MachineProductHeadersRead.headersInTime` and 112 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_ActualGoodRows`, `MaxCut_Encoding_AdviceFibers`, `MaxCut_Encoding_MatrixCoordinates`, `MaxCut_Encoding_PaddedLaw`, `MaxCut_Encoding_PositiveMultiplier`, `MaxCut_Encoding_PrivateFourier`, `MaxCut_Encoding_SelectedPolicies`, `MaxCut_Encoding_TableKeysAddressGame`, `MaxCut_Encoding_TableKeysCompleteness`, `MaxCut_Encoding_TableKeysGame`, `MaxCut_Encoding_VisibleTransfer`, `MaxCut_Games_ActualCompleteness`, `MaxCut_Games_AddressGame`, `MaxCut_Games_Clone100Counting`, `MaxCut_Games_FinalCNFHeader`, `MaxCut_Games_FinalCNFStream`, `MaxCut_Games_NoiseEnumeration`, `MaxCut_Games_OccurrenceTupleOrder`, `MaxCut_Machines_AddressMachineInitial`, `MaxCut_Machines_AddressMachineLoop`, `MaxCut_Machines_AddressMachineProgram`, `MaxCut_Machines_CloneMachineModel`, `MaxCut_Machines_Lookup`, `MaxCut_Machines_Machine`, `MaxCut_Machines_MachineBinaryInputReduction`, `MaxCut_Machines_MachineBinaryParsing`, `MaxCut_Machines_MachineClone100`, `MaxCut_Machines_MachineClone100Triples`, `MaxCut_Machines_MachineHorner`, `MaxCut_Machines_MachineInitialHeaders`, `MaxCut_Machines_MachineLookupCore`, `MaxCut_Machines_MachineProductGatherBounds`, `MaxCut_Machines_MachineProductLoop`, `MaxCut_Machines_MachineProductProgram`, `MaxCut_Machines_MachineRegularOriginalBody`, `MaxCut_Machines_MachineRegularTableRuntime`, `MaxCut_Machines_MachineSingleOrbitProgram`, `MaxCut_Machines_MachineSubroutine`, `MaxCut_Machines_MachineUnaryMultiply`, `MaxCut_Machines_PoweringMachineVertex`, `MaxCut_Machines_RawInitialMachineModel`, `MaxCut_PCP_RawInitialPredicate`.
--
--   **Imports.** It imports the published bundle `Def_OptimalMaxCut`; the bundles `OAIQ087A014`, `OAIQ087A015` and `OAIQ087A016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A029`, `OAIQ087A030`, `OAIQ087A031` and `OAIQ087A032`; the statements `OAI.MaxCutGames.Decoder.ActualProjectedTransfer.actual_success_lower` and `OAI.MaxCutGames.Decoder.MatrixGapChoice.exists_inverse_parameters`; the proofs of `OAI.MaxCutGames.Decoder.ActualMatrixContradiction.contradiction`, `OAI.MaxCutGames.Decoder.ActualProjectedTransfer.actual_success_lower` and `OAI.MaxCutGames.Decoder.MatrixGapChoice.exists_inverse_parameters`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OptimalMaxCut
import Definitions.Def_OAIQ087A014
import Definitions.Def_OAIQ087A015
import Definitions.Def_OAIQ087A016

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Machine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complete-stack cleanup, with an arbitrary continuation. Each symbol
costs one transition and the empty-stack branch costs one final transition. -/

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace MaxCutGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

/-- Exact execution of all concrete drains in the supplied ambient program. -/
theorem trace (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps chosen base]
      (some ⟨entry chosen labels exit, (ambient, register), base⟩) =
    some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩ := by
  have run := MachineFiniteSequence.trace
    (LocalLabel := LocalLabel (K := K)) (main := fun _ => ())
    (localInstruction := localInstruction (σ := σ)) (result := result) (cost := cost)
    program (fun _ : Data K => True) (fun data => (ambient, data.2)) (fun data => data.1)
    chosen (by intros; trivial)
    (by
      intro source _ localLabels localExit atLocal data _
      rcases data with ⟨tapes, reg⟩
      simpa only [cost, result, Function.update_eq_self] using
        MachineDrain.drainTrace source (localLabels ()) localExit program (atLocal ())
          tapes (tapes source) ambient reg)
    labels exit atLabels (base, register) trivial
  simpa only [sequence_steps, sequence_result, entry] using run

end MaxCutGames.Foundations.Complexity.MachineDrainMany

namespace MaxCutGames.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

/-- Exact execution, including the real drain loops, reversal, and reset. The
only program hypotheses identify the caller's actual placed statements. -/
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

end MaxCutGames.Foundations.Hastad.SourceRuntimeFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLookupCore
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control for destructive unary-indexed table lookup. The guard decreases
the index even when the table is exhausted. Selection tests for an empty table
before writing the destination. All tests inspect just one finite head register.
-/

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLookup

open Turing
open MachineComposition

variable {K σ : Type} [DecidableEq K]

theorem guard_step_succ (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) input output⟩ =
      some ⟨some .skip, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord, List.replicate_succ, update_index]

theorem guard_step_zero (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ =
      some ⟨some .select, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord]

theorem select_step_nonempty (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter input output : List Bool) (hinput : input ≠ [])
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .select, (ambient, register),
        tapes index source destination base counter input output⟩ =
      some ⟨some .copy, (ambient, input.head?),
        tapes index source destination base counter input (false :: output)⟩ := by
  change some (TM2.stepAux (program index source destination .select) _ _) = _
  cases input with
  | nil => exact (hinput rfl).elim
  | cons head tail =>
    simp [program, select, Hastad.SourceMachine.fieldStart, TM2.stepAux,
      tapes_source, hsd, update_destination]

theorem copyTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 1]
      (some ⟨some .copy, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) (false :: output)⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  have h := Hastad.SourceMachine.fieldLoopTrace source destination hsd
    Label.copy (some Label.accepted) (program index source destination) rfl
    (Function.update base index counter) n suffix (false :: output) ambient register
  simpa only [Hastad.SourceMachine.fieldTapes, tapes, encodeWord,
    List.append_assoc, List.singleton_append] using h

theorem selectTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .select, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [select_step_nonempty index source destination hsd base counter
    (encodeWord n ++ suffix) output (by simp [encodeWord]) ambient register]
  exact copyTrace index source destination hsd base counter n suffix output ambient _

theorem skipCycleTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i n : Nat) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) (encodeWord n ++ suffix) output⟩) =
      some ⟨some .guard, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) suffix output⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [guard_step_succ index source destination his hid]
  have h := discardTrace source Label.skip Label.guard
    (program index source destination) rfl
    (tapes index source destination base (encodeWord i ++ indexSuffix)
      (encodeWord n ++ suffix) output) n suffix (by simp [hsd]) ambient none
  simpa only [update_source index source destination hsd] using h

/-- A successful positional lookup scans precisely its prior and selected
field. The suffix is arbitrary and is retained byte for byte. -/
theorem successPrefixTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List Nat) (value : Nat)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[
        (encodeWords prior).length + prior.length + value + 3]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord prior.length ++ indexSuffix)
        (encodeWords prior ++ (encodeWord value ++ suffix)) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) suffix (encodeWord value ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [encodeWords, List.length_nil, Nat.zero_add, List.nil_append]
    rw [show value + 3 = (value + 2) + 1 by omega, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [guard_step_zero index source destination his hid]
    exact selectTrace index source destination hsd base _ value suffix output ambient none
  | cons n prior ih =>
    simp only [encodeWords, List.length_cons, List.length_append, encodeWord_length]
    rw [show n + 1 + (encodeWords prior).length + (prior.length + 1) + value + 3 =
      ((encodeWords prior).length + prior.length + value + 3) + (n + 2) by omega,
      Function.iterate_add_apply]
    rw [List.append_assoc,
      skipCycleTrace index source destination his hid hsd base prior.length n]
    exact ih none

/-- Successful array access, with explicit selected value and preserved framing. -/
theorem lookupTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp selected).1
  have hlength : (values.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hsource : encodeWords (values.take i) ++
      (encodeWord value ++ (encodeWords (values.drop (i + 1)) ++ suffix)) =
      encodeWords values ++ suffix := by
    rw [MachineLookupSpec.encoded_selected_split values i value selected]
    simp only [List.append_assoc]
  have htime : MachineLookupSpec.steps values i =
      (encodeWords (values.take i)).length + i + value + 3 := by
    rw [MachineLookupSpec.steps_eq_scannedBits_of_some values i value selected,
      MachineLookupSpec.scannedBits_of_some values i value selected]
    omega
  have h := successPrefixTrace index source destination his hid hsd base (values.take i)
    value indexSuffix (encodeWords (values.drop (i + 1)) ++ suffix) output ambient register
  rw [hlength, hsource] at h
  simpa only [htime] using h

end MaxCutGames.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubroutine
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace MaxCutGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem lookupFramedHaltTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (MachineLookup.program index source destination)))^[
      MachineLookupSpec.steps values i + 1]
      (some ⟨some MachineLookup.Label.guard, (ambient,register),
        MachineLookup.tapes index source destination base (encodeWord i ++ indexSuffix)
          (encodeWords values ++ suffix) output⟩) =
      some ⟨none, (ambient,none), MachineLookup.tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  rw [Function.iterate_succ_apply',
    MachineLookup.lookupTrace_some index source destination his hid hsd
      base values i value selected indexSuffix suffix output ambient register]
  simp only [advance_some, TM2.step, MachineLookup.program, TM2.stepAux]

/-- Code-level interfaces specify the actual two copy loops and six lookup
instructions in the caller's program. No execution premise is supplied. -/
theorem preservingLookupTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1]
      (some ⟨some firstLabel, (ambient,register),
        initialTapes tape base i indexSuffix workSuffix output⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  let start := initialTapes tape base i indexSuffix workSuffix output
  have htable : start (tape 0) = encodeWords values := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 0 3 (by decide))] using tableWord
  have hs : start (tape 4) = [] := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 4 1 (by decide)) (hd 4 2 (by decide)) (hd 4 3 (by decide))] using scratchEmpty
  have hwork : start (tape 2) = workSuffix := by
    simp only [start, initialTapes, MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide))]
  have hcopy := MachineCopy.copyTrace (tape 0) (tape 2) (tape 4)
    (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
    firstLabel secondLabel (some (lookupLabels .guard)) program atFirst atSecond start hs ambient register
  rw [htable, hwork] at hcopy
  simp only [start, initialTapes, MachineLookup.update_source _ _ _ (hd 2 3 (by decide))] at hcopy
  have hlookup := MachineSubroutine.trace lookupLabels exit
    (MachineLookup.program (tape 1) (tape 2) (tape 3)) program atLookup
    (MachineLookupSpec.steps values i + 1) _ _
    (lookupFramedHaltTrace_some (tape 1) (tape 2) (tape 3)
      (hd 1 2 (by decide)) (hd 1 3 (by decide)) (hd 2 3 (by decide))
      base values i value selected indexSuffix workSuffix output ambient none)
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hlookup
  rw [show 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 =
      (MachineLookupSpec.steps values i + 1) + 2 * ((encodeWords values).length + 1) by omega,
    Function.iterate_add_apply]
  change (advance (TM2.step program))^[MachineLookupSpec.steps values i + 1]
    ((advance (TM2.step program))^[2 * ((encodeWords values).length + 1)]
      (some ⟨some firstLabel, (ambient,register),
        MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
          (encodeWord i ++ indexSuffix) workSuffix output⟩)) = _
  rw [hcopy]
  exact hlookup

end MaxCutGames.Foundations.Complexity.MachinePreservingLookup

namespace MaxCutGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def instruction (source : K) (tape : Fin 5 → K) (coefficient offset : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed (tape 1) offset (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source (tape 4) (tape 1)
      coefficient (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt (tape 4) source id false
      (labels .restore) (some (labels .copyFirst))
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false
      (labels .copySecond) (some (labels (.lookup .guard)))
  | .lookup l => MachineSubroutine.statement (fun q => labels (.lookup q)) exit
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

/-- An exact trace for the actual composite instructions. `atLabels` specifies
the caller's finite program; there is no execution or runtime premise. -/
theorem affineLookupTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (coefficient offset : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape coefficient offset labels exit l)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values) (scratchEmpty : base (tape 4) = [])
    (a : Nat) (suffix : List Bool) (sourceWord : base source = encodeWord a ++ suffix)
    (value : Nat) (selected : values[coefficient * a + offset]? = some value)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values a coefficient offset]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values (coefficient * a + offset) value⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have haffine := MachineUnaryAffineAt.seededAffineTrace source (tape 4) (tape 1)
    (outside 4) (outside 1) (hd 4 1 (by decide)) coefficient offset
    (labels .seed) (labels .scan) (labels .restore) (some (labels .copyFirst))
    program (atLabels .seed) (atLabels .scan) (atLabels .restore)
    base a suffix sourceWord scratchEmpty ambient register
  have hlookup := MachinePreservingLookup.preservingLookupTrace tape distinct
    (labels .copyFirst) (labels .copySecond) (fun q => labels (.lookup q)) exit
    program (atLabels .copyFirst) (atLabels .copySecond) (fun q => atLabels (.lookup q))
    base values tableWord scratchEmpty (coefficient * a + offset) value selected
    (base (tape 1)) (base (tape 2)) (base (tape 3)) ambient none
  rw [initialTapes_eq_update tape distinct] at hlookup
  rw [steps, Nat.add_comm, Function.iterate_add_apply, haffine]
  exact hlookup

end MaxCutGames.Foundations.Complexity.MachineAffineLookup

/-!
A fixed-width gather from an input-resident table. Every coordinate index lives
on a unary tape. The coefficient and coordinate-dependent offsets alone live
in finite control. Actual preserving affine lookup instructions read each
requested field, and the proof below composes their traces. This is the gather
phase of product-row construction, before the fixed-width Horner phase.
-/

namespace MaxCutGames.Explicit.MachineProductGather

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def instruction : (width : Nat) → (Tape width → K) → Nat → (Fin width → Nat) →
    (Label width → Λ) → Option Λ → Label width →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | 0, placement, _, _, _, exit, _ =>
    .load (fun state => (state.1, none))
      (MaxCutGames.Reduction.MachineTransfer.exitAt (placement (.inl 0)) exit)
  | width + 1, placement, coefficient, offsets, labels, exit, label =>
    match label with
    | .inl inner => MachineAffineLookup.instruction (placement (.inr (.inl 0)))
        (placement ∘ lookupRole width) coefficient (offsets 0)
        (fun l => labels (.inl l)) (some (labels (.inr (entry width)))) inner
    | .inr inner => instruction width (placement ∘ shift width) coefficient
        (fun i => offsets i.succ) (fun l => labels (.inr l)) exit inner

theorem gatherTrace (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction width placement coefficient offsets labels exit l)
    (base : K → List Bool) (suffixes : Fin width → List Bool)
    (tableWord : base (placement (.inl 0)) = encodeWords values)
    (scratchEmpty : base (placement (.inl 3)) = [])
    (sourceWords : ∀ i, base (placement (.inr (.inl i))) = encodeWord (indices i) ++ suffixes i)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values coefficient width indices offsets]
      (some ⟨some (labels (entry width)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        finalTapes values coefficient width placement indices offsets fields base⟩ := by
  induction width generalizing base register with
  | zero =>
    change some (TM2.stepAux (program (labels ())) _ _) = _
    erw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, finalTapes,
      MaxCutGames.Reduction.MachineTransfer.exitAt]
  | succ width ih =>
    have hd (a b : Tape (width + 1)) (hne : a ≠ b) : placement a ≠ placement b :=
      fun h => hne (distinct h)
    have outside : ∀ i : Fin 5,
        placement (.inr (.inl 0)) ≠ (placement ∘ lookupRole width) i := by
      intro i
      apply hd
      fin_cases i <;> simp [lookupRole]
    have first := MachineAffineLookup.affineLookupTrace (placement (.inr (.inl 0)))
      (placement ∘ lookupRole width) (distinct.comp (lookupRole_injective width)) outside
      coefficient (offsets 0) (fun l => labels (.inl l))
      (some (labels (.inr (entry width)))) program (fun l => atLabels (.inl l))
      base values tableWord scratchEmpty (indices 0) (suffixes 0) (sourceWords 0)
      (fields 0) (selected 0) ambient register
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    have frame (k : Tape (width + 1)) (h1 : k ≠ .inl 1) (h2 : k ≠ .inl 2)
        (h3 : k ≠ .inr (.inr 0)) : mid (placement k) = base (placement k) :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ (hd _ _ h1) (hd _ _ h2) (hd _ _ h3)
    have middleTable : mid (placement (.inl 0)) = encodeWords values := by
      rw [frame (.inl 0) (by simp) (by simp) (by simp)]
      exact tableWord
    have middleScratch : mid (placement (.inl 3)) = [] := by
      rw [frame (.inl 3) (by simp) (by simp) (by simp)]
      exact scratchEmpty
    have middleSources (i : Fin width) : mid (placement (.inr (.inl i.succ))) =
        encodeWord (indices i.succ) ++ suffixes i.succ := by
      rw [frame (.inr (.inl i.succ)) (by simp) (by simp) (by simp)]
      exact sourceWords i.succ
    have rest := ih (placement ∘ shift width) (distinct.comp (shift_injective width))
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (fun i => selected i.succ) (fun l => labels (.inr l))
      (fun l => atLabels (.inr l)) mid (fun i => suffixes i.succ)
      middleTable middleScratch middleSources none
    simp only [entry]
    rw [steps, Nat.add_comm, Function.iterate_add_apply, first]
    exact rest

end MaxCutGames.Explicit.MachineProductGather

/-!
Counted loops in one actual TM2 program. A unary guard is executed once before
each caller body and once more at zero. The caller supplies only individual
body traces, each returning to the guard with the same counter remainder.

Schedules are indexed by the remaining count: body `r` takes ambient state
`r + 1` to ambient state `r`. Consequently the run starts at index `n` and
ends at index zero. Bodies may change the ambient state and unprotected tapes.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineUnaryMultiply
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An actual five-stack unary multiplication subroutine. Both isolated input
fields are preserved. The product field prefixes the previous output stack;
the counter and scratch return empty and all other stacks are framed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

theorem bodyTrace_inline_MachineUnaryMultiply (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b r : ℕ) (hr : r < b)
    (operand : base (slots 0) = encodeWord a) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[bodySteps a]
      (some (MachineCountedLoop.bodyConfiguration (slots 3) (labels .scan) []
        (fun _ => (ambient, ())) (loopBase slots base a b) r)) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) r) := by
  have h04 : slots 0 ≠ slots 4 := slots.injective.ne (by decide)
  have h02 : slots 0 ≠ slots 2 := slots.injective.ne (by decide)
  have h42 : slots 4 ≠ slots 2 := slots.injective.ne (by decide)
  have h03 : slots 0 ≠ slots 3 := slots.injective.ne (by decide)
  have h43 : slots 4 ≠ slots 3 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let start := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b (r + 1)) r []
  have hstartA : start (slots 0) = encodeWord a := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h03, h02, operand]
  have hstartScratch : start (slots 4) = [] := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h43, h42, scratchEmpty]
  have hscan : p (labels .scan) = MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore) := atLabels .scan
  have hemit : ∀ control bit, p (emitterLabel labels control bit) =
      MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) control bit := by
    intro control bit
    cases control
    cases bit <;> exact atLabels _
  have hrestore : p (labels .restore) = Reduction.MachineTransfer.loopAt (slots 4) (slots 0)
      id false (labels .restore) (some (labels .guard)) := atLabels .restore
  have hcopy := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 4) (slots 2)
    h04 h02 h42 () transition payload (labels .scan) (labels .restore) (emitterLabel labels)
    (some (labels .guard)) p hscan hemit hrestore start hstartScratch ambient () none
  rw [hstartA, output_encodeWord_inline_MachineUnaryMultiply, List.reverse_replicate] at hcopy
  have hcount : a + a * (b - (r + 1)) = a * (b - r) := by
    have hr' : b - r = b - (r + 1) + 1 := by omega
    rw [hr']
    ring
  have hfinish : Function.update start (slots 2)
      (List.replicate a true ++ start (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b r) r [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp only [Function.update_self]
      simp only [start, MachineUnaryCounter.counterTapes_other (slots 3) (slots 2) h23,
        loopBase, resultTapes_output]
      rw [prepend_payload_inline_MachineUnaryMultiply, hcount]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [start, MachineUnaryCounter.counterTapes, hk2]
      · simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  rw [hfinish] at hcopy
  simpa only [bodySteps, encodeWord, List.length_append, List.length_replicate,
    List.length_singleton, MachineCountedLoop.bodyConfiguration,
    MachineCountedLoop.guardConfiguration] using hcopy

/-- Exact execution in any ambient program containing the nine declared
statements. The body traces are derived from the actual copy transducer. -/
theorem multiplyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps a b]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
  have h13 : slots 1 ≠ slots 3 := slots.injective.ne (by decide)
  have h14 : slots 1 ≠ slots 4 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let copied := Function.update base (slots 3) (encodeWord b)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (b + 2)]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .seed), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 1) (slots 3) (slots 4) h13 h14 h34 false
      (labels .copyDrain) (labels .copyFork) (some (labels .seed)) p
      (atLabels .copyDrain) (atLabels .copyFork) base scratchEmpty (ambient, ()) register
    simpa only [copied, operandB, counterEmpty, List.append_nil, encodeWord, List.length_append,
      List.length_replicate, List.length_singleton, Nat.add_assoc, Nat.reduceAdd] using h
  have hseedTapes : Function.update copied (slots 2) (false :: copied (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b b) b [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h23, encodeWord]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [copied, MachineUnaryCounter.counterTapes, hk2]
      · simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), none), copied⟩) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) b) := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), none) copied) = _
    rw [atLabels .seed]
    change some (⟨some (labels .guard), ((ambient, ()), none),
      Function.update copied (slots 2) (false :: copied (slots 2))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
    rw [hseedTapes]
    rfl
  have hloop := MachineCountedLoop.loopTrace (slots 3) (labels .guard) (labels .scan)
    (labels .finish) p (atLabels .guard) [] (fun _ => (ambient, ())) (fun _ => none)
    (loopBase slots base a b) (fun _ => bodySteps a) b
    (fun r hr => bodyTrace_inline_MachineUnaryMultiply slots labels exit p atLabels base a b r hr operandA scratchEmpty ambient)
  let finalCounter := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b 0) 0 []
  have hfinishTapes : Function.update finalCounter (slots 3) ((finalCounter (slots 3)).tail) =
      resultTapes slots base (a * b) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp [finalCounter, MachineUnaryCounter.counterTapes, encodeWord, resultTapes,
        Ne.symm h23, counterEmpty]
    · simp [finalCounter, MachineUnaryCounter.counterTapes, loopBase, hk3]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some (MachineCountedLoop.exitConfiguration (slots 3) (labels .finish) []
        (fun _ => (ambient, ())) (loopBase slots base a b))) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) finalCounter) = _
    rw [atLabels .finish]
    cases exit <;>
      simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using
        congrArg (fun tapes => some (⟨_, ((ambient, ()), none), tapes⟩ :
          TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
  rw [show steps a b = 1 + (MachineCountedLoop.totalSteps (fun _ => bodySteps a) b +
      (1 + 2 * (b + 2))) by rw [totalSteps_eq_inline_MachineUnaryMultiply]; unfold steps bodySteps; ring]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    hcopy, hseed, hloop]
  exact hfinish

end MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

/-!
One actual Horner step on unary field stacks. Multiplication and addition are
executions of the same finite program. All three operands are preserved; only
the output stack receives a new field and both work stacks return empty.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRadixStep

open Turing

variable {K Λ σ : Type}

variable [DecidableEq K]

/-- A concrete Horner execution. Caller hypotheses identify the finite code,
not an assumed execution or arithmetic oracle. -/
theorem radixStepTrace (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix acc digit]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  have h24 : slots 2 ≠ slots 4 := slots.injective.ne (by decide)
  have h25 : slots 2 ≠ slots 5 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h53 : slots 5 ≠ slots 3 := slots.injective.ne (by decide)
  have h45 : slots 4 ≠ slots 5 := slots.injective.ne (by decide)
  let multiplied := resultTapes slots base (radix * acc)
  have hmul : (MachineComposition.advance (TM2.step p))^[MachineUnaryMultiply.steps radix acc]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩ := by
    have h := MachineUnaryMultiply.multiplyTrace (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) p
      (fun l => atLabels (.multiply l)) base radix acc operandRadix operandAcc
      counterEmpty scratchEmpty ambient register
    simpa only [MachineUnaryMultiply.resultTapes, multiplySlots_two, multiplied, resultTapes] using h
  have hmulDigit : multiplied (slots 2) = encodeWord digit := by
    simp [multiplied, resultTapes, h23, operandDigit]
  have hmulCounter : multiplied (slots 4) = [] := by
    simp [multiplied, resultTapes, Ne.symm h34, counterEmpty]
  have hmulScratch : multiplied (slots 5) = [] := by
    simp [multiplied, resultTapes, h53, scratchEmpty]
  let copied := Function.update multiplied (slots 4) (encodeWord digit)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (digit + 2)]
      (some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩) =
      some ⟨some (labels .add), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 2) (slots 4) (slots 5) h24 h25 h45 false
      (labels .digitDrain) (labels .digitFork) (some (labels .add)) p
      (atLabels .digitDrain) (atLabels .digitFork) multiplied hmulScratch (ambient, ()) none
    simpa only [copied, hmulDigit, hmulCounter, List.append_nil, encodeWord,
      List.length_append, List.length_replicate, List.length_singleton,
      Nat.add_assoc, Nat.reduceAdd] using h
  have hcopiedCounter : copied (slots 4) = encodeWord digit ++ [] := by simp [copied]
  have hcopiedOutput : copied (slots 3) = encodeWord (radix * acc) ++ base (slots 3) := by
    simp [copied, multiplied, resultTapes, h34]
  let added := MachineUnaryAddAt.unaryTapes (slots 4) (slots 3) copied
    0 (digit + radix * acc) [] (base (slots 3))
  have hadd : (MachineComposition.advance (TM2.step p))^[digit + 1]
      (some ⟨some (labels .add), ((ambient, ()), none), copied⟩) =
      some ⟨some (labels .finish), ((ambient, ()), none), added⟩ :=
    MachineUnaryAddAt.addFromTapes (slots 4) (slots 3) (Ne.symm h34)
      (labels .add) (some (labels .finish)) p (atLabels .add) copied digit (radix * acc)
      [] (base (slots 3)) hcopiedCounter hcopiedOutput (ambient, ()) none
  have hfinishTapes : Function.update added (slots 4) ((added (slots 4)).tail) =
      resultTapes slots base (radix * acc + digit) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp only [Function.update_of_ne h34, added, MachineUnaryAddAt.unaryTapes_destination,
        resultTapes_output]
      rw [Nat.add_comm digit (radix * acc)]
    · by_cases hk4 : k = slots 4
      · subst k
        simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          resultTapes, encodeWord, Ne.symm h34, counterEmpty]
      · simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          copied, multiplied, resultTapes, hk3, hk4]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .finish), ((ambient, ()), none), added⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) added) = _
    rw [atLabels .finish]
    have hcfg := congrArg (fun tapes => some (⟨exit, ((ambient, ()), none), tapes⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
    cases exit <;> simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using hcfg
  rw [show steps radix acc digit =
      1 + ((digit + 1) + (2 * (digit + 2) + MachineUnaryMultiply.steps radix acc)) by
        unfold steps MachineUnaryMultiply.steps; ring]
  rw [Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ (digit + 1),
    Function.iterate_add_apply _ (2 * (digit + 2)), hmul, hcopy, hadd]
  exact hfinish

end MaxCutGames.Foundations.Complexity.MachineRadixStep

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineHorner
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fixed-width Horner traversal by actual radix steps. Two accumulators alternate:
a radix step writes into the empty alternate, then the previous accumulator is
consumed. The base, digit fields, and arbitrary external tapes are preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

/-- One genuine radix execution followed by a unary drain of its old input
accumulator. The new accumulator is left in the alternate physical tape. -/
theorem digitTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : Nat) (i : Fin width)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigit : base (slots (.inr i)) = encodeWord digit)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[stepCost radix acc digit]
      (some ⟨some (labels (.radix i (.multiply .copyDrain))), ((ambient, ()), register),
        stageTapes slots base i.val acc⟩) =
      some ⟨some (labels (entryLabel width (i.val + 1))), ((ambient, ()), none),
        stageTapes slots base (i.val + 1) (radix * acc + digit)⟩ := by
  let rs := radixSlots slots i
  let before := stageTapes slots base i.val acc
  let after := MachineRadixStep.resultTapes rs before (radix * acc + digit)
  have h01 : rs 0 ≠ rs 1 := rs.injective.ne (by decide)
  have h21 : rs 2 ≠ rs 1 := rs.injective.ne (by decide)
  have h31 : rs 3 ≠ rs 1 := rs.injective.ne (by decide)
  have h41 : rs 4 ≠ rs 1 := rs.injective.ne (by decide)
  have h51 : rs 5 ≠ rs 1 := rs.injective.ne (by decide)
  have hb : before (rs 0) = encodeWord radix := by
    change Function.update base (rs 1) (encodeWord acc) (rs 0) = _
    rw [Function.update_of_ne h01]
    exact operandRadix
  have ha : before (rs 1) = encodeWord acc := by
    exact Function.update_self _ _ _
  have hd : before (rs 2) = encodeWord digit := by
    change Function.update base (rs 1) (encodeWord acc) (rs 2) = _
    rw [Function.update_of_ne h21]
    exact operandDigit
  have hc : before (rs 4) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 4) = _
    rw [Function.update_of_ne h41]
    exact clean.counter
  have hs : before (rs 5) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 5) = _
    rw [Function.update_of_ne h51]
    exact clean.scratch
  have hout : before (rs 3) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 3) = _
    rw [Function.update_of_ne h31]
    exact clean.acc _
  have hradix := MachineRadixStep.radixStepTrace rs (fun l => labels (.radix i l))
    (some (labels (.clear i))) p (fun l => atLabels (.radix i l)) before radix acc digit
    hb ha hd hc hs ambient register
  have hold : after (rs 1) = encodeWord acc := by
    change Function.update before (rs 3) _ (rs 1) = _
    rw [Function.update_of_ne (Ne.symm h31), ha]
  have hstart : Function.update after (rs 1) (encodeWord acc ++ []) = after := by
    rw [List.append_nil, ← hold, Function.update_eq_self]
  have hfinish : Function.update after (rs 1) [] =
      stageTapes slots base (i.val + 1) (radix * acc + digit) := by
    have hempty : base (rs 1) = [] := clean.acc _
    change Function.update (Function.update (Function.update base (rs 1) (encodeWord acc))
      (rs 3) (encodeWord (radix * acc + digit) ++ before (rs 3))) (rs 1) [] =
      Function.update base (rs 3) (encodeWord (radix * acc + digit))
    rw [hout, List.append_nil]
    funext k
    by_cases h1 : k = rs 1
    · subst k; simp [Ne.symm h31, hempty]
    · by_cases h3 : k = rs 3
      · subst k; simp [h31]
      · simp [h1, h3]
  have hdrain := drainTrace (rs 1) (labels (.clear i))
    (some (labels (entryLabel width (i.val + 1)))) p (atLabels (.clear i))
    after acc [] ambient none
  rw [hstart, hfinish] at hdrain
  rw [show stepCost radix acc digit = (acc + 1) + MachineRadixStep.steps radix acc digit by
    unfold stepCost; omega, Function.iterate_add_apply, hradix]
  exact hdrain

/-- Prefix induction follows the fixed finite sequence of digit labels. -/
theorem prefixTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (n : Nat) (hn : n ≤ width) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps radix digits n]
      (some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩) =
      some ⟨some (labels (entryLabel width n)), ((ambient, ()), none),
        stageTapes slots base n (value radix digits n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < width := by omega
    let i : Fin width := ⟨n, hlt⟩
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    have h := digitTrace slots labels exit p atLabels base radix (value radix digits n)
      (digits n) i operandRadix (operandDigits i) clean ambient none
    simpa only [entryLabel, dite_eq_left hlt, i, value] using h

/-- Move the final accumulator to the external output, restoring its order and
emptying accumulator/scratch. The old destination is retained as a suffix. -/
theorem finishTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (acc : Nat) (clean : Clean slots base) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[2 * acc + 4]
      (some ⟨some (labels .finishDrain), ((ambient, ()), none), stageTapes slots base width acc⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ := by
  let src := slots (.inl (accumulator (parity width)))
  let scratch := slots (.inl 5)
  let dst := slots (.inl 3)
  have hsrcScratch : src ≠ scratch := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hsrcDst : src ≠ dst := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hscratchDst : scratch ≠ dst := slots.injective.ne (by simp)
  have hsrc : base src = [] := clean.acc _
  have hs : base scratch = [] := clean.scratch
  let before := stageTapes slots base width acc
  let middle := Function.update base scratch (encodeWord acc).reverse
  have hinput : before src = encodeWord acc := Function.update_self _ _ _
  have hscratch : before scratch = [] := by
    change Function.update base src (encodeWord acc) scratch = []
    rw [Function.update_of_ne (Ne.symm hsrcScratch), hs]
  have hfirstTapes : Reduction.MachineTransfer.tapesAt src scratch before []
      ((before src).reverse.map id ++ before scratch) = middle := by
    rw [hinput, hscratch, List.append_nil, List.map_id]
    funext k
    by_cases h1 : k = src
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, middle, hsrcScratch, hsrc]
    · by_cases h2 : k = scratch
      · subst k; simp [Reduction.MachineTransfer.tapesAt, middle]
      · simp [Reduction.MachineTransfer.tapesAt, middle, before, stageTapes, h1, h2, src]
  have first := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) src scratch hsrcScratch id false
    (labels .finishDrain) (some (labels .finishRestore)) p (atLabels .finishDrain)
    before (ambient, ()) none
  rw [hfirstTapes] at first
  have hlength : (before src).length + 1 = acc + 2 := by
    simp [hinput, encodeWord, Nat.add_assoc]
  rw [hlength] at first
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishDrain), ((ambient, ()), none), before⟩) =
      some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩ at first
  have hmSource : middle scratch = (encodeWord acc).reverse := Function.update_self _ _ _
  have hmOutput : middle dst = base dst := by
    exact Function.update_of_ne (Ne.symm hscratchDst) _ _
  have hsecondTapes : Reduction.MachineTransfer.tapesAt scratch dst middle []
      ((middle scratch).reverse.map id ++ middle dst) = resultTapes slots base acc := by
    rw [hmSource, hmOutput, List.reverse_reverse, List.map_id]
    funext k
    by_cases h1 : k = dst
    · subst k; simp [Reduction.MachineTransfer.tapesAt, resultTapes, dst]
    · by_cases h2 : k = scratch
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, hscratchDst, hs, scratch, dst]
      · simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, h1, h2, dst]
  have second := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) scratch dst hscratchDst id false
    (labels .finishRestore) exit p (atLabels .finishRestore) middle (ambient, ()) none
  rw [hsecondTapes] at second
  have hmLength : (middle scratch).length + 1 = acc + 2 := by
    simp [hmSource, encodeWord, Nat.add_assoc]
  rw [hmLength] at second
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ at second
  rw [show 2 * acc + 4 = (acc + 2) + (acc + 2) by omega,
    Function.iterate_add_apply, first]
  exact second

/-- Complete actual Horner execution on preserved digit/base fields. Initial
work tapes are empty; only the destination changes at the optional continuation. -/
theorem hornerTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix digits width]
      (some ⟨some (labels .start), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩ := by
  have start : TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩ =
      some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩ := by
    change some (TM2.stepAux (p (labels .start)) _ _) = _
    rw [atLabels .start]
    simp only [statement, TM2.stepAux, clean.accA, stageTapes, parity, accumulator,
      Bool.false_eq_true, ↓reduceIte, encodeWord, List.replicate_zero, List.nil_append]
  have prefixRun := prefixTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient width (Nat.le_refl _)
  have final := finishTrace slots labels exit p atLabels base (value radix digits width) clean ambient
  have hend : entryLabel width width = .finishDrain := by simp [entryLabel]
  rw [hend] at prefixRun
  rw [show steps radix digits width =
    ((2 * value radix digits width + 4) + prefixSteps radix digits width) + 1 by
      unfold steps; omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[
    (2 * value radix digits width + 4) + prefixSteps radix digits width]
      (TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩) = _
  rw [start, Function.iterate_add_apply, prefixRun]
  exact final

open scoped BigOperators

end MaxCutGames.Foundations.Complexity.MachineHorner

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

namespace MaxCutGames.Explicit.MachineProductField

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

def instruction (slots : Layout width ↪ K) (coefficient : Nat) (offsets : Fin width → Nat)
    (labels : Label slots → Λ) (exit : Option Λ) :
    Label slots → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl l => MachineProductGather.instruction width (gatherSlots slots) coefficient offsets
      (fun x => labels (.inl x)) (some (labels (.inr (.inl .start)))) l
  | .inr (.inl l) => MachineHorner.statement (hornerSlots slots)
      (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ()))))) l
  | .inr (.inr (.inl _)) => loopAt (slots (.inr 5)) (slots (.inr 6)) id false
      (labels (.inr (.inr (.inl ()))))
      (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
  | .inr (.inr (.inr l)) => MachineDrainMany.instruction (clearTapes slots)
      (fun x => labels (.inr (.inr (.inr x)))) exit l

/-- Actual execution of the complete gather/Horner/emit/cleanup phase. The
field equality connects only mathematical tape contents; all transition work
is proved from the concrete instructions. -/
theorem fieldTrace (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (labels : Label slots → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots coefficient offsets labels exit l)
    (base : K → List Bool) (suffixes : Fin width → List Bool) (ready : Ready slots base)
    (tableWord : base (slots (.inl (.inl 0))) = encodeWords values)
    (sourceWords : ∀ i, base (slots (.inl (.inr (.inl i)))) =
      encodeWord (indices i) ++ suffixes i)
    (radix : Nat) (digits : Nat → Nat)
    (radixWord : base (slots (.inr 0)) = encodeWord radix)
    (digitWords : ∀ i : Fin width, digits i.val = fields i.rev)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps slots values coefficient indices offsets fields base radix digits]
      (some ⟨some (labels (entry slots)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), finalTapes slots values coefficient indices offsets fields
        base (MachineHorner.value radix digits width)⟩ := by
  let middle := gathered slots values coefficient indices offsets fields base
  have gather := MachineProductGather.gatherTrace values coefficient width (gatherSlots slots)
    (gatherSlots slots).injective indices offsets fields selected (fun x => labels (.inl x))
    (some (labels (.inr (.inl .start)))) program (fun x => atLabels (.inl x))
    base suffixes tableWord ready.gatherScratch sourceWords (ambient, ()) register
  have preserved (i : Fin 7) : middle (slots (.inr i)) = base (slots (.inr i)) :=
    gathered_extra slots values coefficient indices offsets fields base i
  have middleRadix : middle (hornerSlots slots (.inl 0)) = encodeWord radix := by
    rw [show hornerSlots slots (.inl 0) = slots (.inr 0) from rfl, preserved]
    exact radixWord
  have middleDigits (i : Fin width) :
      middle (hornerSlots slots (.inr i)) = encodeWord (digits i.val) := by
    rw [show hornerSlots slots (.inr i) =
      gatherSlots slots (.inr (.inr i.rev)) from rfl]
    dsimp only [middle, gathered]
    rw [MachineProductGather.finalTapes_field values coefficient width (gatherSlots slots)
      (gatherSlots slots).injective indices offsets fields base i.rev]
    rw [show base (gatherSlots slots (.inr (.inr i.rev))) = [] from ready.fields i.rev,
      List.append_nil, digitWords i]
  have clean : MachineHorner.Clean (hornerSlots slots) middle := by
    constructor
    · change middle (slots (.inr 1)) = []; rw [preserved]; exact ready.accA
    · change middle (slots (.inr 2)) = []; rw [preserved]; exact ready.accB
    · change middle (slots (.inr 3)) = []; rw [preserved]; exact ready.counter
    · change middle (slots (.inr 4)) = []; rw [preserved]; exact ready.hornerScratch
  have horner := MachineHorner.hornerTrace (hornerSlots slots)
    (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ())))))
    program (fun x => atLabels (.inr (.inl x))) middle radix digits middleRadix
    middleDigits clean ambient none
  let value := MachineHorner.value radix digits width
  let after := evaluated slots values coefficient indices offsets fields base value
  have outputWord : after (slots (.inr 5)) = encodeWord value := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value
      (hornerSlots slots (.inl 3)) = _
    rw [MachineHorner.resultTapes_output]
    rw [show hornerSlots slots (.inl 3) = slots (.inr 5) from rfl,
      preserved, ready.output, List.append_nil]
  have accWord : after (slots (.inr 6)) = base (slots (.inr 6)) := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value (slots (.inr 6)) = _
    rw [MachineHorner.resultTapes_other _ _ _ _ (slots.injective.ne (by simp [hornerRole])), preserved]
  have emit := transferAt_fromTapes (Γ := fun _ : K => Bool)
    (slots (.inr 5)) (slots (.inr 6)) (slots.injective.ne (by simp [])) id false
    (labels (.inr (.inr (.inl ()))))
    (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
    program (atLabels (.inr (.inr (.inl ())))) after (ambient, ()) none
  rw [outputWord, accWord, List.map_id] at emit
  simp only [encodeWord_length] at emit
  have drain := MachineDrainMany.trace (clearTapes slots)
    (fun x => labels (.inr (.inr (.inr x)))) exit program
    (fun x => atLabels (.inr (.inr (.inr x))))
    (emitted slots values coefficient indices offsets fields base value) (ambient, ()) none
  rw [MachineDrainMany.finalRegister_none] at drain
  have emit' : (advance (TM2.step program))^[value + 2]
      (some ⟨some (labels (.inr (.inr (.inl ())))), ((ambient, ()), none), after⟩) =
      some ⟨MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit,
        ((ambient, ()), none), emitted slots values coefficient indices offsets fields base value⟩ := emit
  have compose {a b : Nat} {x y z : Option (TM2.Cfg (fun _ : K => Bool) Λ (MachineHorner.State σ))}
      (first : (advance (TM2.step program))^[a] x = y)
      (second : (advance (TM2.step program))^[b] y = z) :
      (advance (TM2.step program))^[a + b] x = z := by
    rw [Nat.add_comm, Function.iterate_add_apply, first, second]
  have gh := compose gather horner
  have ghe := compose gh emit'
  have whole := compose ghe drain
  simpa only [steps, value, entry, finalTapes] using whole

end MaxCutGames.Explicit.MachineProductField

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryParsing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Soundness of the ordinary-binary parser and its concrete name-scanning machine.
Every successful parse consumes exactly a canonical encoding and leaves its
stated suffix. Thus malformed or noncanonical bitstrings cannot name an extra
formula. The finite scanner's final-digit test is proved equivalent to the
codec's arithmetic canonicality test.
-/

/-!
Occurrence-index renaming for the ordinary-binary input machine. Every name is
replaced by the position of its first occurrence in the complete literal-name
list. The output declares three «variables» per clause; some IDs can be unused.
This avoids constructing a duplicate-free dictionary while keeping all IDs
bounded by the literal occurrence count. Equality tests may compare the actual
canonical binary payloads, without converting a name to unary.

These are the correspondence facts for the scan/compare machine.
They do not by themselves assert that the renaming runs in polynomial time.
-/

/-!
The ordinary binary 3SAT language includes exactly the successfully decoded
satisfiable formulas. A total semantic extension of occurrence-index renaming
maps malformed bitstrings to a fixed contradictory formula. Its runtime is a
separate machine-composition obligation; the size theorem below is only size.
-/

namespace MaxCutGames.BinaryLanguage

open MaxCutGames.Foundations

theorem totalParsed_satisfiable_iff (input : List Bool) :
    (totalParsed input).Satisfiable ↔ language input := by
  cases parsed : BinaryEncoding.decodeFormula input with
  | none => simp [totalParsed, parsed, rejectBinary_unsatisfiable, language]
  | some formula => simp [totalParsed, parsed, language]

theorem totalRename_satisfiable_iff (input : List Bool) :
    (totalRename input).Satisfiable ↔ language input := by
  exact (BinaryOccurrenceRename.renamed_satisfiable_iff (totalParsed input)).trans
    (totalParsed_satisfiable_iff input)

end MaxCutGames.BinaryLanguage

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Lookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

def headIndex {q : Nat} (table : Table q) (e : Fin table.darts) : Fin table.darts :=
  table.rows[e].reverseIndex

def headValue {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  table.rows[headIndex table e].tail.val

/-- The looked-up endpoint is the head of the actual graph semantics, including
paired loop darts whose reverse index differs from their own index. -/
theorem headValue_eq_semantics {q : Nat} (table : Table q) (e : Fin table.darts) :
    headValue table e = ((semantics table).head e).val := rfl

def headLookupTapes {q : Nat} (tape : HeadTapes K) (base : K → List Bool)
    (table : Table q) (e : Fin table.darts) : K → List Bool :=
  MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
    (encodeWord 0 ++ base (tape 3))
    (encodeWord table.rows[headIndex table e].reverseIndex.val ++
      (encodeWords (relationWords table.rows[headIndex table e].relation) ++
        (rowsBits ((rowList table).drop ((headIndex table e).val + 1)) ++ base (tape 2))))
    (encodeWord (headValue table e))

end MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_AdviceFibers
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.PartnerLinear.partnerModule _root_.OAI.MaxCutGames.Soundness.PartnerLinear.sourceModule _root_.OAI.MaxCutGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact visible row advice and private matrix coordinates

Every nonempty fiber of `M ↦ A ∘ M` is an affine copy of
`Hom(E, ker A)`, whether or not `A` is surjective.  Choosing one base matrix
for each attainable row gives a product decomposition of the complete matrix
space.  Uniform sampling therefore makes visible row advice and the hidden
kernel-valued matrix independent.
-/

/-! The finite set of realizable orbit records.  Vertices are the image of the
actual canonical-data map, so equal retained data from different questions
become one vertex.  The two sides remain distinct. -/

namespace MaxCutGames.Reduction.ActualOrbit

open MaxCutGames.Integration.BinaryLinear

universe u v

variable {Q : Type u} {T : Type v} {s d : Nat}

/-- The precise orientation used by the generated edge. -/
theorem constraint_iff_unfolded (can : Q → Ambient s d × T)
    (labelL labelR : Vertex can → Vector s) (q r : Q) :
    (labelL (vertex can q) + offset can q) + offset can r = labelR (vertex can r) ↔
      unfold can labelL q = unfold can labelR r := by
  constructor
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'
  · intro h
    have h' := congrArg (fun c => c + offset can r) h
    simpa only [add_cancel_vector, unfold] using h'

end MaxCutGames.Reduction.ActualOrbit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_NoiseEnumeration
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit enumeration of noise indices, retaining repeated vector values.
This additional data leaves `SplitGadget` unchanged and supplies an executable
ordering for the edge list. -/

/-! Actual finite translation game of Definition 4.6.  All questions, linear
maps, noise indices and linear functionals occur once in the outcome list.
Equal noise vectors retain their index multiplicity. -/

namespace MaxCutGames.Reduction.ActualGame

open MaxCutGames.Integration.BinaryLinear
open ActualSource
open Foundations.Target
open scoped BigOperators

noncomputable def unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (side : Bool)
    (q : Query S k s d) : Alphabet s :=
  ActualOrbit.unfold (canonical S k s d) (sideLabel S k s d labeling side) q

theorem edge_satisfied_iff (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (ω : Outcome S k g) :
    (edge S k g ω).satisfied labeling = true ↔
      unfolded S k s d labeling false (leftQuery S k g ω) =
      unfolded S k s d labeling true (rightQuery S k g ω) := by
  rw [Constraint.satisfied, decide_eq_true_eq]
  have h := Encoding.translationTable_satisfied_iff
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))
    (sideLabel S k s d labeling false (vertex S k s d (leftQuery S k g ω)))
    (sideLabel S k s d labeling true (vertex S k s d (rightQuery S k g ω)))
  simp only [sideLabel, Encoding.alphabetEquiv_apply_symm_apply] at h
  exact h.trans (ActualOrbit.constraint_iff_unfolded (canonical S k s d)
    (sideLabel S k s d labeling false) (sideLabel S k s d labeling true) _ _)

theorem acceptanceProbability_eq_test (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      Finset.univ.expect (fun ω : Outcome S k g =>
        if unfolded S k s d labeling false (leftQuery S k g ω) =
            unfolded S k s d labeling true (rightQuery S k g ω)
        then (1 : ℚ) else 0) := by
  unfold acceptanceProbability
  apply Finset.expect_congr rfl
  intro ω _
  simp only [edge_satisfied_iff]

/-! ## Executable enumeration and vertex numbering -/

end MaxCutGames.Reduction.ActualGame

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOriginalBody
attribute [-instance] _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

abbrev Tape := Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕ MachinePaddedExpanderFamily.Tape)

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

variable {Λ : Type}

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2

/-- Every equality decision is explicitly assembled from fixed finite leaves.
There is no classical decision or recursive typeclass search on the tape sum. -/
instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq_inline_MachineRegularOwnerCleanup
    (sumDecidableEq_inline_MachineRegularOwnerCleanup (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq_inline_MachineRegularOwnerCleanup (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq_inline_MachineRegularOwnerCleanup
          (sumDecidableEq_inline_MachineRegularOwnerCleanup
            (sumDecidableEq_inline_MachineRegularOwnerCleanup (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (inferInstanceAs (DecidableEq (Fin 2)))

/-- List membership uses Boolean equality in Lean 4.33. These instances are
the explicit Boolean view of the executable equality procedure above. -/
instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

def core (k : Fin 27) : Tape := .inl (.inl k)
def localRank : Tape := core 3
def count : Tape := core 4
def prefixTape : Tape := core 5
def rotor : Tape := core 7
def padding : Tape := .inl (.inr (.inl .padding))
def level : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0

/-- Every name is distinct, so the exact drain cost uses the entry lengths. -/
def cleanupTapes : List Tape := [localRank, count, rotor, padding, level, dummyFuel]

def afterAddition (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  Function.update base prefixTape (encodeWord (d + o))

def finalTapes (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  MachineDrainMany.finalTapes cleanupTapes (afterAddition base d o)

theorem finalTapes_apply (base : Tape → List Bool) (d o : Nat) (k : Tape) :
    finalTapes base d o k =
      if k ∈ cleanupTapes then []
      else if k = prefixTape then encodeWord (d + o) else base k := by
  simp only [finalTapes, MachineDrainMany.finalTapes_apply, afterAddition,
    Function.update_apply]

@[simp] theorem finalTapes_prefix (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o prefixTape = encodeWord (d + o) := by
  simp [finalTapes_apply, cleanupTapes, prefixTape, localRank, count, rotor,
    padding, level, dummyFuel, core]

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A fixed five-tape machine physically copies a graph table, preserves the
original input, and splits its two unary header fields from the copied rows.
The exact trace is ambient-state polymorphic for static machine placement.
-/

namespace MaxCutGames.Foundations.Complexity.MachineTableSplit

open Turing MachineComposition

def resultTapes (n m : Nat) (rowsBits : List Bool) : Tape → List Bool :=
  tapes (encodeWords [n, m] ++ rowsBits) rowsBits (encodeWord n) (encodeWord m)

@[simp] theorem resultTapes_original (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 0 = encodeWords [n, m] ++ rowsBits := by
  simp [resultTapes, tapes]

end MaxCutGames.Foundations.Complexity.MachineTableSplit

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

/-! Exact table-codec endpoint of the polynomial padding-row routine.
The caller supplies the physical unary counters and copied old-row buffer
with the updated headers. This theorem executes every added row and proves
that the resulting output is exactly the existing full table encoding. -/

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineInitialHeaders
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual caller-program traces for non-destructive unary-prefix emission and
the two headers of the raw initial graph. Unread suffixes are never scanned.
-/

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

namespace MaxCutGames.Foundations.Complexity.MachineOdometerInit
open Turing

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

variable (tape : Tape k → K) (distinct : Function.Injective tape)
  (labels : Label k → Λ) (exit : Option Λ)
  (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
  (atProgram : ∀l, program (labels l) = statement tape labels exit l)

def digitInTime (j : Fin k) (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : base (tape (.current j)) = [])
    (hremaining : base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.seed j)),(ambient,none),base⟩
      (some ⟨some (labelAt labels (j.val+1)),(ambient,none),digitOutput tape j m base⟩)
      (2*m+6) := by
  have hrc : tape .radix ≠ tape (.current j) := distinct.ne (by simp)
  have hrr : tape .radix ≠ tape (.remaining j) := distinct.ne (by simp)
  have hrs : tape .radix ≠ tape .scratch := distinct.ne (by simp)
  have hsc : tape .scratch ≠ tape (.current j) := distinct.ne (by simp)
  have hrsc : tape (.remaining j) ≠ tape .scratch := distinct.ne (by simp)
  have hrcc : tape (.remaining j) ≠ tape (.current j) := distinct.ne (by simp)
  let seeded := Function.update base (tape (.current j)) (encodeWord 0)
  have seedRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.seed j)),(ambient,none),base⟩
      (some ⟨some (labels (.copyOut j)),(ambient,none),seeded⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labels (.seed j))) (ambient,none) base) = _
    rw [atProgram]
    simp [statement,TM2.stepAux,seeded,hcurrent,encodeWord]
  have copiedRun := MachineCopy.copyInTime (tape .radix) (tape (.remaining j)) (tape .scratch)
    hrr hrs hrsc false (labels (.copyOut j)) (labels (.copyBack j))
    (some (labels (.trim j))) program (atProgram (.copyOut j)) (atProgram (.copyBack j))
    seeded (by simpa [seeded,hsc] using hscratch) ambient none
  let copied := Function.update seeded (tape (.remaining j)) (encodeWord m)
  have he : Function.update seeded (tape (.remaining j))
      (seeded (tape .radix) ++ seeded (tape (.remaining j))) = copied := by
    simp [copied,seeded,hradix,hremaining,hrc,hrcc]
  rw [he] at copiedRun
  have trimRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.trim j)),(ambient,none),copied⟩
      (some ⟨some (labelAt labels (j.val+1)),(ambient,none),digitOutput tape j m base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labels (.trim j))) (ambient,none) copied) = _
    have hm' : m = (m-1)+1 := by omega
    have tail : (encodeWord m).tail = encodeWord (m-1) := by
      conv_lhs => rw [hm']
      simp [encodeWord,List.replicate_succ]
    rw [atProgram]
    simp [statement,TM2.stepAux,copied,seeded,digitOutput,tail]
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seedRun copiedRun) trimRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hs : seeded (tape .radix) = encodeWord m := by simpa [seeded,hrc] using hradix
  rw [hs,encodeWord_length]
  omega

/-- Place the actual finite initialization prefix inside an ambient program. -/
def prefixInTime (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : ∀j, base (tape (.current j)) = [])
    (hremaining : ∀j, base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) (r : Nat) (hr : r ≤ k) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels 0),(ambient,none),base⟩
      (some ⟨some (labelAt labels r),(ambient,none),stageTapes tape m base r⟩)
      (r*(2*m+6)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hrk : r < k := by omega
    let j : Fin k := ⟨r,hrk⟩
    let before := stageTapes tape m base r
    have one := digitInTime tape distinct labels exit program atProgram j m hm before
      (by dsimp only [before]; rw [stageTapes_frame tape _ _ _ _
          (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))]; exact hradix)
      (by simp [before,stageTapes_current tape distinct,j,hcurrent])
      (by simp [before,stageTapes_remaining tape distinct,j,hremaining])
      (by dsimp only [before]; rw [stageTapes_frame tape _ _ _ _
          (fun _ => distinct.ne (by simp)) (fun _ => distinct.ne (by simp))]; exact hscratch)
      ambient
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt labels r),(ambient,none),before⟩
        (some ⟨some (labelAt labels (r+1)),(ambient,none),stageTapes tape m base (r+1)⟩)
        (2*m+6) := by
      simpa only [labelAt,dite_eq_left hrk,j,stageTapes,before] using one
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using joined

/-- Complete actual initialization, including width zero and the optional
continuation. The radix, scratch, ambient state and unrelated tapes survive. -/
def initializeInTime (m : Nat) (hm : 0 < m) (base : K → List Bool)
    (hradix : base (tape .radix) = encodeWord m)
    (hcurrent : ∀j, base (tape (.current j)) = [])
    (hremaining : ∀j, base (tape (.remaining j)) = [])
    (hscratch : base (tape .scratch) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels 0),(ambient,none),base⟩
      (some ⟨exit,(ambient,none),stageTapes tape m base k⟩)
      (k*(2*m+6)+1) := by
  have initializedPrefix := prefixInTime tape distinct labels exit program atProgram m hm base
    hradix hcurrent hremaining hscratch ambient k (le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt labels k),(ambient,none),stageTapes tape m base k⟩
      (some ⟨exit,(ambient,none),stageTapes tape m base k⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_refl _ }
    change some (TM2.stepAux (program (labelAt labels k)) (ambient,none) _) = _
    simp only [labelAt,Nat.lt_irrefl,↓reduceDIte]
    rw [atProgram]
    cases exit <;> rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ initializedPrefix doneRun

end MaxCutGames.Foundations.Complexity.MachineOdometerInit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialPredicate
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

namespace MaxCutGames.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

def clauseSigns {n : Nat} (c : Clause n) : Signs :=
  ((c)[0].positive, (c)[1].positive, (c)[2].positive)

def clauseNames {n : Nat} (c : Clause n) : Names :=
  ((c)[0].variableIndex.val, (c)[1].variableIndex.val, (c)[2].variableIndex.val)

def nameWord (names : Names) : Slot → Nat
  | .first => names.1
  | .second => names.2.1
  | .third => names.2.2

def decodedLabel (a : GraphTables.Label) : InitialGraph.Label :=
  AlphabetRetraction.decode64 (labelOrder.symm a)

def incidencePredicate (signs : Signs) (slot : Slot)
    (clauseLabel variableLabel : InitialGraph.Label) : Bool :=
  InitialGraph.variableValid variableLabel &&
    (((literalValue signs.1 clauseLabel.1 ||
      literalValue signs.2.1 clauseLabel.2.1) ||
      literalValue signs.2.2 clauseLabel.2.2) &&
      decide (answerAt (InitialGraph.toClauseAnswer clauseLabel) slot = variableLabel.1))

def relationPredicate (signs : Signs) (slot : Slot) :
    Bool → GraphTables.Label → GraphTables.Label → Bool
  | false, a, b => incidencePredicate signs slot (decodedLabel a) (decodedLabel b)
  | true, a, b => incidencePredicate signs slot (decodedLabel b) (decodedLabel a)

def relationWordsFor (signs : Signs) (slot : Slot) (orientation : Bool) : List Nat :=
  relationWords (relationOf (relationPredicate signs slot orientation))

@[simp] theorem relationWordsFor_length (signs : Signs) (slot : Slot) (orientation : Bool) :
    (relationWordsFor signs slot orientation).length = 4096 := by
  exact relationWords_length _

def incidenceWords (n i : Nat) (names : Names) (signs : Signs)
    (slot : Slot) (orientation : Bool) : List Nat :=
  [if orientation then nameWord names slot else n + i,
    6 * i + 2 * (slotOrder slot).val + (if orientation then 0 else 1)] ++
      relationWordsFor signs slot orientation

def clauseWords (n i : Nat) (names : Names) (signs : Signs) : List Nat :=
  incidenceWords n i names signs .first false ++
  incidenceWords n i names signs .first true ++
  incidenceWords n i names signs .second false ++
  incidenceWords n i names signs .second true ++
  incidenceWords n i names signs .third false ++
  incidenceWords n i names signs .third true

end MaxCutGames.Foundations.PCP.RawInitialRows

/-! Exact ordered rows of the initial incidence table. Every relation retains
all 4096 entries, including repetitions; this is a list identity, not a runtime bound. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual execution of the raw initial graph machine from its standard input
configuration to the first clause-loop guard. The unread clause bits are
preserved verbatim, and all tape contents at the boundary are explicit.
-/

/-! The exact input and output streams at successive clause-loop iterations.
These tape invariants use the actual word codecs and clause occurrence order. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def clauseInput {n : Nat} (clauses : List (Clause n)) : List Bool :=
  encodeWords (clauses.flatMap Complexity.clauseWords)

@[simp] theorem clauseInput_nil (n : Nat) : clauseInput ([] : List (Clause n)) = [] := rfl

@[simp] theorem clauseInput_cons {n : Nat} (c : Clause n) (cs : List (Clause n)) :
    clauseInput (c :: cs) = encodeWords (Complexity.clauseWords c) ++ clauseInput cs := by
  simp only [clauseInput, List.flatMap_cons, encodeWords_append]

def clauseOutput (n i : Nat) (clauses : List (Clause n)) : List Nat :=
  (clauses.mapIdx fun offset c => RawInitialRows.clauseWords n (i + offset)
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)).flatten

@[simp] theorem clauseOutput_nil (n i : Nat) : clauseOutput n i [] = [] := rfl

@[simp] theorem clauseOutput_cons (n i : Nat) (c : Clause n) (cs : List (Clause n)) :
    clauseOutput n i (c :: cs) =
      RawInitialRows.clauseWords n i (RawInitialRows.clauseNames c)
        (RawInitialRows.clauseSigns c) ++ clauseOutput n (i + 1) cs := by
  simp only [clauseOutput, List.mapIdx_cons, Nat.add_zero, List.flatten_cons,
    Nat.add_comm, Nat.add_left_comm]

end MaxCutGames.Foundations.PCP.RawInitialMachineLoopData

/-! Actual execution of the raw initial graph program's reusable phases. -/

/-!
Read exactly one concrete six-field CNF clause in the actual global machine,
then execute its real sign-loading instruction. No extra finish transition
is inserted. Every unrelated tape and the unread input suffix are preserved.
-/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity Hastad RawInitialMachineModel

/-- The six actual serialized fields, in name/sign/name/sign/name/sign order. -/
def fieldValue {n : ℕ} (c : Target.Clause n) (j : Fin 6) : ℕ :=
  (Complexity.clauseWords c)[j.val]'(by
    rw [Complexity.clauseWords_length]
    exact j.isLt)

/-- Full caller frame after the clause fields have been consumed. -/
def recordTapes {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .field j => encodeWord (fieldValue c j)
  | k => base k

@[simp] theorem recordTapes_input {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) :
    recordTapes base c suffix .input = suffix := rfl

@[simp] theorem recordTapes_field {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) (j : Fin 6) :
    recordTapes base c suffix (.field j) = encodeWord (fieldValue c j) := rfl

@[simp] theorem recordTapes_name {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) (j : Fin 3) :
    recordTapes base c suffix (.field (nameField j)) =
      encodeWord ((c)[j].variableIndex.val) := by
  fin_cases j <;> rfl

end MaxCutGames.Foundations.PCP.RawInitialMachineReadClause

/-! The six incidence rows are emitted by the actual finite program, with
their exact order, full relation lists, transition count, and tape frame. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFHeader
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The concrete final-CNF machine's entry phase. It archives its complete input,
reads the two unary size fields, emits the exact formula header, and reaches
the row guard. The transition witness is assembled from actual program calls.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

/-- Exact row-guard handoff: the original table is protected in `archive`,
the output header is accumulated in reverse, and the row index is unary zero. -/
def headerResultTapes (n m : Nat) (rowsBits : List Bool) : Tape → List Bool :=
  headerFrame rowsBits (encodeWords [n, m] ++ rowsBits)
    (encodeWord n) (encodeWord m) (encodeWord 0) [] []
    (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse

@[simp] theorem headerResultTapes_input (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .input = rowsBits := rfl

@[simp] theorem headerResultTapes_archive (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .archive = encodeWords [n, m] ++ rowsBits := rfl

@[simp] theorem headerResultTapes_accumulator (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .accumulator =
      (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse := rfl

@[simp] theorem headerResultTapes_rowIndex (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .rowIndex = encodeWord 0 := rfl

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-!
Actual finite-machine execution of the final converter's row phases. These
certificates use the concrete program statements, preserve all other tapes,
and expose the precise concatenated output of the fixed emission plan.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

def endpointTapes (base : Tape → List Bool) (tail reverse : Nat) (rest : List Bool) :=
  Hastad.SourceMachine.fieldTapes Tape.input Tape.reverseIndex
    (Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
      (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail))
    rest (encodeWord reverse ++ base .reverseIndex)

def finishTapes (base : Tape → List Bool) (row : Nat) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update (Function.update base Tape.tail []) Tape.head [])
      Tape.reverseIndex []) Tape.rowIndex (encodeWord (row + 1))

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-!
# Structural conversion to the generic 64-label table format

The fixed and generic formats store exactly the same fields in the same order.
Conversion maps the row structure, keeping each endpoint, reversal index, and
relation vector unchanged. In particular, the serialized input bits are equal,
so the generic table lookup machine applies to the actual final-converter input.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFTableAdapter

open PCP

def genericRow {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.DartRow 64 n m :=
  ⟨row.tail, row.reverseIndex, row.relation⟩

@[simp] theorem genericRow_tail {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).tail = row.tail := rfl

@[simp] theorem genericRow_reverseIndex {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).reverseIndex = row.reverseIndex := rfl

@[simp] theorem genericRow_relation {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).relation = row.relation := rfl

def genericRows {n m : Nat} (rows : GraphTables.Rows n m) :
    GenericGraphTables.Rows 64 n m := rows.map genericRow

@[simp] theorem genericRows_get {n m : Nat} (rows : GraphTables.Rows n m) (e : Fin m) :
    (genericRows rows)[e] = genericRow rows[e] := by
  simp [genericRows]

@[simp] theorem genericRows_reverseAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) :
    GenericGraphTables.reverseAt (genericRows rows) e = GraphTables.reverseAt rows e := by
  change (genericRows rows)[e].reverseIndex = rows[e].reverseIndex
  rw [genericRows_get]
  rfl

@[simp] theorem genericRows_acceptsAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) (a b : Fin 64) :
    GenericGraphTables.acceptsAt (genericRows rows) e a b =
      GraphTables.acceptsAt rows e a b := by
  simp only [GenericGraphTables.acceptsAt, genericRows_get, genericRow_relation]
  rfl

theorem genericRows_valid {n m : Nat} (rows : GraphTables.Rows n m)
    (valid : GraphTables.Valid rows) : GenericGraphTables.Valid (genericRows rows) := by
  constructor
  · intro e
    simpa only [genericRows_reverseAt] using valid.1 e
  · intro e a b
    simpa only [genericRows_reverseAt, genericRows_acceptsAt] using valid.2 e a b

/-- No row is recomputed, reordered, or selected by an abstract enumeration. -/
def genericTable (table : GraphTables.Table) : GenericGraphTables.Table 64 where
  vertices := table.vertices
  darts := table.darts
  rows := genericRows table.rows
  valid := genericRows_valid table.rows table.valid

@[simp] theorem genericTable_vertices (table : GraphTables.Table) :
    (genericTable table).vertices = table.vertices := rfl

@[simp] theorem genericTable_darts (table : GraphTables.Table) :
    (genericTable table).darts = table.darts := rfl

@[simp] theorem genericTable_row (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e] = genericRow table.rows[e] := genericRows_get _ _

@[simp] theorem genericTable_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].tail = table.rows[e].tail := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_reverseIndex (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].reverseIndex = table.rows[e].reverseIndex := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_relation (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].relation = table.rows[e].relation := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericRow_words {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.rowWords (genericRow row) = GraphTables.rowWords row := rfl

theorem genericTable_rowList (table : GraphTables.Table) :
    GenericGraphTables.rowList (genericTable table) =
      (GraphTables.rowList table).map genericRow := by
  simp only [GenericGraphTables.rowList, GraphTables.rowList, genericTable,
    genericRows, Vector.toList_map]

@[simp] theorem genericTable_tableWords (table : GraphTables.Table) :
    GenericGraphTables.tableWords (genericTable table) = GraphTables.tableWords table := by
  simp only [GenericGraphTables.tableWords, GraphTables.tableWords,
    genericTable_vertices, genericTable_darts, genericTable_rowList, List.flatMap_map,
    genericRow_words]

/-- The shared lookup machine consumes exactly the original serialized input. -/
@[simp] theorem genericTable_tableBits (table : GraphTables.Table) :
    GenericGraphTables.tableBits (genericTable table) = GraphTables.tableBits table := by
  simp only [GenericGraphTables.tableBits, GraphTables.tableBits, genericTable_tableWords]

@[simp] theorem genericTable_semantics_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).tail e =
      (GraphTables.semantics table).tail e := genericTable_tail table e

@[simp] theorem genericTable_semantics_reverse (table : GraphTables.Table)
    (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).reverse e =
      (GraphTables.semantics table).reverse e := genericTable_reverseIndex table e

@[simp] theorem genericTable_semantics_head (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).head e =
      (GraphTables.semantics table).head e := by
  simp only [ConstraintGraph.head, genericTable_semantics_reverse, genericTable_semantics_tail]
  rfl

@[simp] theorem genericTable_semantics_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (a b : Fin 64) :
    (GenericGraphTables.semantics (genericTable table)).accepts e a b =
      (GraphTables.semantics table).accepts e a b := genericRows_acceptsAt _ _ _ _

@[simp] theorem genericTable_headIndex (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headIndex (genericTable table) e = table.rows[e].reverseIndex :=
  genericTable_reverseIndex table e

@[simp] theorem genericTable_headValue (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headValue (genericTable table) e =
      ((GraphTables.semantics table).head e).val := by
  exact (AlphabetTable.Lookup.headValue_eq_semantics (genericTable table) e).trans
    (congrArg Fin.val (genericTable_semantics_head table e))

end MaxCutGames.Foundations.Complexity.FinalCNFTableAdapter

/-! Execution of one complete actual graph row in the final CNF machine. -/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

@[simp] theorem headRoles_zero : headRoles 0 = Tape.archive := rfl
@[simp] theorem headRoles_one : headRoles 1 = Tape.reverseIndex := rfl
@[simp] theorem headRoles_two : headRoles 2 = Tape.scanWork := rfl
@[simp] theorem headRoles_three : headRoles 3 = Tape.indexWork := rfl
@[simp] theorem headRoles_four : headRoles 4 = Tape.head := rfl
@[simp] theorem headRoles_five : headRoles 5 = Tape.scratch := rfl

def rowOperands (table : GraphTables.Table) (e : Fin table.darts) : Fin 5 → Nat :=
  values table.vertices table.darts table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val e.val

def rowRelation (table : GraphTables.Table) (e : Fin table.darts) : Ambient :=
  ((), fun i => table.rows[e].relation[i])

def rowRest (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) : List Bool :=
  encodeWords (GraphTables.relationWords table.rows[e].relation) ++ rest

def preparedTapes (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Lookup.headLookupTapes headRoles
    (endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
      (rowRest table e rest)) (genericTable table) e

def emittedTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Function.update (Function.update (preparedTapes base table e rest) Tape.input rest)
    Tape.accumulator ((plan.flatMap (Emitter.commandBits (rowOperands table e)
      (rowRelation table e))).reverse ++ base .accumulator)

def rowResultTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  finishTapes (emittedTapes plan base table e rest) e.val

@[simp] theorem rowResult_input (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .input = rest := by
  simp [rowResultTapes, finishTapes, emittedTapes]

@[simp] theorem rowResult_tail (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .tail = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_head (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .head = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_reverse (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .reverseIndex = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_index (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .rowIndex = encodeWord (e.val + 1) := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_accumulator (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .accumulator =
      (plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e))).reverse ++
        base .accumulator := by
  simp [rowResultTapes, finishTapes, emittedTapes]

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact row enumeration and input/output stream identities for the concrete
final-CNF machine. Rows occur in stored order, including repeated rows.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTableAdapter

/-- The actual unprocessed suffix of the finite table's stored row indices. -/
def remainingEvents (table : GraphTables.Table) (r : Nat) : List (Fin table.darts) :=
  (List.finRange table.darts).drop r

def inputStream (table : GraphTables.Table) (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => encodeWords (GraphTables.rowWords table.rows[e]))

@[simp] theorem remainingEvents_zero (table : GraphTables.Table) :
    remainingEvents table 0 = List.finRange table.darts := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_length (table : GraphTables.Table) (r : Nat) :
    (remainingEvents table r).length = table.darts - r := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_done (table : GraphTables.Table) :
    remainingEvents table table.darts = [] := by
  simp [remainingEvents]

@[simp] theorem inputStream_nil (table : GraphTables.Table) : inputStream table [] = [] := rfl

@[simp] theorem inputStream_cons (table : GraphTables.Table) (e : Fin table.darts)
    (events : List (Fin table.darts)) :
    inputStream table (e :: events) =
      encodeWords (GraphTables.rowWords table.rows[e]) ++ inputStream table events := rfl

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-! The actual bounded loop over every stored row of the final CNF converter. -/

/-!
The complete actual output-producing trace of the final CNF machine. Its
terminal configuration still contains private work tapes before the
canonical halt required by the machine interface.
-/

/-!
Fixed literal templates for the twelve-query converter. All control data have
constant size: twelve query references, nine auxiliary references, ten clauses,
and three literal slots. Pattern bits remain symbolic throughout the proof.

These templates specify the actual serialized rows. Their machine execution
is proved separately in FinalCNFRow and FinalCNFComputation.
-/

/-!
The fixed finite emission plan for one directed graph row. All choices based
on the relation are functions of its 4096-bit finite register. Vertex counts,
endpoint names and row indices are read by preserving unary scans.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineVertex
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

def afterHeaders (output : K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update base output (encodeWords [n, m] ++ base output)

@[simp] theorem afterHeaders_output (output : K) (base : K → List Bool) (n m : Nat) :
    afterHeaders output base n m output = encodeWords [n, m] ++ base output := by
  simp only [afterHeaders, Function.update_self]

end MaxCutGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Clone100Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete clone sample space. Global distinctness is a stronger
conditioning rule than distinctness only at repeated original «variables».
It retains the same 3/100 bound and makes the number of copies uniform. -/

namespace MaxCutGames.Outer.Clone100

open MaxCutGames.Reduction CloneGap ActualSource
open Clone100Triples
open scoped BigOperators

noncomputable section

theorem clonedInput_bits_length_le (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (clonedInput input)).length ≤
      input.«variables» * 100 + input.equations.length * 970200 + 2 +
        input.equations.length * 970200 * (300 * input.«variables» + 2) := by
  have h := SourceEncoding.inputBits_length_le (clonedInput input)
  simpa [clonedInput, equations_length, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

end
end MaxCutGames.Outer.Clone100

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineClone100Triples
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.MachineClone100Run

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MachineClone100Model

def inputTapes (input : SourceEncoding.Input) : Tape → List Bool :=
  fun tape => if tape = .input then SourceEncoding.inputBits input else []

theorem inputBits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.«variables», input.equations.length] ++ sourceBody input := by
  simp only [SourceEncoding.inputBits, SourceEncoding.inputWords, encodeWords_append, sourceBody]

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

/-- Actual execution from the existing input codec to the complete literal
halt configuration, with the sum of the three proved phase budgets. -/
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

end MaxCutGames.Explicit.MachineClone100Run

namespace MaxCutGames.Explicit.MachineClone100Certified

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity

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

end MaxCutGames.Explicit.MachineClone100Certified

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineClone100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.MachineClone100

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations.Complexity

noncomputable section

theorem input_bits_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputBits (Outer.Clone100.clonedInput input) =
      MachineClone100Run.outputBits triples input := by
  rw [SourceEncoding.inputBits, input_words_eq, encodeWords_append]
  rfl

theorem size_bound (input : SourceEncoding.Input) :
    (SourceEncoding.inputBits (Outer.Clone100.clonedInput input)).length ≤
      (300 * triples.length) * (SourceEncoding.inputBits input).length *
        (SourceEncoding.inputBits input).length +
      (100 + 3 * triples.length) * (SourceEncoding.inputBits input).length + 2 := by
  rw [triples_length]
  exact (Outer.Clone100.clonedInput_bits_length_le input).trans
    (serialized_polynomial_inline_MachineClone100 970200 (SourceEncoding.inputBits input).length
      input.«variables» input.equations.length
      (SourceEncoding.inputBits_length_ge_variables input)
      (SourceEncoding.inputBits_length_ge_equations input))

def computation : TM2ComputableInPolyTime SourceEncoding.inputBits
    SourceEncoding.inputBits Outer.Clone100.clonedInput :=
  MachineClone100Certified.certifiedFunction triples triples_nonempty
    Outer.Clone100.clonedInput input_bits_eq size_bound

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

end

end MaxCutGames.Explicit.MachineClone100

/-!
A finite-state validator for the concrete ordinary-binary formula encoding.
It checks clause and literal framing, canonical name payloads, and the unique
terminal formula marker. The last-digit register starts at true for each name,
so the empty payload is accepted as zero while a nonempty payload must end in
one. Every bit following the terminal formula marker causes rejection.
-/

/-!
Total raw-input preprocessing for the ordinary binary formula codec. The
machine copies each input bit onto a reverse stack while running the finite
validator. Accepted words are restored verbatim; rejected words are drained
and replaced by the fixed contradictory formula. All three stack alphabets
and all control/register types are finite.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryInputReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The complete ordinary-binary input bridge. Arbitrary raw input bits are first
validated and retained, or replaced by a fixed contradictory encoded formula.
The checked occurrence-index renamer then emits the inherited dense 3CNF
codec. Both stages and their physical handoff have actual polynomial-time
finite-alphabet machine certificates.

This is a bridge for the explicit ordinary binary 3SAT language. It is not the
PCP construction, a proof of that construction's runtime, or an NP-hardness
assertion about the eventual 2-to-1 target.
-/

namespace MaxCutGames.BinaryInputReduction

open Turing MaxCutGames.Foundations.Complexity

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineFiniteAlphabet.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime
    BinaryTotalInputMachine.computation_finiteAlphabet
    BinaryRenameMachine.computation_finiteAlphabet

end MaxCutGames.BinaryInputReduction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineProductGatherBounds
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual work stacks left by the preserving gather. These
bounds justify clearing the query/scan remnants after each product field;
they are consequences of the exact tape formulas, not runtime assumptions. -/

/-! The product-field machine restores every work tape and appends precisely
one field to the reversed output. This boundary is strong enough to compose
all fields and every odometer visit without retaining an unbounded history. -/

/-! A finite row-field schedule. Endpoint fields use the input vertex radix;
permutation fields use the fixed alphabet radix. The complete list of columns
is in finite control, while all row indices, table entries and radix magnitudes
remain data on tapes. -/

namespace MaxCutGames.Explicit.MachineProductRow

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

def localInstruction (slots : Layout width ↪ K) (coefficient : Nat) (command : Command width)
    (labels : LocalLabel slots command → Λ) (exit : Option Λ) :
    LocalLabel slots command → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineProductField.instruction (fieldSlots slots command.1) coefficient command.2 labels exit

def instruction (slots : Layout width ↪ K) (coefficient : Nat) (commands : List (Command width))
    (labels : Label slots commands → Λ) (exit : Option Λ) :
    Label slots commands → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction slots coefficient) commands labels exit

/-- Complete row trace from the concrete field implementation. The only
premises concerning values are literal indexed-table identities and the
Horner interpretation of those values. -/
theorem rowTrace (slots : Layout width ↪ K) (table : List Nat) (coefficient : Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat) (commands : List (Command width))
    (fields : Command width → Fin width → Nat) (digits : Command width → Nat → Nat)
    (selected : ∀ command ∈ commands, ∀ i,
      table[coefficient * indices i + command.2 i]? = some (fields command i))
    (reversed : ∀ command ∈ commands, ∀ i : Fin width,
      digits command i.val = fields command i.rev)
    (labels : Label slots commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots coefficient commands labels exit l)
    (base : K → List Bool) (ready : Ready slots table indices radices base) (ambient : σ) :
    let values := fun c : Command width => MachineHorner.value (radices c.1) (digits c) width
    let cost := fun (c : Command width) (tapes : K → List Bool) =>
      MachineProductField.steps (fieldSlots slots c.1) table coefficient indices c.2 (fields c)
        tapes (radices c.1) (digits c)
    (advance (TM2.step program))^[MachineFiniteSequence.steps (result slots values) cost commands base]
      (some ⟨entry slots commands labels exit, ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update base (outputTape slots)
          ((rowBits values commands).reverse ++ base (outputTape slots))⟩ := by
  dsimp only
  let values := fun c : Command width => MachineHorner.value (radices c.1) (digits c) width
  let cost := fun (c : Command width) (tapes : K → List Bool) =>
    MachineProductField.steps (fieldSlots slots c.1) table coefficient indices c.2 (fields c)
      tapes (radices c.1) (digits c)
  have run := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction slots coefficient) (result slots values) cost program
    (Ready slots table indices radices) (fun _ => ((ambient, ()), none)) id commands
    (by intro c hc tapes ht; exact ht.appendField slots table indices radices tapes (values c))
    (by
      intro c hc fieldLabels fieldExit atField tapes ht
      have h := MachineProductField.fieldTrace (fieldSlots slots c.1) table coefficient
        indices c.2 (fields c) (selected c hc) fieldLabels fieldExit program atField tapes
        (fun _ => []) (ht.work c.1) ht.tableWord
        (fun i => by simpa [fieldSlots, fieldRole] using ht.sourceWords i) (radices c.1) (digits c)
        (ht.radixWords c.1) (reversed c hc) ambient none
      rw [MachineProductField.finalTapes_eq _ _ _ _ _ _ _ (ht.work c.1)] at h
      exact h)
    labels exit atLabels base ready
  rw [resultOf_eq] at run
  exact run

end MaxCutGames.Explicit.MachineProductRow

/-!
The exact table lookups and field schedule consumed by the product machine.
The table contains rows only: the three input header words have already been
consumed, so each affine lookup has coefficient `q+2` and no header offset.
-/

/-! Actual power-header emission by fixed-width Horner evaluation of
`[1,0,...,0]`, followed by physical transfer to the reverse accumulator. -/

namespace MaxCutGames.Explicit.MachineProductPower

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {exponent : Nat}

def instruction (slots : MachineHorner.Layout (exponent + 1) ↪ K) (output : K)
    (labels : Label exponent → Λ) (exit : Option Λ) :
    Label exponent → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl l => MachineHorner.statement slots (fun x => labels (.inl x))
      (some (labels (.inr ()))) l
  | .inr _ => loopAt (slots (.inl 3)) output id false (labels (.inr ())) exit

/-- Header powers are computed from a unary input radix, not stored in an
unbounded register. Only the output accumulator changes at the boundary. -/
theorem powerTrace (slots : MachineHorner.Layout (exponent + 1) ↪ K) (output : K)
    (outside : ∀ i, output ≠ slots i) (labels : Label exponent → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots output labels exit l)
    (base : K → List Bool) (radix : Nat)
    (radixWord : base (slots (.inl 0)) = encodeWord radix)
    (digitWords : ∀ i : Fin (exponent + 1), base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : MachineHorner.Clean slots base) (fieldEmpty : base (slots (.inl 3)) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps radix exponent]
      (some ⟨some (labels (.inl .start)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update base output ((encodeWord (radix ^ exponent)).reverse ++ base output)⟩ := by
  have horner := MachineHorner.hornerTrace slots (fun x => labels (.inl x))
    (some (labels (.inr ()))) program (fun x => atLabels (.inl x)) base radix digits
    radixWord digitWords clean ambient register
  rw [value_eq] at horner
  let after := MachineHorner.resultTapes slots base (radix ^ exponent)
  have hout : after (slots (.inl 3)) = encodeWord (radix ^ exponent) := by
    dsimp only [after]
    rw [MachineHorner.resultTapes_output, fieldEmpty, List.append_nil]
  have hacc : after output = base output :=
    MachineHorner.resultTapes_other slots base (radix ^ exponent) output (outside _)
  have emit := transferAt_fromTapes (Γ := fun _ : K => Bool)
    (slots (.inl 3)) output (Ne.symm (outside _)) id false (labels (.inr ())) exit
    program (atLabels (.inr ())) after (ambient, ()) none
  rw [hout, hacc, List.map_id, encodeWord_length] at emit
  have tapes_eq : tapesAt (slots (.inl 3)) output after []
      ((encodeWord (radix ^ exponent)).reverse ++ base output) =
      Function.update base output ((encodeWord (radix ^ exponent)).reverse ++ base output) := by
    funext k
    by_cases h1 : k = output
    · subst k; simp [tapesAt]
    · by_cases h2 : k = slots (.inl 3)
      · subst k; simp [tapesAt, h1, fieldEmpty]
      · simp [tapesAt, after, MachineHorner.resultTapes, h1, h2]
  rw [tapes_eq] at emit
  rw [show steps radix exponent = (radix ^ exponent + 2) +
    MachineHorner.steps radix digits (exponent + 1) by unfold steps; omega,
    Function.iterate_add_apply, horner]
  exact emit

end MaxCutGames.Explicit.MachineProductPower

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineProductProgram
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.MachineProductProgram

open Turing
open MaxCutGames.Foundations
open Complexity Hastad
open MaxCutGames.Reduction.MachineTransfer

abbrev Tape (t : Nat) := SourceContextLoad.Tape t (Extra t)

def auxiliary (t : Nat) (i : Fin 10) : Tape t := .extra (.inl i)
def constantDigit (t : Nat) (i : Fin (t + 1)) : Tape t := .extra (.inr i)
def accumulator (t : Nat) : Tape t := auxiliary t 6
def output (t : Nat) : Tape t := auxiliary t 9

def rowRole (t : Nat) : MachineProductRow.Layout t → Tape t
  | .inl (.inl (.inl 0)) => .formula
  | .inl (.inl (.inl 1)) => .index
  | .inl (.inl (.inl 2)) => .work
  | .inl (.inl (.inl 3)) => .scratch
  | .inl (.inl (.inr (.inl i))) => .current i
  | .inl (.inl (.inr (.inr i))) => .field i 0
  | .inl (.inr i) => auxiliary t (Fin.castLE (by omega) i)
  | .inr _ => auxiliary t 7

def decodeRow_inline_MachineProductProgram (t : Nat) : Tape t → Option (MachineProductRow.Layout t)
  | .formula => some (.inl (.inl (.inl 0)))
  | .index => some (.inl (.inl (.inl 1)))
  | .work => some (.inl (.inl (.inl 2)))
  | .scratch => some (.inl (.inl (.inl 3)))
  | .current i => some (.inl (.inl (.inr (.inl i))))
  | .field i s => if s = 0 then some (.inl (.inl (.inr (.inr i)))) else none
  | .extra (.inl i) => if h : i.val < 7 then some (.inl (.inr ⟨i.val, h⟩))
      else if i = 7 then some (.inr ()) else none
  | _ => none

theorem decodeRow_role_inline_MachineProductProgram (t : Nat) (i : MachineProductRow.Layout t) :
    decodeRow_inline_MachineProductProgram t (rowRole t i) = some i := by
  rcases i with (((i | (i | i)) | i) | i)
  · fin_cases i <;> rfl
  · rfl
  · simp [decodeRow_inline_MachineProductProgram, rowRole]
  · simp [rowRole, auxiliary, decodeRow_inline_MachineProductProgram, i.isLt]
  · cases i; rfl

def rowSlots (t : Nat) : MachineProductRow.Layout t ↪ Tape t where
  toFun := rowRole t
  inj' := by
    intro a b h
    have d := congrArg (decodeRow_inline_MachineProductProgram t) h
    exact Option.some.inj (by simpa only [decodeRow_role_inline_MachineProductProgram] using d)

def powerRole (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) → Tape t
  | .inl 0 => auxiliary t (if edgeCount then 8 else 0)
  | .inl 1 => auxiliary t 1
  | .inl 2 => auxiliary t 2
  | .inl 3 => auxiliary t 5
  | .inl 4 => auxiliary t 3
  | .inl 5 => auxiliary t 4
  | .inr i => constantDigit t i

theorem powerRole_injective (t : Nat) (edgeCount : Bool) : Function.Injective (powerRole t edgeCount) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;> cases edgeCount <;> simp_all [powerRole, auxiliary]
    | inr b => fin_cases a <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
  | inr a =>
    cases b with
    | inl b => fin_cases b <;> cases edgeCount <;> simp [powerRole, auxiliary, constantDigit] at h
    | inr b => simpa [powerRole, constantDigit] using h

def powerSlots (t : Nat) (edgeCount : Bool) : MachineHorner.Layout (t + 1) ↪ Tape t :=
  ⟨powerRole t edgeCount, powerRole_injective t edgeCount⟩

def initRole (t : Nat) : MachineOdometerInit.Tape t → Tape t
  | .radix => auxiliary t 8
  | .scratch => .copyScratch
  | .current i => .current i
  | .remaining i => .remaining i

theorem initRole_injective (t : Nat) : Function.Injective (initRole t) := by
  intro a b h
  cases a <;> cases b <;> simp_all [initRole, auxiliary]

def seedCommands (t : Nat) : List (MachineProductSeed.Command (Tape t)) :=
  List.ofFn (fun i : Fin (t + 1) => (constantDigit t i, encodeWord (MachineProductPower.digits i.val)))

noncomputable def clearKeys (t : Nat) : List (Tape t) :=
  Finset.univ.toList.filter (fun k => decide (k ≠ accumulator t ∧ k ≠ output t))

@[simp] theorem mem_clearKeys (t : Nat) (k : Tape t) :
    k ∈ clearKeys t ↔ k ≠ accumulator t ∧ k ≠ output t := by
  simp [clearKeys]

noncomputable section

inductive Label (q t : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | seedStart
  | seed (inner : MachineProductSeed.Label (seedCommands t))
  | power (edgeCount : Bool) (inner : MachineProductPower.Label t)
  | alphabetHeader
  | initialize_ (inner : MachineOdometerInit.Label t)
  | row (inner : MachineProductRow.Label (rowSlots t) (ProductMachineSemantics.commands q t))
  | check (i : Fin t)
  | reset (i : Fin t)
  | finishStart
  | finish (inner : SourceRuntimeFinish.Label (clearKeys t))
  deriving DecidableEq, Fintype

def headerDestination (t : Nat) : Fin 3 → Tape t
  | 0 => auxiliary t 0
  | 1 => auxiliary t 7
  | 2 => auxiliary t 8

def rowMain (q t : Nat) : Label q t :=
  .row (.inl (MachineProductRow.localMain (rowSlots t) (ProductMachineSemantics.sourceCommand t)))

def nextCheck (q t i : Nat) : Label q t := if h : i < t then .check ⟨i, h⟩ else .finishStart

def resetAt (q t i : Nat) : Label q t := if h : i < t then .reset ⟨i, h⟩ else .finishStart

def headerNext (q t : Nat) (i : Fin 3) : Label q t :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .seedStart

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
  | .alphabetHeader => MaxCutGames.Reduction.MachineSubstitution.pushWord (accumulator t)
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

end MaxCutGames.Explicit.MachineProductProgram

/-! Concrete header and initialized work-tape frames for the product machine. -/

namespace MaxCutGames.Explicit.MachineProductHeaders

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
open MachineProductProgram

/-- All permanent input fields and fixed Horner digits are explicit tape words.
The argument is the forward-order emitted already emitted. -/
def frame {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) : Tape t → List Bool
  | .formula => encodeWords (ProductMachineSemantics.inputTable H)
  | .extra (.inl i) =>
      if i = 0 then encodeWord H.vertices
      else if i = 7 then encodeWord q
      else if i = 8 then encodeWord H.constraints.length
      else if i = 6 then emitted.reverse else []
  | .extra (.inr i) => encodeWord (MachineProductPower.digits i.val)
  | _ => []

/-- Canonical frame before the odometer digits are filled. -/
def baseTapes {q : Nat} (H : Instance q) (t : Nat) : Tape t → List Bool :=
  frame H t (headerBits H t)

@[simp] theorem frame_accumulator {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    frame H t emitted (accumulator t) = emitted.reverse := by simp [frame, accumulator, auxiliary]

@[simp] theorem frame_output {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool) :
    frame H t emitted (output t) = [] := by simp [frame, output, auxiliary]

@[simp] theorem frame_radix {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) :
    frame H t emitted (powerSlots t edgeCount (.inl 0)) =
      encodeWord (if edgeCount then H.constraints.length else H.vertices) := by
  cases edgeCount <;> simp [frame, powerSlots, powerRole, auxiliary]

@[simp] theorem frame_digit {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) (i : Fin (t + 1)) :
    frame H t emitted (powerSlots t edgeCount (.inr i)) =
      encodeWord (MachineProductPower.digits i.val) := rfl

theorem power_outside (t : Nat) (edgeCount : Bool) (i : MachineHorner.Layout (t + 1)) :
    accumulator t ≠ powerSlots t edgeCount i := by
  cases i with
  | inl i => fin_cases i <;> cases edgeCount <;> simp [accumulator, powerSlots, powerRole, auxiliary]
  | inr i => simp [accumulator, powerSlots, powerRole, auxiliary, constantDigit]

theorem frame_power_clean {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) : MachineHorner.Clean (powerSlots t edgeCount) (frame H t emitted) := by
  constructor <;> simp [frame, powerSlots, powerRole, auxiliary]

@[simp] theorem frame_power_output {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) : frame H t emitted (powerSlots t edgeCount (.inl 3)) = [] := by
  simp [frame, powerSlots, powerRole, auxiliary]

theorem frame_append {q : Nat} (H : Instance q) (t : Nat) (emitted suffix : List Bool) :
    Function.update (frame H t emitted) (accumulator t)
      (suffix.reverse ++ frame H t emitted (accumulator t)) = frame H t (emitted ++ suffix) := by
  funext tape
  cases tape <;> simp [frame, accumulator, auxiliary, Function.update_apply]
  rename_i extra
  cases extra with
  | inl i =>
    fin_cases i <;> simp []
  | inr i => simp []

/-- The generic odometer initializer has exactly the scheduler's concrete digit
frame; all permanent headers and output-emitted bits retain their identity. -/
theorem initialized_eq {q : Nat} (H : Instance q) (t : Nat) :
    MachineOdometerInit.stageTapes (initRole t) H.constraints.length (baseTapes H t) t =
      SourceOdometerSchedule.setDigits H.constraints.length (fun _ : Fin t => 0) (baseTapes H t) := by
  funext tape
  cases tape with
  | current i =>
    have h := MachineOdometerInit.output_current (initRole t) (initRole_injective t)
      H.constraints.length (baseTapes H t) i
    simpa [initRole, SourceOdometerSchedule.setDigits, i.isLt] using h
  | remaining i =>
    have h := MachineOdometerInit.output_remaining (initRole t) (initRole_injective t)
      H.constraints.length (baseTapes H t) i
    simpa [initRole, SourceOdometerSchedule.setDigits, i.isLt] using h
  | _ =>
    rw [MachineOdometerInit.stageTapes_frame (initRole t) H.constraints.length
      (baseTapes H t) t _ (fun _ => by simp [initRole]) (fun _ => by simp [initRole])]
    rfl

end MaxCutGames.Explicit.MachineProductHeaders

/-! Three actual header reads for the fixed-alphabet, fixed-power product
machine. The constraint table stays in its original order on the formula tape. -/

namespace MaxCutGames.Explicit.MachineProductHeadersRead

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineProductProgram

noncomputable section

def inputTapes (t : Nat) (bits : List Bool) : Tape t → List Bool
  | .formula => bits
  | _ => []

def afterVertices (t n : Nat) (rest : List Bool) : Tape t → List Bool
  | .formula => rest
  | .extra (.inl i) => if i = 0 then encodeWord n else []
  | _ => []

def afterAlphabet (t n q : Nat) (rest : List Bool) : Tape t → List Bool
  | .formula => rest
  | .extra (.inl i) => if i = 0 then encodeWord n else if i = 7 then encodeWord q else []
  | _ => []

def rawResultTapes (t n q m : Nat) (body : List Bool) : Tape t → List Bool
  | .formula => body
  | .extra (.inl i) => if i = 0 then encodeWord n else if i = 7 then encodeWord q
      else if i = 8 then encodeWord m else []
  | _ => []

def resultTapes {q : Nat} (H : Target.Instance q) (t : Nat) : Tape t → List Bool
  | .formula => encodeWords (ProductMachineSemantics.inputTable H)
  | .extra (.inl i) => if i = 0 then encodeWord H.vertices else if i = 7 then encodeWord q
      else if i = 8 then encodeWord H.constraints.length else []
  | _ => []

theorem initList_eq (q t : Nat) (bits : List Bool) :
    initList (machine q t) bits =
      ⟨some (.headerStart 0), (((), ()), none), inputTapes t bits⟩ := by
  unfold initList
  congr 1
  funext k
  (cases k <;> simp [inputTapes, machine]); rfl

theorem first_result (t n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 0)
      (inputTapes t (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes t (encodeWord n ++ rest) (auxiliary t 0)) =
      afterVertices t n rest := by
  funext k
  cases k with
  | extra x =>
    cases x with
    | inl i => fin_cases i <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices, auxiliary]
    | inr i => simp [SourceMachine.fieldTapes, inputTapes, afterVertices, auxiliary]
  | _ => simp [SourceMachine.fieldTapes, inputTapes, afterVertices, auxiliary]

theorem second_result (t n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 7)
      (afterVertices t n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices t n (encodeWord q ++ rest) (auxiliary t 7)) =
      afterAlphabet t n q rest := by
  funext k
  cases k with
  | extra x =>
    cases x with
    | inl i => fin_cases i <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet, auxiliary]
    | inr i => simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet, auxiliary]
  | _ => simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet, auxiliary]

theorem third_result (t n q m : Nat) (body : List Bool) :
    SourceMachine.fieldTapes (SourceContextLoad.Tape.formula : Tape t) (auxiliary t 8)
      (afterAlphabet t n q (encodeWord m ++ body)) body
      (encodeWord m ++ afterAlphabet t n q (encodeWord m ++ body) (auxiliary t 8)) =
      rawResultTapes t n q m body := by
  funext k
  cases k with
  | extra x =>
    cases x with
    | inl i => fin_cases i <;> simp [SourceMachine.fieldTapes, afterAlphabet, rawResultTapes, auxiliary]
    | inr i => simp [SourceMachine.fieldTapes, afterAlphabet, rawResultTapes, auxiliary]
  | _ => simp [SourceMachine.fieldTapes, afterAlphabet, rawResultTapes, auxiliary]

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
  simpa only [FinTM2.step, FinTM2.Cfg, machine, encodeWords,
    List.nil_append, List.append_assoc] using! timed

/-- The exact runtime machine starts on the complete ordinary target game codec
and reaches the seed phase with its untouched row table and three unary headers. -/
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

theorem headers_budget {q : Nat} (H : Target.Instance q) (_t : Nat) :
    H.vertices + q + H.constraints.length + 6 ≤ (gameBits H).length + 3 := by
  simp [gameBits, gameWords, List.length_append, encodeWords]
  omega

end
end MaxCutGames.Explicit.MachineProductHeadersRead

/-! Actual literal initialization of the finitely many product power digits. -/

namespace MaxCutGames.Explicit.MachineProductHeaders

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

theorem seedCommands_nodup (t : Nat) : ((seedCommands t).map Prod.fst).Nodup := by
  simp only [seedCommands, List.map_ofFn, Function.comp_def]
  apply List.nodup_ofFn.mpr
  intro i j same
  simpa [constantDigit] using same

theorem seed_result {q : Nat} (H : Instance q) (t : Nat) :
    MachineProductSeed.finalTapes (seedCommands t)
      (MachineProductHeadersRead.resultTapes H t) = frame H t [] := by
  have unchanged (tape : Tape t) (outside : ∀ i, tape ≠ constantDigit t i) :
      MachineProductSeed.finalTapes (seedCommands t)
        (MachineProductHeadersRead.resultTapes H t) tape =
        MachineProductHeadersRead.resultTapes H t tape := by
    apply MachineProductSeed.finalTapes_frame
    intro command member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact outside i
  funext tape
  cases tape with
  | extra extra =>
    cases extra with
    | inl i =>
      rw [unchanged _ (by intro j; simp [constantDigit])]
      fin_cases i <;> simp [MachineProductHeadersRead.resultTapes, frame]
    | inr i =>
      have run := MachineProductSeed.finalTapes_field (seedCommands t) (seedCommands_nodup t)
        (MachineProductHeadersRead.resultTapes H t)
        (constantDigit t i, encodeWord (MachineProductPower.digits i.val))
        (by apply List.mem_ofFn.mpr; exact ⟨i, rfl⟩)
      simpa [constantDigit, MachineProductHeadersRead.resultTapes, frame] using run
  | _ =>
    rw [unchanged _ (by intro j; simp [constantDigit])]
    rfl

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
end MaxCutGames.Explicit.MachineProductHeaders

/-! The three actual output-header emissions of the product controller. -/

namespace MaxCutGames.Explicit.MachineProductHeaders

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def powerExit (q t : Nat) (edgeCount : Bool) : Label q t :=
  if edgeCount then MachineOdometerInit.labelAt Label.initialize_ 0 else .alphabetHeader

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
end MaxCutGames.Explicit.MachineProductHeaders

/-! Complete actual initialization of the independent-product machine. -/

namespace MaxCutGames.Explicit.MachineProductHeaders

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
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

def steps {q : Nat} (H : Instance q) (t : Nat) : Nat :=
  H.vertices + q + H.constraints.length + 6 + (t + 2) +
    (MachineProductPower.steps H.vertices t + 1 + MachineProductPower.steps H.constraints.length t) +
    (t * (2 * H.constraints.length + 6) + 1)

/-- Header reading, literal seed setup, actual Horner power computation, and
all odometer digits are supplied by real execution traces of the same program. -/
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

theorem steps_le {q : Nat} (H : Instance q) (t : Nat) :
    steps H t ≤ (timePolynomial t).eval (gameBits H).length := by
  have headerBound := MachineProductHeadersRead.headers_budget H t
  have hn : H.vertices ≤ (gameBits H).length + 1 := by omega
  have hm : H.constraints.length ≤ (gameBits H).length + 1 := by omega
  have hm' : H.constraints.length ≤ (gameBits H).length := by omega
  have first := MachineProductPower.steps_le H.vertices t ((gameBits H).length + 1) hn (by omega)
  have second := MachineProductPower.steps_le H.constraints.length t ((gameBits H).length + 1) hm (by omega)
  have initialization := Nat.mul_le_mul_left t (show 2 * H.constraints.length + 6 ≤
      2 * (gameBits H).length + 6 by omega)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold steps
  omega

/-- Polynomial initialization in the literal incoming instance-code length. -/
def inPolynomialTime {q : Nat} (H : Instance q) (t : Nat) :
    StateTransition.EvalsToInTime (machine q t).step
      (initList (machine q t) (gameBits H))
      (some (SourceOdometerSchedule.initialConfiguration (m := H.constraints.length)
        t (rowMain q t) ((), ()) (baseTapes H t)))
      ((timePolynomial t).eval (gameBits H).length) :=
  { toEvalsTo := (prepareInTime H t).toEvalsTo
    steps_le_m := (prepareInTime H t).steps_le_m.trans (steps_le H t) }

end
end MaxCutGames.Explicit.MachineProductHeaders

/-! Polynomial bounds for actual field and row traces. The output accumulator
is excluded from local cleanup and is never rescanned by row emission. -/

namespace MaxCutGames.Explicit.MachineProductBounds

open MaxCutGames.Foundations.Complexity

variable {K : Type} [DecidableEq K] {width : Nat}

@[simp] theorem fieldPolynomial_eval (width magnitude : Nat) :
    (fieldPolynomial width).eval magnitude =
      width * (7 * magnitude + 6) + 1 + (MachineHorner.timePolynomial width).eval magnitude +
        (magnitude + 1) ^ width + 2 + (width + 2) * (width * (magnitude + 1) + 1) := by
  simp [fieldPolynomial]

theorem field_steps_le (slots : MachineProductField.Layout width ↪ K) (table : List Nat)
    (coefficient : Nat) (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, table[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : MachineProductField.Ready slots base)
    (radix : Nat) (digits : Nat → Nat) (magnitude : Nat)
    (tableBound : (encodeWords table).length ≤ magnitude)
    (indexBound : ∀ i, indices i ≤ magnitude) (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    MachineProductField.steps slots table coefficient indices offsets fields base radix digits ≤
      (fieldPolynomial width).eval magnitude := by
  have gather := MachineProductGather.steps_le table coefficient width magnitude indices offsets fields selected indexBound
  have horner := MachineHorner.steps_le_timePolynomial radix digits width magnitude radixBound digitBound
  have value := MachineHorner.value_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  have cleanup := MachineProductField.cleanup_steps_le slots table coefficient indices offsets fields selected
    base ready (MachineHorner.value radix digits width)
  have gatherBound : width * (2 * magnitude + 5 * (encodeWords table).length + 6) + 1 ≤
      width * (7 * magnitude + 6) + 1 := by gcongr; omega
  have cleanupBound : (width + 2) * (width * ((encodeWords table).length + 1) + 1) ≤
      (width + 2) * (width * (magnitude + 1) + 1) := by gcongr
  rw [fieldPolynomial_eval]
  unfold MachineProductField.steps
  omega

theorem row_steps_le (slots : MachineProductRow.Layout width ↪ K) (table : List Nat)
    (coefficient : Nat) (indices : Fin width → Nat) (radices : Bool → Nat)
    (commands : List (MachineProductRow.Command width))
    (fields : MachineProductRow.Command width → Fin width → Nat)
    (digits : MachineProductRow.Command width → Nat → Nat)
    (selected : ∀ c ∈ commands, ∀ i, table[coefficient * indices i + c.2 i]? = some (fields c i))
    (base : K → List Bool) (ready : MachineProductRow.Ready slots table indices radices base)
    (magnitude : Nat) (tableBound : (encodeWords table).length ≤ magnitude)
    (indexBound : ∀ i, indices i ≤ magnitude) (radixBound : ∀ b, radices b ≤ magnitude)
    (digitBound : ∀ c ∈ commands, ∀ i, i < width → digits c i ≤ magnitude) :
    MachineFiniteSequence.steps
      (MachineProductRow.result slots (fun c => MachineHorner.value (radices c.1) (digits c) width))
      (rowCost slots table coefficient indices radices fields digits) commands base ≤
      commands.length * (fieldPolynomial width).eval magnitude := by
  induction commands generalizing base with
  | nil => simp [MachineFiniteSequence.steps]
  | cons command commands ih =>
    have first := field_steps_le (MachineProductRow.fieldSlots slots command.1) table coefficient
      indices command.2 (fields command) (selected command (by simp)) base (ready.work command.1)
      (radices command.1) (digits command) magnitude tableBound indexBound (radixBound command.1)
      (digitBound command (by simp))
    have nextReady := MachineProductRow.Ready.appendField slots table indices radices base ready
      (MachineHorner.value (radices command.1) (digits command) width)
    have rest := ih (fun c hc => selected c (by simp [hc]))
      (MachineProductRow.result slots (fun c => MachineHorner.value (radices c.1) (digits c) width)
        command base) nextReady (fun c hc => digitBound c (by simp [hc]))
    rw [MachineFiniteSequence.steps, List.length_cons, Nat.add_mul, Nat.one_mul]
    simpa only [Nat.add_comm, rowCost] using Nat.add_le_add first rest

end MaxCutGames.Explicit.MachineProductBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineProductLoop
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole tuple traversal of the concrete product program. The odometer theorem
is instantiated by the proved actual row trace, not by an assumed row machine. -/

namespace MaxCutGames.Explicit.MachineProductLoop

open Turing
open MaxCutGames.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram

variable {q t : Nat}

noncomputable section

structure BaseReady (H : Target.Instance q) (base : Tape t → List Bool) : Prop where
  work : ∀ b, MachineProductField.Ready (MachineProductRow.fieldSlots (rowSlots t) b) base
  table : base .formula = encodeWords (ProductMachineSemantics.inputTable H)
  vertices : base (auxiliary t 0) = encodeWord H.vertices
  alphabet : base (auxiliary t 7) = encodeWord q

def tupleTapes (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) : Tape t → List Bool :=
  SourceOdometerSchedule.setDigits H.constraints.length (fun i => (edges i).val)
    (SourceOdometerSchedule.setAcc (Sum.inl (6 : Fin 10)) base out)

theorem tupleTapes_frame (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) (k : Tape t)
    (hc : ∀ i, k ≠ .current i) (hr : ∀ i, k ≠ .remaining i)
    (ha : k ≠ accumulator t) : tupleTapes H base edges out k = base k := by
  cases k with
  | current i => exact (hc i rfl).elim
  | remaining i => exact (hr i rfl).elim
  | extra x =>
    simp only [tupleTapes, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]
    exact Function.update_of_ne ha _ _
  | _ => simp [tupleTapes, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]

@[simp] theorem tupleTapes_current (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) (i : Fin t) :
    tupleTapes H base edges out (.current i) = encodeWord (edges i).val := by
  simp [tupleTapes, SourceOdometerSchedule.setDigits, i.isLt]

@[simp] theorem tupleTapes_accumulator (H : Target.Instance q) (base : Tape t → List Bool)
    (edges : Fin t → Fin H.constraints.length) (out : List Bool) :
    tupleTapes H base edges out (accumulator t) = out := by
  simp [tupleTapes, accumulator, auxiliary, SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc]

theorem tupleTapes_ready (H : Target.Instance q) (base : Tape t → List Bool)
    (ready : BaseReady H base) (edges : Fin t → Fin H.constraints.length) (out : List Bool) :
    MachineProductRow.Ready (rowSlots t) (ProductMachineSemantics.inputTable H)
      (fun i => (edges i).val) (fun b => if b then q else H.vertices) (tupleTapes H base edges out) := by
  have other (k : Tape t) (hc : ∀ i, k ≠ .current i) (hr : ∀ i, k ≠ .remaining i)
      (ha : k ≠ accumulator t) := tupleTapes_frame H base edges out k hc hr ha
  constructor
  · intro b
    have work := ready.work b
    constructor
    · change tupleTapes H base edges out .index = []
      rw [other .index (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.query
    · change tupleTapes H base edges out .work = []
      rw [other .work (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.scan
    · change tupleTapes H base edges out .scratch = []
      rw [other .scratch (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.gatherScratch
    · intro i
      change tupleTapes H base edges out (.field i 0) = []
      rw [other (.field i 0) (by simp) (by simp) (by simp [accumulator, auxiliary])]
      exact work.fields i
    · change tupleTapes H base edges out (auxiliary t 1) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.accA
    · change tupleTapes H base edges out (auxiliary t 2) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.accB
    · change tupleTapes H base edges out (auxiliary t 3) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.counter
    · change tupleTapes H base edges out (auxiliary t 4) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.hornerScratch
    · change tupleTapes H base edges out (auxiliary t 5) = []
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact work.output
  · change tupleTapes H base edges out .formula = _
    rw [other .formula (by simp) (by simp) (by simp [accumulator, auxiliary])]
    exact ready.table
  · intro i; exact tupleTapes_current H base edges out i
  · intro b
    cases b
    · change tupleTapes H base edges out (auxiliary t 0) = _
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact ready.vertices
    · change tupleTapes H base edges out (auxiliary t 7) = _
      rw [other _ (by simp [auxiliary]) (by simp [auxiliary]) (by simp [accumulator, auxiliary])]
      exact ready.alphabet

def rowBits (H : Target.Instance q) (edges : Fin t → Fin H.constraints.length) : List Bool :=
  MachineProductRow.rowBits (ProductMachineSemantics.fieldValue H edges)
    (ProductMachineSemantics.commands q t)

theorem input_length (H : Target.Instance q) :
    (gameBits H).length = H.vertices + q + H.constraints.length + 3 +
      (encodeWords (ProductMachineSemantics.inputTable H)).length := by
  simp [gameBits, gameWords, ProductMachineSemantics.inputTable,
    encodeWords, encodeWord_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] ; omega

def bodyBound (H : Target.Instance q) (t : Nat) : Nat :=
  (q ^ t + 2) * (MachineProductBounds.fieldPolynomial t).eval (gameBits H).length

/-- The actual row execution supplies the local obligation of the generic
odometer schedule. Its cost is uniformly polynomial in the original bits. -/
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
      ((rowBits H edges).reverse ++ frame (MachineProductRow.outputTape (rowSlots t)))⟩ : (machine q t).Cfg) at run
  erw [hframe] at run
  exact run

/-- Complete positive-radix tuple traversal with actual row bodies discharged. -/
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

end MaxCutGames.Explicit.MachineProductLoop

/-! Exact final cleanup and binary-output identification for the product
controller. The final runtime bound is derived from actual stack lengths. -/

namespace MaxCutGames.Explicit.MachineProductFinish

open Turing
open MaxCutGames.Foundations
open Complexity Hastad
open MachineComposition
open MachineProductProgram

variable {q t : Nat}

noncomputable section

theorem base_ready (H : Target.Instance q) (t : Nat) :
    MachineProductLoop.BaseReady H (MachineProductHeaders.baseTapes H t) := by
  constructor
  · intro b
    constructor <;> simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame,
      MachineProductRow.fieldSlots, MachineProductRow.fieldRole, rowSlots] <;> (intros; rfl)
  · rfl
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]

def afterRows (H : Target.Instance q) (t : Nat) : (machine q t).Cfg :=
  SourceOdometerSchedule.finalConfiguration (nextCheck q t t) ((), ())
    (Sum.inl (6 : Fin 10)) (MachineProductHeaders.baseTapes H t) (MachineProductLoop.rowBits (t := t) H)

theorem afterRows_output (H : Target.Instance q) (t : Nat) :
    (afterRows H t).stk (output t) = [] := by
  simp [afterRows, SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration,
    SourceOdometerSchedule.setDigits, SourceOdometerSchedule.setAcc, output, auxiliary,
    MachineProductHeaders.baseTapes, MachineProductHeaders.frame]
  rfl

theorem allRows_eq (H : Target.Instance q) (t : Nat) :
    (MachineTupleOdometer.tupleOrder H.constraints.length t).flatMap (MachineProductLoop.rowBits (t := t) H) =
      ProductMachineSemantics.allRowsBits H t := by
  simp only [MachineTupleOdometer.tupleOrder, ProductMachineSemantics.allRowsBits,
    List.ofFn_eq_map, List.flatMap_map, MachineProductLoop.rowBits]

theorem afterRows_accumulator (H : Target.Instance q)
    (presentation : MachineOutputContract.SimpleBipartite H) (t : Nat) (ht : 0 < t) :
    ((afterRows H t).stk (accumulator t)).reverse =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  change ((SourceOdometerSchedule.allBits (MachineProductLoop.rowBits (t := t) H)).reverse ++
    MachineProductHeaders.baseTapes H t (accumulator t)).reverse = _
  rw [MachineProductHeaders.baseTapes, MachineProductHeaders.frame_accumulator,
    List.reverse_append, List.reverse_reverse, List.reverse_reverse]
  rw [SourceOdometerSchedule.allBits, allRows_eq]
  exact ProductMachineSemantics.gameBits_eq H presentation t ht

/-- The entry hop reaches the actual cleanup list, then all work is drained,
the accumulator is reversed, and the final finite register is reset. -/
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
    simp only [program, MaxCutGames.Reduction.MachineTransfer.exitAt]
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
  erw [afterRows_accumulator H presentation t ht] at run
  have hstart : (afterRows H t).l = some .finishStart := by simp [afterRows,
    SourceOdometerSchedule.finalConfiguration, SourceOdometerSchedule.configuration, nextCheck]
  have hstate : (afterRows H t).var = (((), ()), none) := rfl
  have halt : (⟨none, (((), ()), none), SourceRuntimeFinish.canonicalTapes (output t)
      (gameBits (ProductPaddedOutput.output H presentation t ht))⟩ : (machine q t).Cfg) =
      haltList (machine q t) (gameBits (ProductPaddedOutput.output H presentation t ht)) := by
    unfold haltList SourceRuntimeFinish.canonicalTapes
    congr 1
    funext k
    by_cases hk : k = output t
    · subst k
      simp only [machine]
      erw [Function.update_self]
      rfl
    · simp only [machine]
      erw [Function.update_of_ne hk, dite_eq_right hk]
  erw [halt] at run
  have hcfg : (⟨some .finishStart, (((), ()), none), (afterRows H t).stk⟩ : (machine q t).Cfg) =
      afterRows H t := by cases h : afterRows H t; simp_all
  erw [hcfg] at run
  exact ⟨run⟩

end

end MaxCutGames.Explicit.MachineProductFinish

/-! The complete explicit product computation. Every execution phase is supplied
by the actual controller; the cleanup bound follows from the space reached by
its actual prefix. The exponent and alphabet enter only the fixed program. -/

namespace MaxCutGames.Explicit.MachineProductRuntime

open Turing
open MaxCutGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def loopPolynomial (q t : Nat) : Polynomial Nat :=
  (Polynomial.C (q ^ t + 2) * MachineProductBounds.fieldPolynomial t +
    Polynomial.C (2 * t)) * Polynomial.X ^ t

theorem loop_budget {q : Nat} (H : Instance q) (t : Nat) :
    (MachineProductLoop.bodyBound H t + 2 * t) * H.constraints.length ^ t ≤
      (loopPolynomial q t).eval (gameBits H).length := by
  have hlen := MachineProductLoop.input_length H
  have hm : H.constraints.length ≤ (gameBits H).length := by omega
  simp only [loopPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm t)

def prefixPolynomial (q t : Nat) : Polynomial Nat :=
  MachineProductHeaders.timePolynomial t + loopPolynomial q t

/-- Actual header initialization followed by every product row and odometer step. -/
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

/-- The complete run produces the literal full-table target code, clears all
private stacks, resets its finite state, and halts. -/
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
  have bound : SourceRuntimeFinish.finishCost (clearKeys t) (accumulator t)
      (MachineProductFinish.afterRows H t).stk ≤ (gameBits H).length +
        (prefixPolynomial q t).eval (gameBits H).length *
          (@Fintype.card (machine q t).K (machine q t).kFin * Runtime.programPushBound (machine q t)) +
        (clearKeys t).length + 2 :=
    SourceRuntimeSpace.finishCost_le_of_prefix (machine q t) (gameBits H)
    initialRun (clearKeys t) (accumulator t) (output t)
    keepAccumulator keepOutput covers
    (MachineProductFinish.afterRows H t).stk (MachineProductFinish.afterRows_output H t)
    (fun _ => rfl)
  change StateTransition.EvalsToInTime (machine q t).step _
    (some (haltList (machine q t) _)) _
  refine { toEvalsTo := whole.toEvalsTo, steps_le_m := whole.steps_le_m.trans ?_ }
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one,
    SourceRuntimeSpace.completedTime_eval]
  omega

/-- The bipartition is proof-side data. Its codec is exactly the underlying
instance code and the fixed program does not inspect it. -/
abbrev Input (q : Nat) := Σ H : Instance q, MachineOutputContract.SimpleBipartite H

def construct {q : Nat} (t : Nat) (ht : 0 < t) (H : Input q) : Instance (q ^ t) :=
  ProductPaddedOutput.output H.1 H.2 t ht

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
    have hi := @List.map_id ((machine q t).Γ (machine q t).k₀) (gameBits H.1)
    have ho := @List.map_id ((machine q t).Γ (machine q t).k₁) (gameBits (construct t ht H))
    simp only [hi, ho]
    exact outputInTime H.1 H.2 t ht

theorem finiteAlphabet (q t : Nat) (ht : 0 < t) :
    MachineFiniteAlphabet.FiniteAlphabet (computation q t ht).tm :=
  MachineFiniteAlphabet.of_bool _ (fun _ => rfl)

variable {A : Type} {q : Nat} {encode : A → List Bool} {f : A → Instance q}

def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (presentation : ∀ a, MachineOutputContract.SimpleBipartite (f a)) :
    TM2ComputableInPolyTime encode (fun H : Input q => gameBits H.1)
      (fun a => ⟨f a, presentation a⟩) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

/-- Direct composition with an actual preceding simple-bipartite producer. -/
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

end MaxCutGames.Explicit.MachineProductRuntime

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_PaddedLaw
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual linear-map realization of the sparse padded-table experiment.
The finite sample has one independent full pair or singleton coefficient at
each occurrence position and one independent homogeneous intercept. Its map
is formed by composing a genuine map on the raw projected target with the
actual parity projection. The third position contributes its parity-dependent
intercept; it is not treated as a homogeneous two-coordinate projection.
-/

namespace MaxCutGames.Decoder.PaddedLaw

open scoped BigOperators
open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget RawMapLaw
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

variable [Fintype V]

def paddedWeights (rhs : Fin k → Bool) (β : ℝ) : ActualEnumeration.Coefficients k V → ℝ :=
  pushforwardWeight (drawWeights β k)
    (fun dz => ActualEnumeration.toCoefficients k V (paddedMap rhs dz.1 dz.2))

variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

def paddedMapWeights (rhs : Fin k → Bool) (β : ℝ) :
    (ActualHomogeneous.E k →ₗ[F2] V) → ℝ :=
  pushforwardWeight (drawWeights β k) (fun dz => paddedMap rhs dz.1 dz.2)

end
end MaxCutGames.Decoder.PaddedLaw

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_PrivateFourier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Decoder.PrivateFourier

open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Fourier.MatrixFourier
open scoped BigOperators Classical

section AffineSlice

variable {E H V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)]

/-- Frequencies in the affine target's annihilator coset.  With `q = Q.mkQ`,
this is exactly `θ + Hom(H,Q)` in the ambient reverse-map space. -/
def frequencyCoset (q : E →ₗ[F2] V) (θ : H →ₗ[F2] E) :
    Finset (H →ₗ[F2] E) := Finset.univ.filter fun Φ => q.comp (Φ + θ) = 0

/-- Correlation on a genuine affine slice.  `N₀` is retained: its phase cannot
be discarded when the witness has a nonzero affine intercept. -/
def sliceCorrelation (q : E →ₗ[F2] V) (N₀ : E →ₗ[F2] H)
    (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) : ℝ :=
  𝔼 A : V →ₗ[F2] H,
    f (N₀ + A.comp q) * (linearTraceCharacter θ (N₀ + A.comp q)).re

end AffineSlice

end MaxCutGames.Decoder.PrivateFourier

/-!
# Actual private response laws for v2 Fourier decoding

The right response law has only its row-fiber table, the inclusion of its hidden
kernel, a first-bit map, and an actual fallback answer as arguments.  In
particular it has no column slice or witness.  Zero-mass invalid frequencies
are repaired to the fallback so that the response type always consists of
actual answers.  Witness data occur only in the success analysis.
-/

namespace MaxCutGames.Decoder.PrivateStrategy

attribute [local instance] Classical.propDecidable

open PrivateFourier
open MaxCutGames.Fourier.MatrixCharacters
open MaxCutGames.Foundations.Games
open scoped BigOperators Classical

section ConditionalAgreement

variable {U E H K : Type*}
variable [AddCommGroup U] [Module F2 U] [Fintype U]
variable [AddCommGroup E] [Module F2 E] [Fintype E]
variable [AddCommGroup H] [Module F2 H]
variable [AddCommGroup K] [Module F2 K]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (K →ₗ[F2] F2)]

/-- Actual independent response-law success, with the literal projection test. -/
def conditionalAgreement (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) : ℝ :=
  ((candidateLaw Z z τU hz).product (privateLaw F ι τ fallback)).probability
    (fun a => decide (π a.1.1 = a.2.1))

/-- The exact good Fourier mass in a witness coset; unlike the response law,
this analysis-only quantity is allowed to mention the witness. -/
def goodCosetMass (Q : Submodule F2 E) (z' : E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K) : ℝ :=
  𝔼 σ : K →ₗ[F2] F2, if σ.comp ι ≠ 0 then
    ∑ Φ ∈ frequencyCoset Q.mkQ ((σ.comp ι).smulRight z'),
      frequencyWeight (tableSign F σ) Φ else 0

end ConditionalAgreement

end MaxCutGames.Decoder.PrivateStrategy
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TableKeysGame
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.TableKeysGame

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction
open ActualSource Foundations.Target
open scoped BigOperators

theorem edge_satisfied_iff (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (ω : Outcome S k g) :
    (edge S k g ω).satisfied labeling = true ↔
      unfolded S k s d labeling (leftQuery S k g ω) =
        unfolded S k s d labeling (rightQuery S k g ω) := by
  rw [Constraint.satisfied, decide_eq_true_eq]
  have h := Encoding.translationTable_satisfied_iff
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))
    (vertexLabel S k s d labeling (vertex S k s d (leftQuery S k g ω)))
    (vertexLabel S k s d labeling (vertex S k s d (rightQuery S k g ω)))
  simp only [vertexLabel, Encoding.alphabetEquiv_apply_symm_apply] at h
  exact h.trans (ActualOrbit.constraint_iff_unfolded (canonical S k s d)
    (vertexLabel S k s d labeling) (vertexLabel S k s d labeling) _ _)

theorem acceptanceProbability_eq_test (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      𝔼 ω : Outcome S k g,
        if unfolded S k s d labeling (leftQuery S k g ω) =
            unfolded S k s d labeling (rightQuery S k g ω)
        then (1 : ℚ) else 0 := by
  unfold acceptanceProbability
  apply Finset.expect_congr rfl
  intro ω _
  simp only [edge_satisfied_iff]

end MaxCutGames.Decoder.TableKeysGame

/-!
Restore actual orbit labels as a total function of the entire reduced key.
The arbitrary value at unrealized orbit bodies is used only to make this
function total; every table queried by the verifier and by the sparse
experiment is proved to be an actual realization.  Folding holds even for
the total extension, because the removed intercept is always restored.
-/

/-!
The private row table obtained from an actual single-orbit labeling.  Its
parameters are only the visible question, public row map, visible row value,
and complement table.  Neither a hidden full question nor a selected affine
witness is supplied to its definition.  Affine target intercepts remain
explicit when the matrix is expressed in private kernel coordinates.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_ActualCompleteness
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-distribution identities for completeness. -/
namespace MaxCutGames.Reduction.ActualCompleteness

open MaxCutGames.Integration.BinaryLinear
open scoped BigOperators

open ActualSource

noncomputable section

/-- Equivariance recovers the dropped alphabet component exactly. -/
theorem honest_unfolded (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) (side : Bool) (q : ActualGame.Query S k s d) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (evaluate (ActualGame.names S) (fun n => ofBit (A n))
        (ActualGame.canonical S k s d q)) := by
  simp only [honestLabeling, ActualGame.unfolded, ActualGame.sideLabel_labelingOf,
    ActualOrbit.unfold]
  let z := (ActualGame.canonical S k s d q).1
  let r := ∑ j, evalRecord (ActualGame.names S) (fun n => ofBit (A n))
    ((ActualGame.canonical S k s d q).2 j)
  change g.f ((0, z.2) + r) + z.1 = g.f (z + r)
  have hsplit : ((0, z.2) + r) + (z.1, 0) = z + r := by
    apply Prod.ext <;> simp [add_comm]
  have h := g.equivariant ((0, z.2) + r) z.1
  rw [hsplit] at h
  exact h.symm

theorem honest_unfolded_valid (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.«variables» → Bool) (side : Bool) (q : ActualGame.Query S k s d)
    (hgood : ∀ j, S.satisfied A (q.1 j) = true) :
    ActualGame.unfolded S k s d (honestLabeling S k g A) side q =
      g.f (q.2 (sourcePoint S k A q.1)) := by
  rw [honest_unfolded]
  apply congrArg g.f
  exact canonical_evaluate q.1 (ActualGame.names S) (ActualGame.rhs S)
    (fun n => ofBit (A n)) q.2 (fun j => satisfied_parity S A (q.1 j) (hgood j))

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      ActualGame.acceptanceProbability S k g (honestLabeling S k g A) := by
  classical
  let P (ω : ActualGame.Outcome S k g) : Prop :=
    ActualGame.unfolded S k s d (honestLabeling S k g A) false
        (ActualGame.leftQuery S k g ω) =
      ActualGame.unfolded S k s d (honestLabeling S k g A) true
        (ActualGame.rightQuery S k g ω)
  let bad (ω : ActualGame.Outcome S k g) : ℚ :=
    if ∀ j, S.satisfied A (ω.1.1 j) = true then 0 else 1
  let noiseBad (ω : ActualGame.Outcome S k g) : ℚ :=
    if g.f (ω.1.2 (sourcePoint S k A ω.1.1) +
        ω.2.2 (sourcePoint S k A ω.1.1) • g.noise ω.2.1) =
      g.f (ω.1.2 (sourcePoint S k A ω.1.1)) then 0 else 1
  have hpoint (ω : ActualGame.Outcome S k g) :
      (if P ω then (0 : ℚ) else 1) ≤ bad ω + noiseBad ω := by
    by_cases hgood : ∀ j, S.satisfied A (ω.1.1 j) = true
    · have hL := honest_unfolded_valid S k g A false (ActualGame.leftQuery S k g ω) hgood
      have hR := honest_unfolded_valid S k g A true (ActualGame.rightQuery S k g ω) hgood
      simp only [P, hL, hR, bad, ite_eq_left hgood, zero_add]
      simp [noiseBad, ActualGame.leftQuery, ActualGame.rightQuery,
        LinearMap.add_apply, LinearMap.smulRight_apply, eq_comm]
      exact le_rfl
    · have hn : 0 ≤ noiseBad ω := by dsimp [noiseBad]; split <;> norm_num
      have hf : (if P ω then (0 : ℚ) else 1) ≤ 1 := by split <;> norm_num
      simpa only [bad, ite_eq_right hgood] using hf.trans (le_add_of_nonneg_right hn)
  have hbad : (𝔼 ω : ActualGame.Outcome S k g, bad ω) = tupleFailure S A k := by
    simp only [expect_pair_inline_ActualCompleteness, bad]
    change (𝔼 U : ActualGame.Question S k, 𝔼 _X : ActualGame.Map k s d,
      𝔼 _i : g.NoiseIndex, 𝔼 _ell : ActualGame.Dual k,
      if ∀ j, S.satisfied A (U j) = true then (0 : ℚ) else 1) = _
    simp_rw [Fintype.expect_const]
    rfl
  have hnoise : (𝔼 ω : ActualGame.Outcome S k g, noiseBad ω) = g.stabilityError / 2 := by
    simp only [expect_pair_inline_ActualCompleteness]
    change (𝔼 U : ActualGame.Question S k, localNoiseFailure g (sourcePoint S k A U)) = _
    have hu (U : ActualGame.Question S k) := localNoiseFailure_eq_half g
      ActualHomogeneous.tau (sourcePoint S k A U) (sourcePoint_tau S k A U)
    simp only [hu, Fintype.expect_const]
  have hfailure : (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) ≤
      tupleFailure S A k + g.stabilityError / 2 := by
    calc
      _ ≤ 𝔼 ω : ActualGame.Outcome S k g, (bad ω + noiseBad ω) :=
        Finset.expect_le_expect (fun ω _ => hpoint ω)
      _ = _ := by rw [Finset.expect_add_distrib, hbad, hnoise]
  have hsum : ActualGame.acceptanceProbability S k g (honestLabeling S k g A) +
      (𝔼 ω : ActualGame.Outcome S k g, if P ω then (0 : ℚ) else 1) = 1 := by
    rw [ActualGame.acceptanceProbability_eq_test]
    change (𝔼 ω : ActualGame.Outcome S k g, if P ω then (1 : ℚ) else 0) + _ = _
    rw [← Finset.expect_add_distrib]
    have hp (ω : ActualGame.Outcome S k g) :
        (if P ω then (1 : ℚ) else 0) + (if P ω then (0 : ℚ) else 1) = 1 := by
      split <;> norm_num
    simp only [hp, Fintype.expect_const]
  have htuple := tupleFailure_le S A k
  linarith

end

end MaxCutGames.Reduction.ActualCompleteness

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TableKeysCompleteness
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Completeness of the v2 single-orbit matrix game. The generic finite-average
calculation is shared with the proved actual completeness calculation. Its
reuse is justified below by pointwise equality of restored answers under
diagonal labels; the output vertices themselves are never doubled.

No gadget existence, dispersion hypothesis, inverse theorem, or legacy
soundness theorem is a premise. The bound includes the exact fair-bit factor
`1 / 2`, and is a statement about the actual finite edge occurrence list.
-/

namespace MaxCutGames.Decoder.TableKeysCompleteness

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction
open ActualSource Foundations.Target
open TableKeysGame
open scoped BigOperators

noncomputable section

theorem diagonal_unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (side : Bool) (q : Query S k s d) :
    ActualGame.unfolded S k s d (diagonalLabeling S k s d labeling) side q =
      unfolded S k s d labeling q := by
  simp only [diagonalLabeling, ActualGame.unfolded,
    ActualGame.sideLabel_labelingOf, unfolded, canonical]

/-- Pointwise-identical matrix tests have exactly the same acceptance average. -/
theorem acceptanceProbability_eq_diagonal (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      ActualGame.acceptanceProbability S k g (diagonalLabeling S k s d labeling) := by
  rw [acceptanceProbability_eq_test, ActualGame.acceptanceProbability_eq_test]
  simp only [diagonal_unfolded, leftQuery, rightQuery]

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      acceptanceProbability S k g (honestLabeling S k g A) := by
  rw [acceptanceProbability_eq_diagonal, diagonal_honestLabeling]
  exact ActualCompleteness.honest_acceptance_bound S k g A

theorem honest_acceptance_of_bounds (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.«variables» → Bool) (ξ p ε : ℚ)
    (hsource : S.failure A ≤ ξ) (hstable : g.stabilityError ≤ p)
    (hbudget : (k : ℚ) * ξ + p / 2 ≤ ε) :
    1 - ε ≤ acceptanceProbability S k g (honestLabeling S k g A) := by
  have hm := mul_le_mul_of_nonneg_left hsource (show (0 : ℚ) ≤ k by positivity)
  have hactual := honest_acceptance_bound S k g A
  linarith

end

end MaxCutGames.Decoder.TableKeysCompleteness

/-! Internal serialization of canonical orbit bodies. Each record occupies nine
natural-number words, so record boundaries are independent of the tag. The
outer complement coordinate occupies one leading word. These are injectivity,
deduplication, and output-size statements, not machine running-time claims. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_TableKeysAddressGame
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Direct addresses for the v2 single-orbit matrix game. There is one canonical
body address space, with no side bit and no extra right-endpoint offset.
Unused addresses are isolated. Runtime construction uses canonical words and
radix arithmetic, not deduplication or inverse vertex enumeration.
-/

namespace MaxCutGames.Decoder.TableKeysAddressGame

open MaxCutGames.Reduction
open ActualSource Foundations.Target
open Integration.VertexEmbedding

theorem vertexAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (vertexAddress S k s d) := by
  intro v w h
  apply Subtype.ext
  exact CanonicalAddress.bodyAddress_injective h

theorem explicitToAddress_injective (S : Source) (k s d : Nat) :
    Function.Injective (explicitToAddress S k s d) :=
  (vertexAddress_injective S k s d).comp
    (TableKeysGame.explicitVertexEncoding S k s d).symm.injective

theorem addressEdge_eq_embed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : TableKeysGame.Outcome S k g) :
    addressEdge S k g ω = embedConstraint (explicitToAddress S k s d)
      (TableKeysGame.explicitEdge S k g ω) := by
  simp only [addressEdge, embedConstraint, TableKeysGame.explicitEdge,
    explicitToAddress_apply, vertexAddress_query]

theorem outputInstance_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    countSatisfied labeling (outputInstance S k g en).constraints =
      countSatisfied (labeling ∘ explicitToAddress S k s d)
        (TableKeysGame.outputInstanceWithEnumeration S k g en).constraints := by
  simpa only [outputInstance, TableKeysGame.outputInstanceWithEnumeration, List.map_map,
    Function.comp_def, ← addressEdge_eq_embed] using
    count_map (explicitToAddress S k s d)
      ((ActualGame.explicitOutcomes S k g en).map (TableKeysGame.explicitEdge S k g)) labeling

theorem outputInstance_translations (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (outputInstance S k g en) := by
  intro constraint hconstraint
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hconstraint
  refine ⟨TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω) +
    TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω), ?_⟩
  intro label
  have h := Encoding.translationTable_images
    (TableKeysGame.offset S k s d (TableKeysGame.leftQuery S k g ω))
    (TableKeysGame.offset S k s d (TableKeysGame.rightQuery S k g ω))
    ((Encoding.alphabetEquiv s).symm label)
  simpa only [addressEdge, Encoding.alphabetEquiv_apply_symm_apply,
    Encoding.alphabetEquiv_symm_apply_apply, add_assoc] using
    congrArg (Encoding.alphabetEquiv s).symm h

/-- Fixed finite noise data suffice for executable output. -/
def tableOutput (S : Source) (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    Instance (2^s) :=
  outputInstance S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

/-- The nonlinear correctness witness is erased from the output program. -/
theorem tableOutput_eq_with_witness (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c) :
    tableOutput S k T = outputInstance S k (T.gadget f hf)
      (Integration.TableReduction.tableEnumeration T f hf) := by
  rfl

theorem tableOutput_translations (S : Source) (k : Nat) {s d : Nat}
    (T : Integration.NoiseTables.Table s d) :
    Integration.TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv s).symm
      (tableOutput S k T) := outputInstance_translations S k _ _

end MaxCutGames.Decoder.TableKeysAddressGame

/-! Transport the matrix-test bound to the actual direct-address edge list.
Every address labeling restricts to a semantic orbit labeling, with exactly
the same satisfied fraction and the same occurrence multiplicities. -/

namespace MaxCutGames.Decoder.MatrixGap

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Foundations.Target
open MaxCutGames.Integration
open ActualSource

noncomputable section

theorem address_rate_eq_semantic_acceptance (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysAddressGame.vertexCount S k s d) → Fin (2 ^ s)) :
    GapSemantics.satisfactionRate (TableKeysAddressGame.outputInstance S k g en) labeling =
      TableKeysGame.acceptanceProbability S k g
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) := by
  calc
    _ = GapSemantics.satisfactionRate
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) := by
      unfold GapSemantics.satisfactionRate
      exact congrArg₂ (fun a b : Nat => (a : ℚ) / b)
        (TableKeysAddressGame.outputInstance_count S k g en labeling)
        (by simp only [TableKeysAddressGame.outputInstance,
          TableKeysGame.outputInstanceWithEnumeration, List.length_map])
    _ = GapSemantics.satisfactionRate (TableKeysGame.outputInstance S k g)
        ((labeling ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
          TableKeysGame.semanticToExplicitVertices S k s d) :=
      InstanceEquivalences.satisfactionRate_eq_of_rename_perm
        (TableKeysGame.outputInstance S k g)
        (TableKeysGame.outputInstanceWithEnumeration S k g en)
        (TableKeysGame.semanticToExplicitVertices S k s d)
        (TableKeysGame.explicitConstraints_perm_renamed S k g en) _
    _ = _ := (TableKeysGame.acceptanceProbability_eq_count S k g _).symm

end

end MaxCutGames.Decoder.MatrixGap

/-!
Completeness on the actual single-orbit address output. An honest semantic
labeling is extended over unused addresses, with its satisfied fraction
unchanged. The two rational error bounds need no packaged error parameter.
-/

namespace MaxCutGames.Decoder.MatrixGap

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Foundations.Target
open MaxCutGames.Integration
open ActualSource

noncomputable section

/-- Every semantic labeling extends to a labeling of the padded address space.
The generated edge list retains its exact acceptance fraction. -/
theorem semantic_acceptance_le_address_value (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) :
    (TableKeysGame.acceptanceProbability S k g labeling : ℝ) ≤
      InstanceValue.value (TableKeysAddressGame.outputInstance S k g en) := by
  let e := TableKeysGame.semanticToExplicitVertices S k s d
  let addressLabel := VertexEmbedding.extendLabeling
    (TableKeysAddressGame.explicitToAddress S k s d) (labeling ∘ e.symm)
      (⟨0, by positivity⟩ : Fin (2 ^ s))
  have hrestrict : addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d =
      labeling ∘ e.symm :=
    VertexEmbedding.extendLabeling_comp _
      (TableKeysAddressGame.explicitToAddress_injective S k s d) _ _
  have hpullback : (addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
      TableKeysGame.semanticToExplicitVertices S k s d = labeling := by
    rw [hrestrict]
    funext v
    exact congrArg labeling (e.symm_apply_apply v)
  have hrate := address_rate_eq_semantic_acceptance S k g en addressLabel
  rw [hpullback] at hrate
  have hvalue := InstanceValue.satisfactionRate_le_value
    (TableKeysAddressGame.outputInstance S k g en) addressLabel
  rw [hrate] at hvalue
  exact hvalue

/-- The exact near-assignment loss and fair-bit factor one half, measured on
the generated address instance and then cast to its real optimum value. -/
theorem address_value_ge_of_near_assignment (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (assignment : Fin S.«variables» → Bool) (ξ p : ℚ)
    (hfailure : S.failure assignment ≤ ξ)
    (hstable : (T.gadget f hf).stabilityError ≤ p) :
    (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S k T) := by
  let g := T.gadget f hf
  have hrat := TableKeysCompleteness.honest_acceptance_of_bounds S k g assignment
    ξ p ((k : ℚ) * ξ + p / 2) hfailure hstable (le_refl _)
  have hreal : (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      (TableKeysGame.acceptanceProbability S k g
        (TableKeysCompleteness.honestLabeling S k g assignment) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 hrat
    simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_add, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] using h
  rw [TableKeysAddressGame.tableOutput_eq_with_witness S k T f hf]
  exact hreal.trans (semantic_acceptance_le_address_value S k g
    (TableReduction.tableEnumeration T f hf)
    (TableKeysCompleteness.honestLabeling S k g assignment))

end
end MaxCutGames.Decoder.MatrixGap

namespace MaxCutGames.Decoder.MatrixGap

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Games
open MaxCutGames.Integration
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Fixed matrix-test parameters, before the separate bipartite subdivision
and repetition. Existence is proved by the v2 spectral/decoding argument. -/
structure Parameters (p : ℚ) where
  k : Nat
  s : Nat
  d : Nat
  k_pos : 1 ≤ k
  s_pos : 1 ≤ s
  T : NoiseTables.Table s d
  f : Ambient s d → Alphabet s
  equivariant : ∀ x c, f (x + (c, 0)) = f x + c
  stability : (T.gadget f equivariant).stabilityError ≤ p
  sound : ∀ S : Source, S.DistinctNames →
    Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5 →
    InstanceValue.value (TableKeysAddressGame.tableOutput S k T) ≤ (99 : ℝ) / 100

namespace Parameters

variable {p : ℚ}

/-- The actual output constructor depends only on finite tables, not on the
correcting map or its equivariance proof. -/
def output (P : Parameters p) (S : Source) : Instance (2 ^ P.s) :=
  TableKeysAddressGame.tableOutput S P.k P.T

theorem completeness (P : Parameters p) (S : Source)
    (assignment : Fin S.«variables» → Bool) (ξ : ℚ)
    (hfailure : S.failure assignment ≤ ξ) :
    (1 : ℝ) - ((P.k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S P.k P.T) :=
  address_value_ge_of_near_assignment S P.k P.T P.f P.equivariant assignment
    ξ p hfailure P.stability

theorem output_translations (P : Parameters p) (S : Source) :
    TranslationTarget.IsTranslationInstance (Encoding.alphabetEquiv P.s).symm
      (P.output S) :=
  TableKeysAddressGame.tableOutput_translations S P.k P.T

end Parameters

end

end MaxCutGames.Decoder.MatrixGap

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CloneMachineModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine word emission in the actual clone-table machine

The shared machine keeps its context fixed while copying one saved word. Its
finite transducer therefore acts by a fixed symbol substitution. The lemmas
below identify that substitution with the established unary encoding of
`offset + scale * value`, including all header and equation-field contexts.
Scale, offset, and the triple-table length remain symbolic.
-/

namespace MaxCutGames.Reduction.CloneMachineAffine

open MaxCutGames.Foundations.Complexity
open CloneMachineModel

theorem affineEmit_replicate_true (scale offset v : Nat) :
    (List.replicate v true).flatMap (affineEmit scale offset) =
      List.replicate (scale * v) true := by
  rw [List.flatMap_replicate]
  change (List.replicate v (List.replicate scale true)).flatten = _
  rw [List.flatten_replicate_replicate, Nat.mul_comm v scale]

end MaxCutGames.Reduction.CloneMachineAffine

namespace MaxCutGames.Reduction.MachineAddressHeaders

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineComposition

noncomputable section

namespace Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type}

variable [DecidableEq K]

structure WorkClean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop where
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients k s d noiseCount, base (slots (.inr i)) = []

structure Clean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop
    extends WorkClean slots base where
  baseValue : base (control slots .baseValue) = []
  capacity : base (control slots .capacity) = []
  temporary : base (control slots .temporary) = []

def steps (k s d noiseCount n m : Nat) : Nat :=
  2 * n + 3 * m + 10 +
    SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .capacity) (radix s d n m) +
    SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .edges) m +
    3 * capacity k s d n m + edgeCount k s d noiseCount m + 8

/-- A fixed polynomial in the serialized input length bounds actual steps. -/
def timePolynomial (k s d noiseCount : Nat) : Polynomial Nat :=
  let B : Polynomial Nat := Polynomial.C 2 * Polynomial.X + Polynomial.C (baseConstant s d)
  (CookLevin.PolynomialMachine.timePolynomial (polynomial k s d noiseCount .capacity)).comp B +
    CookLevin.PolynomialMachine.timePolynomial (polynomial k s d noiseCount .edges) +
    Polynomial.C 3 * (polynomial k s d noiseCount .capacity).comp B +
    polynomial k s d noiseCount .edges + Polynomial.C 5 * Polynomial.X + Polynomial.C 18

theorem steps_le_timePolynomial (k s d noiseCount n m L : Nat) (hn : n ≤ L) (hm : m ≤ L) :
    steps k s d noiseCount n m ≤ (timePolynomial k s d noiseCount).eval L := by
  have hB : radix s d n m ≤ 2 * L + baseConstant s d := by unfold radix; omega
  have hEval (p : Polynomial Nat) (a b : Nat) (hab : a ≤ b) :
      SourceHeaderCounts.Eval.steps p a ≤ (CookLevin.PolynomialMachine.timePolynomial p).eval b := by
    apply Nat.le_trans (m := (CookLevin.PolynomialMachine.timePolynomial p).eval a)
    · rw [CookLevin.PolynomialMachine.timePolynomial_eval]
      unfold SourceHeaderCounts.Eval.steps
      omega
    · exact natPolynomial_eval_mono _ hab
  have h1 := hEval (polynomial k s d noiseCount .capacity) _ _ hB
  have h2 := hEval (polynomial k s d noiseCount .edges) _ _ hm
  have hc : capacity k s d n m ≤ (2 * L + baseConstant s d) ^ (1 + 9 * k) :=
    Nat.pow_le_pow_left hB _
  have he : edgeCount k s d noiseCount m ≤ edgeCount k s d noiseCount L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_comp, polynomial_capacity_eval, polynomial_edges_eval]
  unfold steps
  omega

end Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type} [DecidableEq K]

structure Clean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop
    extends Arithmetic.Clean (arithmeticSlots slots) base where
  readCopy : base (slots (.inl 1)) = []
  variableCount : base (Arithmetic.control (arithmeticSlots slots) .variableCount) = []
  occurrenceCount : base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) = []

end

end MaxCutGames.Reduction.MachineAddressHeaders

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressGame
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Executable direct addresses for the actual canonical game. Every original
edge occurrence and its translation table is retained, in the same order.
Addresses not representing realized bodies are isolated vertices. No vertex
list, duplicate removal, or inverse enumeration is evaluated by the output. -/

namespace MaxCutGames.Reduction.AddressGame

open ActualSource
open Foundations.Target
open Integration.VertexEmbedding

/-- The concrete vector-table interface contains no correcting-map witness. -/
def tableOutput (S : Source) (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    Instance (2^s) :=
  outputInstance S k (Integration.TableReduction.tableSkeleton T)
    (Integration.TableReduction.tableEnumeration T Prod.fst (fun _ _ => rfl))

end MaxCutGames.Reduction.AddressGame

namespace MaxCutGames.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration _root_.OAI.MaxCutGames.Reduction.Explicit

variable {N α β γ R : Type*}

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

end MaxCutGames.Reduction.FixedOutcomes

namespace MaxCutGames.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

variable {s d : Nat} {α : Type*}

/-- Complete output-byte factorization used by the actual outer loop. -/
theorem gameBits_factor (S : Source) (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    gameBits (AddressGame.tableOutput S k T) =
      encodeWords [(AddressGame.tableOutput S k T).vertices, 2^s,
        (AddressGame.tableOutput S k T).constraints.length] ++
      (FixedOutcomes.occurrenceTuples S.occurrences k).flatMap (tupleBits S k T) := by
  rw [gameBits, gameWords, encodeWords_append, encodeWords_flatMap_inline_AddressOutcomeSpecs]
  rw [FixedOutcomes.tableOutput_constraints]
  erw [List.flatMap_assoc]
  congr 1
  apply List.flatMap_congr
  intro U _
  erw [List.flatMap_map]
  rfl

end MaxCutGames.Reduction.AddressOutcomeSpecs

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OccurrenceTupleOrder
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate-order bridge from the checked tuple odometer to the
outer reduction's occurrence enumeration. The odometer changes coordinate zero
fastest; `ActualEnumeration.functions` changes it slowest. Reading saved digit
`j.rev` as query coordinate `j` matches the complete ordered list. No primitive
machine or assumed whole-loop runtime is introduced here. -/

namespace MaxCutGames.Integration.AddressTupleBudget

open Reduction Foundations.Complexity
open AddressTupleBody

variable {k s d noiseCount : Nat}

/-- Both canonical templates have exactly the same fixed token count. -/
noncomputable def rowPolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  Polynomial.C (2^((2*k+1)*(s+d+1))*T.vectors.length) *
    MachineAddressEdge.timePolynomial (1+9*k) (1+9*k) (1+9*k) + 1

/-- Fixed program dimensions determine this explicit polynomial in input bits. -/
noncomputable def timePolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  (Polynomial.C k*(Polynomial.C 10*Polynomial.X+Polynomial.C 20)+1)+1+
    (rowPolynomial k T).comp (magnitudePolynomial k s d)+
    Polynomial.C (4*k)*(Polynomial.X+Polynomial.C 2)+1

end MaxCutGames.Integration.AddressTupleBudget

/-!
# Polynomial encoded length of the actual output

The encoder uses a unary, delimited forward-permutation
format. The instance is the actual list-based reduction, including canonical
body deduplication and every repeated edge occurrence. The polynomial's
coefficients depend only on the fixed gadget table and tuple dimensions.

These are output-length theorems. They do not assert a machine running-time
certificate for canonicalization, enumeration, or serialization.
-/

namespace MaxCutGames.Reduction.AddressOutputSize

open ActualSource
open MaxCutGames.Integration
open MaxCutGames.Foundations

variable {s d : Nat}

theorem table_constraints_eq (S : Source) (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput S k T).constraints.length =
      Explicit.edgeCount S.occurrences k (s + d) T.vectors.length := by
  unfold AddressGame.tableOutput
  erw [AddressGame.outputInstance_length]
  simp only [TableReduction.tableEnumeration]
  erw [List.length_finRange]

end MaxCutGames.Reduction.AddressOutputSize

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineProgram
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration
open MachineComposition

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

theorem accumulator_ne_output : accumulator k T ≠ output k T :=
  AddressMachineSpace.headerTape_ne_finalOutput k s d T.vectors.length .reversed

theorem clearKeys_covers (tape : Tape k T) (ha : tape ≠ accumulator k T)
    (ho : tape ≠ output k T) : tape ∈ clearKeys k T := (mem_clearKeys k T tape).2 ⟨ha,ho⟩

/-- This bridge has no data-dependent action and costs exactly one transition. -/
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

theorem haltList_eq (bits : List Bool) : haltList (machine k T) bits =
    ⟨none,AddressMachineSpace.initialState k,outputTapes k T bits⟩ := by
  change (⟨none,AddressMachineSpace.initialState k,
    (haltList (machine k T) bits).stk⟩ : (machine k T).Cfg) = _
  apply congrArg (fun tapes =>
    (⟨none,AddressMachineSpace.initialState k,tapes⟩ : (machine k T).Cfg))
  funext tape
  by_cases h : tape = output k T
  · subst tape; simp [haltList,machine,outputTapes,SourceRuntimeFinish.canonicalTapes]; rfl
  · simp [haltList,machine,outputTapes,SourceRuntimeFinish.canonicalTapes]
    erw [dite_eq_right h, Function.update_of_ne h]

end
end MaxCutGames.Reduction.AddressMachineProgram

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineInitial

open Turing MaxCutGames.Foundations.Complexity

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

end
end MaxCutGames.Reduction.AddressMachineInitial

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSingleOrbitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Physical postprocessing of the two-side address codec. The program reads
`2*C,q,m`, writes `C,q,m`, and replaces each row `u,C+v,table` by `u,v,table`.
Only the fixed alphabet size `q` occurs in finite control. All input-dependent
integers reside on unary tapes. Six Bool tapes suffice.
-/

/-! Exact streaming traces in the single-orbit postprocessor. -/

/-! Physical unary header conversion, with an exact TM2 transition count. -/

/-! Actual subtraction of the right-side address offset, preserving the unary
capacity tape for every later edge. -/

/-! The exact input/output codec of the one-orbit postprocessor. Doubling is
only an encoding adapter: no equality of game values under independent labels
on the two copies is asserted. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitCodec

open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Complexity

def doubleInstance {q : Nat} (I : Instance q) : Instance q where
  vertices := 2 * I.vertices
  constraints := I.constraints.map doubleConstraint
  nonempty h := I.nonempty (List.map_eq_nil_iff.mp h)

def doubledRowsBits {n q : Nat} (cs : List (Constraint n q)) : List Bool :=
  encodeWords (cs.flatMap (fun c => constraintWords (doubleConstraint c)))

@[simp] theorem rowsBits_nil {n q : Nat} : rowsBits ([] : List (Constraint n q)) = [] := rfl
@[simp] theorem doubledRowsBits_nil {n q : Nat} :
    doubledRowsBits ([] : List (Constraint n q)) = [] := rfl

@[simp] theorem rowsBits_cons {n q : Nat} (c : Constraint n q) (cs : List (Constraint n q)) :
    rowsBits (c :: cs) = rowBits c ++ rowsBits cs := by
  simp [rowsBits, rowBits]

@[simp] theorem doubledRowsBits_cons {n q : Nat} (c : Constraint n q)
    (cs : List (Constraint n q)) :
    doubledRowsBits (c :: cs) = doubledRowBits c ++ doubledRowsBits cs := by
  simp [doubledRowsBits, doubledRowBits]

end MaxCutGames.Explicit.MachineSingleOrbitCodec

/-! Complete ordered row traversal of the physical one-orbit postprocessor. -/

/-! Actual tape cleanup, accumulator reversal, and halt for the one-orbit
postprocessor. The time bound is derived from an actual executed prefix. -/

/-!
Complete finite-machine postprocessing of the doubled address representation.
Every input field and row is physically processed. The time polynomial is in
the literal input bit length, including the final reversal and all tape cleanup.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AddressMachineLoop
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressMachineLoop

open Turing Foundations.Complexity Integration

noncomputable section

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

/-- The actual header machine emits exactly the target instance's three headers. -/
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

/-- The final reversed tape is exactly the complete encoded actual instance. -/
theorem final_accumulator (F : SourceEncoding.Input) :
    finalTapes k T F (AddressMachineProgram.accumulator k T) =
      (gameBits (AddressGame.tableOutput (AddressTupleBody.source F) k T)).reverse := by
  rw [AddressOutcomeSpecs.gameBits_factor, ← headerBits_eq k T F, List.reverse_append]
  exact final_reversed k T F

/-- The exponent and coefficients depend only on fixed reduction parameters. -/
def timePolynomial : Polynomial Nat :=
  (AddressTupleBudget.timePolynomial k T + Polynomial.C (2*k)) * Polynomial.X^k

@[simp] theorem timePolynomial_eval (N : Nat) :
    (timePolynomial k T).eval N = ((AddressTupleBudget.timePolynomial k T).eval N + 2*k)*N^k := by
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

end
end MaxCutGames.Reduction.AddressMachineLoop

/-!
The actual address machine's final bridge, cleanup, reversal, and halt. The
polynomial cleanup bound follows from space used by the supplied actual prefix
execution. The complete reduction supplies that prefix in `MachineAddressGame`.
-/

namespace MaxCutGames.Reduction.AddressMachineFinish

open Turing Foundations.Complexity Foundations.Hastad

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def timePolynomial (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (AddressMachineProgram.machine k T)
    (AddressMachineProgram.clearKeys k T).length (prefixTime + 1)

/-- Finish the concrete program, including its one-step finalizer entry bridge.
The runtime bound uses all actual intermediate tapes, with no output-size or
private-space assumption. -/
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
end MaxCutGames.Reduction.AddressMachineFinish

/-!
# The complete addressed outer-reduction machine

The fixed finite machine reads an encoded nonempty E3LIN occurrence list and
writes the exact encoded addressed Unique Games instance. Its execution covers
all headers, all occurrence tuples, every fixed noise/coefficient outcome,
every permutation image, reversal, and complete tape cleanup.
-/

namespace MaxCutGames.Reduction.MachineAddressGame

open Turing Foundations.Complexity

noncomputable section

variable (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d)

def output (input : SourceEncoding.Input) : Foundations.Target.Instance (2 ^ s) :=
  AddressGame.tableOutput
    (ActualSource.Source.ofList input.equations input.nonempty) k T

end
end MaxCutGames.Reduction.MachineAddressGame

/-!
The old addressed producer is reused only as a code generator. Its exact output
is the doubled codec of the new single-orbit game. The proved physical
postprocessor then yields the new game, with no premise about the value of the
legacy game and no legacy gadget or inverse theorem used.
-/

namespace MaxCutGames.Explicit.MachineSingleOrbitBridge

open Turing MaxCutGames.Reduction MaxCutGames.Foundations.Complexity
open ActualSource MachineSingleOrbitCodec

namespace SingleAddress

abbrev addressEdge := Decoder.TableKeysAddressGame.addressEdge
abbrev outputInstance := Decoder.TableKeysAddressGame.outputInstance
abbrev tableOutput := Decoder.TableKeysAddressGame.tableOutput

end SingleAddress

theorem old_addressEdge_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    AddressGame.addressEdge S k g ω = doubleConstraint (SingleAddress.addressEdge S k g ω) := by
  unfold AddressGame.addressEdge doubleConstraint SingleAddress.addressEdge
    Decoder.TableKeysAddressGame.addressEdge
  congr 1
  apply Fin.ext
  exact Encoding.sideEquiv_true_val _

/-- Exact equality of the ordered, fully serialized constraint data. -/
theorem old_outputInstance_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    AddressGame.outputInstance S k g en = doubleInstance (SingleAddress.outputInstance S k g en) := by
  unfold AddressGame.outputInstance doubleInstance SingleAddress.outputInstance
    Decoder.TableKeysAddressGame.outputInstance
  congr 1
  simp only [List.map_map, Function.comp_def, ← old_addressEdge_eq_double]
  rfl

theorem old_tableOutput_eq_double (S : Source) (k : Nat) {s d : Nat}
    (T : MaxCutGames.Integration.NoiseTables.Table s d) :
    AddressGame.tableOutput S k T = doubleInstance (SingleAddress.tableOutput S k T) :=
  old_outputInstance_eq_double S k _ _

def output (k : Nat) {s d : Nat} (T : MaxCutGames.Integration.NoiseTables.Table s d)
    (input : SourceEncoding.Input) : MaxCutGames.Foundations.Target.Instance (2 ^ s) :=
  SingleAddress.tableOutput (Source.ofList input.equations input.nonempty) k T

theorem old_output_eq_double (k : Nat) {s d : Nat}
    (T : MaxCutGames.Integration.NoiseTables.Table s d) (input : SourceEncoding.Input) :
    MachineAddressGame.output k T input = doubleInstance (output k T input) :=
  old_tableOutput_eq_double _ k T

end MaxCutGames.Explicit.MachineSingleOrbitBridge

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_PositiveMultiplier
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Fourier
open MatrixCharacters MatrixFourier MatrixNoise

namespace MaxCutGames.Decoder.PositiveMultiplier

section ActualMatrixTest

variable {Q C E V : Type*} [Fintype Q] [Fintype C]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
  [Fintype V] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)]

/-- The actual equality test, including zero perturbation factors. -/
def equalityAcceptance (ν : V → ℝ) (label : (E →ₗ[F2] V) → C) : ℝ := by
  classical
  exact 𝔼 X, ∑ v, ν v * (𝔼 l : E →ₗ[F2] F2,
    if label X = label (X + l.smulRight v) then (1 : ℝ) else 0)

end ActualMatrixTest

section UniformSubspace

variable {K V E : Type*}
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 K] [Fintype K]
  [AddCommGroup V] [Module F2 V] [Fintype V]
  [AddCommGroup E] [Module F2 E]

/-- Pushforward of uniform sampling in `K`.  For a subspace inclusion this
is uniform sampling in that subspace; the definition also permits a linear
map with nontrivial fibers without accidentally conditioning on nonzero vectors. -/
def subspaceLaw (ι : K →ₗ[F2] V) (v : V) : ℝ := by
  classical
  exact ∑ k, if ι k = v then (Fintype.card K : ℝ)⁻¹ else 0

end UniformSubspace

end MaxCutGames.Decoder.PositiveMultiplier
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_MatrixCoordinates
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end
end MaxCutGames.Decoder.MatrixCoordinates

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_ActualGoodRows
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Decoder.MatrixGapChoice

open Integration.BinaryLinear Reduction ActualSource
open Inverse.Shortcode (Mat HasAffineSlice equalityAcceptance)

noncomputable section

/-- Fixed dimensions, density and sparse mask for one logical alphabet.
The remaining gadget codimension may be arbitrary when choosing the cube. -/
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
end MaxCutGames.Decoder.MatrixGapChoice

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_SelectedPolicies
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual visible selector used by the stochastic decoder

At fixed labeling, the matrix table depends only on the occurrence question and
complement map. Its normalized row/column witness is selected from the observed
row map and row value. Transporting this witness through the actual homogeneous
coordinates supplies `VisiblePolicies.ResponseWitness`; the selected target's
affine intercept is retained separately, including exact equality on the slice.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedPolicies

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction
open MaxCutGames.Inverse
open ActualSource VisiblePolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

variable {k s d r : ℕ}

/-- The generic selector predicate is now the graph of the actual normalized
row-advice selector, rather than an unspecified class of candidate witnesses. -/
def goodPredicate (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α : ℝ) (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (q : LeftInput S k s d (Vector r)) (w : ResponseWitness k) : Prop :=
  ∃ hgood : GoodAdvice S labeling α q,
    w = normalizedResponse S labeling α hα hsmall q hgood

end MaxCutGames.Decoder.SelectedPolicies
end

/-! The selected full-table events pulled back to the genuine projected
experiment. The comparison space forgets the projection, while complete data
retains it only for the subsequent finite conditional-law argument. -/

/-! Whole-table variation for the exact projected seed law in the selected
event coordinates. The projection is averaged out before the comparison. -/

/-!
# Conditional success of the actual selected policies

This endpoint uses the normalized witness chosen from the left observation and
the private Fourier kernel chosen from the right observation. The hypothesis is
literal uniform agreement on a transferred affine column slice. Deriving that
hypothesis from the actual visible conditional law is the separate transfer
step; it is not assumed as an inverse theorem or as extra prover information.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedDecoding

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Inverse
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

/-- The affine slice is a subtype of a finite linear-map space. -/
instance affineSliceFintype {E K L : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup K] [Module F2 K]
    [AddCommGroup L] [Module F2 L] [Fintype (E →ₗ[F2] K)]
    (A : K →ₗ[F2] L) (Q : Submodule F2 E) (Mstar : E →ₗ[F2] K) :
    Fintype (RowErasureSliceQuotient.AffineSlice A Q Mstar) := by
  unfold RowErasureSliceQuotient.AffineSlice
  infer_instance

variable {k s d r : ℕ}

/-- Literal uniform target agreement on the projected affine slice. The slice
origin is an analysis witness, independent of the canonical visible row base. -/
def transferredAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r))
    (w : ResponseWitness k) (u : Alphabet s)
    (Mstar : RawPartnerTarget.RawPoint draw.singletons →ₗ[F2] Alphabet s) : ℝ :=
  𝔼 M : RowErasureSliceQuotient.AffineSlice draw.rowMap
      (w.columns.map (AdviceExperiment.projection (ActualGame.rhs S) draw)) Mstar,
    if TableKeysRestoration.projectedAnswer S k s d labeling draw.singletons
        (RawPrivateTable.supported draw.singletons (ActualGame.names S)
          draw.occurrences draw.positions) (M.val.prod draw.complement) =
      M.val (AdviceExperiment.projection (ActualGame.rhs S) draw w.coefficient) + u
    then (1 : ℝ) else 0

end MaxCutGames.Decoder.SelectedDecoding
end

/-!
# The selected padded slice is the actual projected affine slice

After fixing row advice, the selected full-domain column equations on `Mπ` are
exactly the equations fixing `M` on the image of the selected column span under
`π`. The equivalence keeps the same maps, so both uniform sampling and affine
target equality transport without changing the chosen intercept.
-/

/-! A finite experiment whose sample weights are constant on the selected
event becomes exactly uniform after conditioning on that event. The event is
allowed to have arbitrary positive mass, so this applies after the complete
visible datum and the chosen column constraints have both been fixed. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_VisibleTransfer
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete-data conditional law of the actual projected experiment.
The residual private matrix is uniform even when the occurrence law is
weighted and the public row map has deficient rank. -/

/-!
# Actual conditional selected-fiber agreement

The selected event is the full-table event used by the total-variation
comparison. On a positive complete-data fiber it becomes the uniform actual
affine row/column slice. The selector is fixed by the left observation; the
extra complete data and a supporting matrix occur only in this analysis.
-/

noncomputable section

namespace MaxCutGames.Decoder.SelectedFiberLaw

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction MaxCutGames.Soundness
open MaxCutGames.Inverse MaxCutGames.Foundations.Games
open ActualSource VisiblePolicies SelectedPolicies MatrixCoordinates ActualSeedEvents
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

end MaxCutGames.Decoder.SelectedFiberLaw
end

/-! The full selected-witness argument on the actual projected experiment.
The variation comparison precedes all conditioning. Its visible event then
pays the independent private decoder success on every selected datum. -/

end OAI
end


