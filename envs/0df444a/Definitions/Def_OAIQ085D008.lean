-- Prove2me | Definitions.Def_OAIQ085D008
-- name    : OAIQ085D008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:57:18.300175+00:00
-- url     : https://prove2.me/theorems/63dc8e04-fdc7-45f8-86ea-0b6854dc9d5c
-- title:
--   Definitions bundle OAIQ085D008 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 547 declarations of OpenAI's Lean: 216 definitions, 10 inductive types or structures, 2 instances and 319 theorems. The definitions and types are `OAI.DFVSGames.Decoder.PaddedLaw.RawTuple`, `OAI.DFVSGames.Decoder.PaddedLaw.blockKernel`, `OAI.DFVSGames.Decoder.PaddedLaw.kernelTupleWeight`, `OAI.DFVSGames.Decoder.TableKeysGame.Map`, `OAI.DFVSGames.Decoder.TableKeysPrivateRow.targetIntercept`, `OAI.DFVSGames.Decoder.TransferredDecoding.homFintype`, `OAI.DFVSGames.Decoder.TransferredDecoding.privateOrigin`, `OAI.DFVSGames.Explicit.BipartiteGame.Satisfied`, `OAI.DFVSGames.Explicit.BipartiteGame.binaryProductEquiv`, `OAI.DFVSGames.Explicit.BipartiteGame.maxSatisfied`, `OAI.DFVSGames.Explicit.BipartiteGame.occurrenceSuccess`, `OAI.DFVSGames.Explicit.BipartiteGame.satisfiedCount`, `OAI.DFVSGames.Explicit.BipartiteGame.value`, `OAI.DFVSGames.Explicit.MachineClone100.indices`, `OAI.DFVSGames.Explicit.MachineClone100.triples`, `OAI.DFVSGames.Explicit.MachineClone100Model.Alphabet`, `OAI.DFVSGames.Explicit.MachineClone100Model.Label`, `OAI.DFVSGames.Explicit.MachineClone100Model.State`, `OAI.DFVSGames.Explicit.MachineClone100Model.cleanupNext`, `OAI.DFVSGames.Explicit.MachineClone100Model.contextNext`, `OAI.DFVSGames.Explicit.MachineClone100Model.defaultControl`, `OAI.DFVSGames.Explicit.MachineClone100Model.drain`, `OAI.DFVSGames.Explicit.MachineClone100Model.initialState`, `OAI.DFVSGames.Explicit.MachineClone100Triples.startAt`, `OAI.DFVSGames.Explicit.MachineProductBounds.fieldPolynomial`, `OAI.DFVSGames.Explicit.MachineProductField.hornerRole`, `OAI.DFVSGames.Explicit.MachineProductField.hornerSlots`, `OAI.DFVSGames.Explicit.MachineProductGather.steps`, `OAI.DFVSGames.Explicit.MachineProductHeaders.baseTapes`, `OAI.DFVSGames.Explicit.MachineProductHeaders.headerBits`, `OAI.DFVSGames.Explicit.MachineProductHeaders.steps`, `OAI.DFVSGames.Explicit.MachineProductHeaders.timePolynomial`, `OAI.DFVSGames.Explicit.MachineProductHeadersRead.afterAlphabet`, `OAI.DFVSGames.Explicit.MachineProductHeadersRead.afterVertices`, `OAI.DFVSGames.Explicit.MachineProductHeadersRead.inputTapes`, `OAI.DFVSGames.Explicit.MachineProductHeadersRead.rawResultTapes`, `OAI.DFVSGames.Explicit.MachineProductHeadersRead.resultTapes`, `OAI.DFVSGames.Explicit.MachineProductLoop.BaseReady`, `OAI.DFVSGames.Explicit.MachineProductLoop.bodyBound`, `OAI.DFVSGames.Explicit.MachineProductLoop.rowBits` and 186 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Analysis_NoiseEnumeration`, `DirectedFeedback_CookLevin_PolynomialMachine`, `DirectedFeedback_Encoding_FormulaEncoding`, `DirectedFeedback_Encoding_PreprocessingRegularTables`, `DirectedFeedback_Encoding_ProductTarget`, `DirectedFeedback_Encoding_VerifierCNF`, `DirectedFeedback_Games_AddressTupleLoaded`, `DirectedFeedback_Games_CanonicalAddress`, `DirectedFeedback_Games_Collision`, `DirectedFeedback_Games_ExpanderFamily`, `DirectedFeedback_Games_Explicit`, `DirectedFeedback_Games_FieldArray`, `DirectedFeedback_Games_InitialGraph`, `DirectedFeedback_Games_Preprocessing`, `DirectedFeedback_Games_Product`, `DirectedFeedback_Games_RowErasureSliceQuotient`, `DirectedFeedback_Games_SharedSampling`, `DirectedFeedback_Games_Target`, `DirectedFeedback_Games_TensorDomination`, `DirectedFeedback_Games_TestEmit`, `DirectedFeedback_Games_UniformReduction`, `DirectedFeedback_Machines_AddressMachineInitial`, `DirectedFeedback_Machines_FinalCNFHeader`, `DirectedFeedback_Machines_MachineAddressHeaders`, `DirectedFeedback_Machines_MachineAffineLookup`, `DirectedFeedback_Machines_MachineBinaryRenameMachine`, `DirectedFeedback_Machines_MachineCloudCount`, `DirectedFeedback_Machines_MachineCloudPadding`, `DirectedFeedback_Machines_MachineLazyTableRuntime`, `DirectedFeedback_Machines_MachineLookupSpec`, `DirectedFeedback_Machines_MachinePreservingLookupClean`, `DirectedFeedback_Machines_MachineProductField`, `DirectedFeedback_Machines_MachineProductFinish`, `DirectedFeedback_Machines_MachineProductPower`, `DirectedFeedback_Machines_MachineProductProgram`, `DirectedFeedback_Machines_MachineRegularExecutionBounds`, `DirectedFeedback_Machines_MachineSingleOrbitCodec`, `DirectedFeedback_Machines_MachineSubdivisionInit`, `DirectedFeedback_Machines_MachineSubdivisionLoop`, `DirectedFeedback_Machines_MachineSubdivisionRows`, `DirectedFeedback_Machines_MachineTemplateAddress`, `DirectedFeedback_Machines_MachineTransducer`, `DirectedFeedback_Machines_MachineTuple`, `DirectedFeedback_Machines_MachineUnaryAdd`, `DirectedFeedback_Machines_RawInitialMachineFinish`, `DirectedFeedback_Machines_RuntimeFinish`, `DirectedFeedback_Machines_RuntimeSpace`, `DirectedFeedback_Machines_Tape`, `DirectedFeedback_Machines_TupleOrder`, `DirectedFeedback_Probability_Basic`, `DirectedFeedback_Probability_TraceLaw`, `DirectedFeedback_RankGraph_Clone100Counting`, `DirectedFeedback_RankGraph_MachineClone100Cleanup`, `DirectedFeedback_RankGraph_MachineClone100Finish`, `DirectedFeedback_RankGraph_SumBox`.
--
--   **Imports.** It imports the bundles `OAIQ085D000`, `OAIQ085D001` and `OAIQ085D002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D013`, `OAIQ085D014`, `OAIQ085D015` and `OAIQ085D016`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ085D000
import Definitions.Def_OAIQ085D001
import Definitions.Def_OAIQ085D002

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Target
attribute [-instance] _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity

theorem encodeWords_length_le (ns : List Nat) (bound : Nat)
    (bounded : ∀ n ∈ ns, n ≤ bound) :
    (encodeWords ns).length ≤ ns.length * (bound + 1) := by
  induction ns with
  | nil => simp [encodeWords]
  | cons n ns ih =>
      have hn := bounded n (by simp)
      have hns := ih (fun x hx => bounded x (by simp [hx]))
      simp only [encodeWords, List.length_append, encodeWord_length, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

open Target

end DFVSGames.Foundations.Complexity


namespace DFVSGames.Foundations.Hastad.SourceMachine

open Turing
open DFVSGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

theorem fieldTapes_other (source destination p : K)
    (hpS : p ≠ source) (hpD : p ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output p = base p := by
  simp [fieldTapes, hpS, hpD]

theorem update_field_source_inline_SourceMachine (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) source replacement =
      fieldTapes source destination base replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [fieldTapes, hne]
  · by_cases hd : p = destination
    · subst p; simp [fieldTapes, Ne.symm hne]
    · simp [fieldTapes, hs, hd]

theorem update_field_destination_inline_SourceMachine (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) destination replacement =
      fieldTapes source destination base input replacement := by
  simp [fieldTapes]

theorem fieldStartStep (source destination : K)
    (startLabel loopLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = fieldStart destination loopLabel)
    (base : K → List Bool) (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some startLabel, (ambient, register), fieldTapes source destination base input output⟩ =
      some ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base input (false :: output)⟩ := by
  change some (TM2.stepAux (program startLabel) (ambient, register)
    (fieldTapes source destination base input output)) = _
  rw [atStart]
  simp [fieldStart, TM2.stepAux, update_field_destination_inline_SourceMachine]

def afterField (source destination : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) : K → List Bool :=
  fieldTapes source destination base suffix (encodeWord n ++ base destination)

def fourTapes (source : K) (destination : Fin 4 → K) (base : K → List Bool)
    (a b c d : Nat) (suffix : List Bool) : K → List Bool :=
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  afterField source (destination 3) t₂ d suffix

end DFVSGames.Foundations.Hastad.SourceMachine


namespace DFVSGames.Foundations.Complexity.MachineFiniteSequence

open Turing MachineComposition

variable {Command : Type} (LocalLabel : Command → Type)

variable (main : ∀ command, LocalLabel command)
variable {K Λ σ : Type} {Γ : K → Type}

variable (localInstruction : ∀ command, (LocalLabel command → Λ) → Option Λ →
  LocalLabel command → TM2.Stmt Γ Λ σ)

variable {Data : Type} (result : Command → Data → Data) (cost : Command → Data → Nat)

variable [DecidableEq K]

theorem trace (program : Λ → TM2.Stmt Γ Λ σ)
    (invariant : Data → Prop) (state : Data → σ) (tapes : Data → ∀ k, List (Γ k))
    (commands : List Command)
    (localInvariant : ∀ command ∈ commands, ∀ data, invariant data →
      invariant (result command data))
    (localTrace : ∀ command ∈ commands, ∀ (labels : LocalLabel command → Λ) (exit : Option Λ),
      (∀ l, program (labels l) = localInstruction command labels exit l) →
      ∀ data, invariant data →
      (advance (TM2.step program))^[cost command data]
        (some ⟨some (labels (main command)), state data, tapes data⟩) =
      some ⟨exit, state (result command data), tapes (result command data)⟩)
    (labels : Label LocalLabel commands → Λ) (exit : Option Λ)
    (atLabels : ∀ l, program (labels l) =
      instruction LocalLabel main localInstruction commands labels exit l)
    (data : Data) (valid : invariant data) :
    (advance (TM2.step program))^[steps result cost commands data]
      (some ⟨entry LocalLabel main commands labels exit, state data, tapes data⟩) =
    some ⟨exit, state (resultOf result commands data), tapes (resultOf result commands data)⟩ := by
  induction commands generalizing data with
  | nil => rfl
  | cons command commands ih =>
      have firstRun := localTrace command (by simp)
        (fun l => labels (.inl l))
        (entry LocalLabel main commands (fun l => labels (.inr l)) exit)
        (fun l => atLabels (.inl l)) data valid
      have nextValid := localInvariant command (by simp) data valid
      have tailRun := ih
        (fun c hc d hd => localInvariant c (by simp [hc]) d hd)
        (fun c hc => localTrace c (by simp [hc]))
        (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
        (result command data) nextValid
      rw [steps, Nat.add_comm, Function.iterate_add_apply]
      change (advance (TM2.step program))^[steps result cost commands (result command data)]
        ((advance (TM2.step program))^[cost command data]
          (some ⟨some (labels (.inl (main command))), state data, tapes data⟩)) = _
      rw [firstRun]
      exact tailRun

end DFVSGames.Foundations.Complexity.MachineFiniteSequence


namespace DFVSGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def lengthSum (chosen : List K) (base : Tapes K) : Nat :=
  (chosen.map (fun k => (base k).length)).sum

omit [DecidableEq K] in
theorem lengthSum_mono (chosen : List K) (first second : Tapes K)
    (h : ∀ k, (first k).length ≤ (second k).length) :
    lengthSum chosen first ≤ lengthSum chosen second := by
  induction chosen with
  | nil => exact Nat.le_refl 0
  | cons source chosen ih =>
      simp only [lengthSum, List.map_cons, List.sum_cons] at ih ⊢
      exact Nat.add_le_add (h source) ih

theorem steps_le (chosen : List K) (base : Tapes K) :
    steps chosen base ≤ lengthSum chosen base + chosen.length := by
  induction chosen generalizing base with
  | nil => simp [steps, lengthSum]
  | cons source chosen ih =>
      have hshort : ∀ k, ((Function.update base source []) k).length ≤ (base k).length := by
        intro k
        by_cases h : k = source
        · subst k
          simp
        · simp [Function.update_of_ne h]
      have hsum := lengthSum_mono chosen (Function.update base source []) base hshort
      have htail := ih (Function.update base source [])
      simp only [steps, lengthSum, List.map_cons, List.sum_cons, List.length_cons] at hsum htail ⊢
      omega

theorem steps_le_uniform (chosen : List K) (base : Tapes K) (bound : Nat)
    (h : ∀ k, (base k).length ≤ bound) :
    steps chosen base ≤ chosen.length * (bound + 1) := by
  have hsum : lengthSum chosen base ≤ chosen.length * bound := by
    induction chosen with
    | nil => simp [lengthSum]
    | cons source chosen ih =>
        simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
          Nat.one_mul] at ih ⊢
        have hs := h source
        omega
  have hc := steps_le chosen base
  rw [Nat.mul_add, Nat.mul_one]
  omega

def haltTapes (output : K) (word : List Bool) : Tapes K :=
  fun k => if k = output then word else []

end DFVSGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_SumBox
attribute [-instance] _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition

theorem dsRate_nonneg {gap : ℝ} (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1) :
    0 ≤ dsRate gap := by
  dsimp [dsRate]
  nlinarith

end DFVSGames.Repetition


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.MachineFieldTemplate

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem outputTapes_append (base : K → List Bool) (output : K) (first second : List Bool) :
    outputTapes (outputTapes base output first) output second =
      outputTapes base output (first ++ second) := by
  simp [outputTapes, List.reverse_append, List.append_assoc]

theorem fieldValues_outputTapes (field : Fin q → K) (output : K)
    (fieldOutput : ∀ j, field j ≠ output) (base : K → List Bool) (bits : List Bool) :
    (fun j => outputTapes base output bits (field j)) = (fun j => base (field j)) := by
  funext j
  exact outputTapes_other base output bits _ (fieldOutput j)

theorem identity_output (bits : List Bool) :
    MachineTransducer.output (fun (_ : Unit) _ => ()) identityEmit () bits = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [MachineTransducer.output, identityEmit, ih]

end DFVSGames.Reduction.MachineFieldTemplate

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

def finishCost (clearKeys : List K) (accumulator : K) (base : Tapes K) : Nat :=
  MachineDrainMany.steps clearKeys base + (base accumulator).length + 2

theorem cleared_frame (clearKeys : List K) (base : Tapes K) (tape : K)
    (h : tape ∉ clearKeys) : MachineDrainMany.finalTapes clearKeys base tape = base tape :=
  MachineDrainMany.finalTapes_not_mem clearKeys base tape h

theorem reversed_tapes (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) :
    Reduction.MachineTransfer.tapesAt accumulator output
      (MachineDrainMany.finalTapes clearKeys base) [] (base accumulator).reverse =
      canonicalTapes output (base accumulator).reverse := by
  funext k
  by_cases hout : k = output
  · subst k
    simp [Reduction.MachineTransfer.tapesAt, canonicalTapes]
  · by_cases hacc : k = accumulator
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, distinct]
    · have hclear := MachineDrainMany.finalTapes_mem clearKeys base k (covers k hacc hout)
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, hout, hacc, hclear]


variable [Fintype K]
open scoped BigOperators

def totalLength (base : Tapes K) : Nat := ∑ k, (base k).length

theorem totalLength_erase (base : Tapes K) (source : K) :
    totalLength (Function.update base source []) + (base source).length = totalLength base := by
  calc
    _ = ∑ k, (((Function.update base source []) k).length +
        if k = source then (base source).length else 0) := by
      simp [totalLength, Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k = source
      · subst k
        simp
      · simp [h]

theorem drain_conservation (clearKeys : List K) (base : Tapes K) :
    MachineDrainMany.steps clearKeys base +
      totalLength (MachineDrainMany.finalTapes clearKeys base) =
        totalLength base + clearKeys.length := by
  induction clearKeys generalizing base with
  | nil => simp [MachineDrainMany.steps, MachineDrainMany.finalTapes]
  | cons source rest ih =>
      have h := ih (Function.update base source [])
      have erase := totalLength_erase base source
      simp only [MachineDrainMany.steps, MachineDrainMany.finalTapes, List.length_cons]
      omega

theorem cleared_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    totalLength (MachineDrainMany.finalTapes clearKeys base) = (base accumulator).length := by
  have point (k : K) : (MachineDrainMany.finalTapes clearKeys base k).length =
      if k = accumulator then (base accumulator).length else 0 := by
    by_cases ha : k = accumulator
    · subst k
      simp [cleared_frame clearKeys base accumulator keepAccumulator]
    · by_cases ho : k = output
      · subst k
        simp [ha, cleared_frame clearKeys base output keepOutput, outputEmpty]
      · rw [MachineDrainMany.finalTapes_mem clearKeys base k (covers k ha ho)]
        simp [ha]
  simp only [totalLength, point]
  simp

theorem finishCost_eq_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    finishCost clearKeys accumulator base = totalLength base + clearKeys.length + 2 := by
  have h := drain_conservation clearKeys base
  rw [cleared_totalLength clearKeys accumulator output keepAccumulator keepOutput covers
    base outputEmpty] at h
  unfold finishCost
  omega


end DFVSGames.Foundations.Hastad.SourceRuntimeFinish


namespace DFVSGames.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

theorem prepend_replicate_word (c b : Nat) (suffix : List Bool) :
    List.replicate c true ++ (encodeWord b ++ suffix) =
      encodeWord (c + b) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

end DFVSGames.Foundations.Complexity.MachineUnaryAffineAt


namespace DFVSGames.Explicit.MachineUniformProgram

open Turing DFVSGames.Reduction
open DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad

abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def tokens (C : Nat) : List (MachineFieldTemplate.Token 4) :=
  [.copy 0, .copy 1, .copy 2] ++ List.replicate C (.copy 3)

inductive Label (C : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | scale (phase : Fin 3)
  | emit (label : MachineFieldTemplate.Label (tokens C).length)
  | finishStart
  | finish (label : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def headerNext {C : Nat} (i : Fin 3) : Label C :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .scale 0

def emitEntry (C : Nat) : Label C :=
  .emit (MachineFieldTemplate.startAt (tokens C).length 0)

end DFVSGames.Explicit.MachineUniformProgram


namespace DFVSGames.Explicit.MachineUniformHeaders

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineUniformProgram

def afterVertices (n : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n else []

def afterAlphabet (n q : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q else []

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q
    else if k = .occurrences then encodeWord Q else []

theorem first_result (n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .vertices
      (inputTapes (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes (encodeWord n ++ rest) .vertices) =
      afterVertices n rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices]

theorem second_result (n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .alphabet
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabet) =
      afterAlphabet n q rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet]

theorem third_result (n q Q : Nat) (body : List Bool) :
    SourceMachine.fieldTapes Tape.input .occurrences
      (afterAlphabet n q (encodeWord Q ++ body)) body
      (encodeWord Q ++ afterAlphabet n q (encodeWord Q ++ body) .occurrences) =
      resultTapes n q Q body := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterAlphabet, resultTapes]

end DFVSGames.Explicit.MachineUniformHeaders


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_FormulaEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity

open Target

def gameWords {q : Nat} (game : Instance q) : List Nat :=
  [game.vertices, q, game.constraints.length] ++ game.constraints.flatMap constraintWords

def gameBits {q : Nat} (game : Instance q) : List Bool := encodeWords (gameWords game)

end DFVSGames.Foundations.Complexity


namespace DFVSGames.Explicit.UniformTarget

open DFVSGames.Foundations Target Complexity
open DFVSGames.Integration
open MachineUniformCopyOrder

theorem mem_original {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q)
    (c : Constraint g.vertices q) (hc : c ∈ (construct C hC g).constraints) :
    c ∈ g.constraints := by
  obtain ⟨es, hes, hc⟩ := List.mem_flatten.mp hc
  have he : es = g.constraints := List.eq_of_mem_replicate hes
  simpa [he] using hc

theorem flatMap_copies {α β : Type*} (C : Nat) (xs : List α) (f : α → List β) :
    (copyMajor C xs).flatMap f = copyMajor C (xs.flatMap f) := by
  induction C with
  | zero => simp [copyMajor]
  | succ C ih =>
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons,
      List.flatMap_append] using congrArg (fun ys => xs.flatMap f ++ ys) ih

theorem encode_copies (C : Nat) (words : List Nat) :
    encodeWords (copyMajor C words) = copyMajor C (encodeWords words) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons,
      encodeWords_append] using congrArg (fun xs => encodeWords words ++ xs) ih

theorem gameWords_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameWords (construct C hC g) =
      [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (g.constraints.flatMap constraintWords) := by
  simp only [gameWords, vertices]
  rw [show (construct C hC g).constraints = copyMajor C g.constraints from rfl,
    flatMap_copies, copy_length]

theorem gameBits_construct {q : Nat} (C : Nat) (hC : 0 < C) (g : Instance q) :
    gameBits (construct C hC g) =
      encodeWords [g.vertices, q, C * g.constraints.length] ++
        copyMajor C (encodeWords (g.constraints.flatMap constraintWords)) := by
  rw [gameBits, gameWords_construct, encodeWords_append, encode_copies]

end DFVSGames.Explicit.UniformTarget

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionRows

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction

def rowBits {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List Bool := encodeWords ((rows vertices p).flatMap constraintWords)

end DFVSGames.Explicit.MachineSubdivisionRows


namespace DFVSGames.Explicit.MachineSubdivisionDynamicRows

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionRows (identityTable inverseTable)

def rows {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List (Constraint n q) :=
  [⟨vertices 0, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 1, identityTable q⟩,
   ⟨vertices 2, vertices 3, identityTable q⟩,
   ⟨vertices 4, vertices 3, p⟩]

def rowBits {n q : Nat} (vertices : Fin 5 → Fin n) (p : PermutationTable q) :
    List Bool := encodeWords ((rows vertices p).flatMap constraintWords)

end DFVSGames.Explicit.MachineSubdivisionDynamicRows


namespace DFVSGames.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem counterTapes_other (counter other : K) (hne : other ≠ counter)
    (base : K → List Bool) (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix other = base other := by
  simp [counterTapes, hne]

theorem stepAux_succ (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base (n + 1) suffix) =
      ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord, List.replicate_succ]

theorem stepAux_zero (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base 0 suffix) =
      ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord]

theorem guardStep_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩ =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base (n + 1) suffix)) = _
  rw [atGuard, stepAux_succ]

theorem guardStep_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩ =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base 0 suffix)) = _
  rw [atGuard, stepAux_zero]

theorem guardTrace_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register),
        counterTapes counter base (n + 1) suffix⟩) =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register

theorem guardTrace_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩) =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register

def guardInTime_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩
      (some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register
  steps_le_m := Nat.le_refl _

def guardInTime_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩
      (some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineUnaryCounter


namespace DFVSGames.Explicit.MachineSubdivisionProgram

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction

abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def rowTokens (q : Nat) := MachineSubdivisionDynamicRows.tokens
  (encodeWords (tableWords (MachineSubdivisionRows.identityTable q)))

def headerTokens (q : Nat) : List (MachineFieldTemplate.Token 2) :=
  [.copy 0, .literal (encodeWord q), .copy 1]

inductive Label (q : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | initialize_ (i : Fin 9) (phase : Fin 3)
  | emitHeader (label : MachineFieldTemplate.Label (headerTokens q).length)
  | guard
  | startU | readU | startV | readV
  | readTable (completed : Fin (q + 1))
  | reverseTable
  | emitRows (label : MachineFieldTemplate.Label (rowTokens q).length)
  | drainU | drainV | drainPermutation
  | increment
  | finishStart
  | finish (label : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def headerNext {q : Nat} (i : Fin 3) : Label q :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .initialize_ 0 0

def initNext {q : Nat} (i : Fin 9) : Label q :=
  if h : i.val + 1 < 9 then .initialize_ ⟨i.val + 1, h⟩ 0
  else .emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)

def rowEntry (q : Nat) : Label q :=
  .emitRows (MachineFieldTemplate.startAt (rowTokens q).length 0)

theorem clearKeys_covers (k : Tape) :
    k ∈ clearKeys ∨ k = .accumulator ∨ k = .output := by
  cases k <;> simp [clearKeys]

end DFVSGames.Explicit.MachineSubdivisionProgram


namespace DFVSGames.Explicit.MachineSubdivisionHeaders

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineSubdivisionProgram

def afterVertices (n : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n else []

def afterAlphabet (n q : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n
    else if k = .alphabetHeader then encodeWord q else []

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabetHeader then encodeWord q
    else if k = .occurrences then encodeWord Q else []

theorem first_result (n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .vertices
      (inputTapes (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes (encodeWord n ++ rest) .vertices) =
      afterVertices n rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices]

theorem second_result (n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .alphabetHeader
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabetHeader) =
      afterAlphabet n q rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet]

theorem third_result (n q Q : Nat) (body : List Bool) :
    SourceMachine.fieldTapes Tape.input .occurrences
      (afterAlphabet n q (encodeWord Q ++ body)) body
      (encodeWord Q ++ afterAlphabet n q (encodeWord Q ++ body) .occurrences) =
      resultTapes n q Q body := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterAlphabet, resultTapes]

end DFVSGames.Explicit.MachineSubdivisionHeaders

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionInit
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

def priorWord (seed : Option Nat) (b : Nat) : List Bool :=
  match seed with
  | none => encodeWord b
  | some _ => []

def frame (n q Q : Nat) (body : List Bool) : Nat → Tape → List Bool
  | 0 => MachineSubdivisionHeaders.resultTapes n q Q body
  | r + 1 => if h : r < 9 then
      Function.update (frame n q Q body r) (initOp ⟨r, h⟩).destination
        (encodeWord (afterValue n Q ⟨r, h⟩))
    else frame n q Q body r

theorem frame_source (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).source = encodeWord (sourceValue n Q i) := by
  fin_cases i <;>
    simp [frame, sourceValue, initOp, MachineSubdivisionHeaders.resultTapes]

theorem frame_scratch (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val .affineScratch = [] := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes]

theorem frame_destination (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).destination =
      priorWord (initOp i).seed (beforeValue n i) := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes,
    afterValue, sourceValue, beforeValue, priorWord]

def atStage (q r : Nat) : Label q :=
  if h : r < 9 then .initialize_ ⟨r, h⟩ 0
  else .emitHeader (MachineFieldTemplate.startAt (headerTokens q).length 0)

theorem initNext_eq_atStage (q : Nat) (i : Fin 9) :
    (initNext i : Label q) = atStage q (i.val + 1) := by
  simp [initNext, atStage]

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => body
  | .vertices => encodeWord n
  | .alphabetHeader => encodeWord q
  | .occurrences => encodeWord Q
  | .remaining => encodeWord Q
  | .newVertices => encodeWord (n + 3 * Q)
  | .newEdges => encodeWord (4 * Q)
  | .middle => encodeWord n
  | .first => encodeWord (n + Q)
  | .last => encodeWord (n + Q + 1)
  | _ => []

theorem final_frame (n q Q : Nat) (body : List Bool) :
    frame n q Q body 9 = resultTapes n q Q body := by
  funext tape
  cases tape <;>
    simp [frame, resultTapes, initOp, MachineSubdivisionHeaders.resultTapes,
      afterValue, sourceValue, beforeValue, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]

end DFVSGames.Explicit.MachineSubdivisionInit


namespace DFVSGames.Explicit.MachineSubdivisionEmission

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

def headerBits (n q Q : Nat) : List Bool := encodeWords [n + 3 * Q, q, 4 * Q]

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineSubdivisionInit.resultTapes n q Q body)
    .accumulator (headerBits n q Q).reverse

theorem header_result (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.outputTapes (MachineSubdivisionInit.resultTapes n q Q body)
      .accumulator (headerBits n q Q) = resultTapes n q Q body := by
  simp only [MachineFieldTemplate.outputTapes, MachineSubdivisionInit.resultTapes,
    List.append_nil, resultTapes]

end DFVSGames.Explicit.MachineSubdivisionEmission


namespace DFVSGames.Reduction.GameEncodingSize

open Foundations.Target Foundations.Complexity

theorem tableBits_length_le {q : Nat} (table : PermutationTable q) :
    (encodeWords (tableWords table)).length ≤ q * (q + 1) := by
  have h := encodeWords_length_le (tableWords table) q (by
    intro value hvalue
    obtain ⟨label, _, hlabel⟩ := List.mem_map.mp hvalue
    rw [← hlabel]
    exact Nat.le_of_lt label.isLt)
  simpa only [tableWords_length] using h

end DFVSGames.Reduction.GameEncodingSize


namespace DFVSGames.Explicit.MachineSubdivisionBody

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction
open MachineSubdivisionProgram

def tableBits {q : Nat} (table : Target.PermutationTable q) : List Bool :=
  encodeWords (tableWords table)

structure Ready {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Prop where
  input : base .input = encodeWord u ++ encodeWord v ++ tableBits table ++ suffix
  uEmpty : base .u = []
  vEmpty : base .v = []
  permutationEmpty : base .permutation = []
  reverseEmpty : base .permutationReverse = []
  scratchEmpty : base .copyScratch = []

def afterU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .u base u (encodeWord v ++ tableBits table ++ suffix)

def afterV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .v (afterU base u v table suffix) v (tableBits table ++ suffix)

def afterTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineSubdivisionTableRead.finalTapes (afterV base u v table suffix) suffix (tableBits table)

end DFVSGames.Explicit.MachineSubdivisionBody


namespace DFVSGames.Explicit.MachineSubdivisionLoopFrame

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

theorem bodyBits_cons {n q : Nat} (edge : Constraint n q) (edges : List (Constraint n q)) :
    bodyBits (edge :: edges) =
      encodeWord edge.source.val ++ encodeWord edge.target.val ++
        MachineSubdivisionBody.tableBits edge.permutation ++ bodyBits edges := by
  simp [bodyBits, constraintWords, encodeWords, MachineSubdivisionBody.tableBits,
    List.append_assoc]

def identityBits (q : Nat) : List Bool :=
  encodeWords (tableWords (MachineSubdivisionRows.identityTable q))

def rowBits {n q : Nat} (Q e : Nat) (edge : Constraint n q) : List Bool :=
  encodeWords [edge.source.val, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e + 1] ++ identityBits q ++
  encodeWords [edge.target.val, n + Q + 2 * e + 1] ++
    MachineSubdivisionBody.tableBits edge.permutation

def outputRows {n q : Nat} (Q : Nat) : Nat → List (Constraint n q) → List Bool
  | _, [] => []
  | e, edge :: edges => rowBits Q e edge ++ outputRows Q (e + 1) edges

def frame {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => bodyBits edges
  | .remaining => encodeWord edges.length
  | .middle => encodeWord (n + e)
  | .first => encodeWord (n + Q + 2 * e)
  | .last => encodeWord (n + Q + 2 * e + 1)
  | .accumulator => emitted.reverse
  | _ => MachineSubdivisionInit.resultTapes n q Q [] tape

def afterGuard {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) : Tape → List Bool :=
  Function.update (frame Q e (edge :: edges) emitted) .remaining (encodeWord edges.length)

theorem frame_prepared {n q : Nat} (edges : List (Constraint n q)) :
    frame edges.length 0 edges (MachineSubdivisionEmission.headerBits n q edges.length) =
      MachineSubdivisionEmission.resultTapes n q edges.length (bodyBits edges) := by
  funext tape
  cases tape <;> simp [frame, MachineSubdivisionEmission.resultTapes,
    MachineSubdivisionInit.resultTapes]

theorem ready {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.Ready (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) := by
  constructor
  · simpa only [afterGuard, Function.update_of_ne (by decide : Tape.input ≠ .remaining),
      frame] using bodyBits_cons edge edges
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]

end DFVSGames.Explicit.MachineSubdivisionLoopFrame


namespace DFVSGames.Explicit.MachineSubdivisionBodySpec

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction
open MachineSubdivisionProgram MachineSubdivisionBody

theorem encodeWord_succ (n : Nat) : encodeWord (n + 1) = true :: encodeWord n := by
  simp [encodeWord, List.replicate_succ]

def rowBits {q : Nat} (u middle first last v : Nat) (table : Target.PermutationTable q) :
    List Bool :=
  encodeWords
    ([u, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, last] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [v, last] ++ tableWords table)

theorem rowBits_eq_dynamic {N q : Nat} (vertices : Fin 5 → Fin N)
    (table : Target.PermutationTable q) :
    rowBits (vertices 0).val (vertices 2).val (vertices 1).val (vertices 3).val
      (vertices 4).val table = MachineSubdivisionDynamicRows.rowBits vertices table := by
  simp [rowBits, MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionDynamicRows.rows,
    constraintWords, List.append_assoc]

end DFVSGames.Explicit.MachineSubdivisionBodySpec

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeSpace
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceRuntimeSpace

open Turing Complexity
open scoped BigOperators

attribute [local instance] FinTM2.kFin

noncomputable def spacePolynomial (tm : FinTM2) (time : Polynomial Nat) : Polynomial Nat :=
  Polynomial.X + time * Polynomial.C (Fintype.card tm.K * Runtime.programPushBound tm)

theorem spacePolynomial_eval (tm : FinTM2) (time : Polynomial Nat) (N : Nat) :
    (spacePolynomial tm time).eval N = N +
      time.eval N * (Fintype.card tm.K * Runtime.programPushBound tm) := by
  simp [spacePolynomial]

theorem totalLength_eq_configurationLength (tm : FinTM2) (finish : tm.Cfg)
    (base : tm.K → List Bool)
    (sameLengths : ∀ k, (base k).length = (finish.stk k).length) :
    SourceRuntimeFinish.totalLength base = configurationLength tm finish := by
  exact Finset.sum_congr rfl (fun k _ => sameLengths k)

noncomputable def completedTime (tm : FinTM2) (clearKeyCount : Nat)
    (time : Polynomial Nat) : Polynomial Nat :=
  time + spacePolynomial tm time + Polynomial.C (clearKeyCount + 2)

theorem completedTime_eval (tm : FinTM2) (clearKeyCount : Nat)
    (time : Polynomial Nat) (N : Nat) :
    (completedTime tm clearKeyCount time).eval N = time.eval N +
      (N + time.eval N * (Fintype.card tm.K * Runtime.programPushBound tm)) +
      (clearKeyCount + 2) := by
  simp [completedTime, spacePolynomial_eval]

end DFVSGames.Foundations.Hastad.SourceRuntimeSpace


namespace DFVSGames.Foundations.Complexity.MachineRepeat
open Turing

abbrev Symbols (M : FinTM2) := MachineEmbedding.Alphabet M.Γ (fun _ : ExtraTape => M.Γ M.k₀)

def inputTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (initList M word).stk (extraTapes M counter [] [])

@[simp] theorem inputTapes_input (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inl M.k₀) = word := by
  simp [inputTapes, initList]

@[simp] theorem inputTapes_counter (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inr .counter) = counter := rfl

end DFVSGames.Foundations.Complexity.MachineRepeat


namespace DFVSGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

theorem of_homogeneous (M : FinTM2) {α : Type} [Finite α]
    (alphabet : ∀ k, M.Γ k = α) : FiniteAlphabet M := by
  intro k
  rw [alphabet k]
  infer_instance

theorem of_bool (M : FinTM2) (alphabet : ∀ k, M.Γ k = Bool) : FiniteAlphabet M :=
  of_homogeneous M alphabet

end DFVSGames.Foundations.Complexity.MachineFiniteAlphabet


namespace DFVSGames.Explicit.MachineUniformRun

open Turing DFVSGames.Reduction
open DFVSGames.Foundations Target
open DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad
open MachineUniformProgram

def outputBits (C n q Q : Nat) (body : List Bool) : List Bool :=
  encodeWords [n, q, C * Q] ++ MachineUniformCopyOrder.copyMajor C body

def afterScale (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineUniformHeaders.resultTapes n q Q body)
    .newOccurrences (encodeWord (C * Q))

def afterEmit (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterScale C n q Q body)
    .accumulator (outputBits C n q Q body)

theorem input_length (n q Q : Nat) (body : List Bool) :
    (encodeWords [n, q, Q] ++ body).length = n + q + Q + 3 + body.length := by
  simp [Nat.add_assoc]

end DFVSGames.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionLoop
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
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

theorem covers (k : Tape) (ha : k ≠ .accumulator) (ho : k ≠ .output) :
    k ∈ clearKeys := by
  rcases clearKeys_covers k with h | h | h
  · exact h
  · exact False.elim (ha h)
  · exact False.elim (ho h)

end DFVSGames.Explicit.MachineSubdivisionFinish


namespace DFVSGames.Explicit

namespace BipartiteGame

def Satisfied {L R E A : Type*} (G : BipartiteGame L R E A)
    (leftLabeling : L → A) (rightLabeling : R → A) (e : E) : Prop :=
  rightLabeling (G.right e) = G.permutation e (leftLabeling (G.left e))

instance satisfiedDecidable {L R E A : Type*} [DecidableEq A]
    (G : BipartiteGame L R E A) (a : L → A) (b : R → A) (e : E) :
    Decidable (G.Satisfied a b e) := inferInstanceAs (Decidable (_ = _))

end BipartiteGame


open scoped BigOperators

namespace OccurrenceGame

variable {V E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : OccurrenceGame V E A) (a : V → A) : Nat :=
  ∑ e, if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0

variable [Fintype V] [Fintype A]

noncomputable def maxSatisfied (g : OccurrenceGame V E A) : Nat := by
  classical
  exact Finset.univ.sup (satisfiedCount g)

noncomputable def value (g : OccurrenceGame V E A) : ℝ :=
  (maxSatisfied g : ℝ) / Fintype.card E

theorem satisfiedCount_le_maxSatisfied (g : OccurrenceGame V E A) (a : V → A) :
    satisfiedCount g a ≤ maxSatisfied g := by
  classical
  exact Finset.le_sup (f := satisfiedCount g) (Finset.mem_univ a)

theorem maxSatisfied_attained [Nonempty A] (g : OccurrenceGame V E A) :
    ∃ a, satisfiedCount g a = maxSatisfied g := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (satisfiedCount g)
  exact ⟨a, ha.symm⟩

end OccurrenceGame

namespace BipartiteGame

variable {L R E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : BipartiteGame L R E A) (a : L → A) (b : R → A) : Nat :=
  ∑ e, if g.permutation e (a (g.left e)) = b (g.right e) then 1 else 0

theorem satisfiedCount_eq_sum_satisfied (g : BipartiteGame L R E A)
    (a : L → A) (b : R → A) :
    satisfiedCount g a b = ∑ e, if g.Satisfied a b e then 1 else 0 := by
  classical
  unfold satisfiedCount
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : g.Satisfied a b e
  · have h' : g.permutation e (a (g.left e)) = b (g.right e) := Eq.symm h
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ g.permutation e (a (g.left e)) = b (g.right e) :=
      fun he => h he.symm
    rw [ite_eq_right h', ite_eq_right h]

variable [Fintype L] [Fintype R] [Fintype A]

noncomputable def maxSatisfied (g : BipartiteGame L R E A) : Nat := by
  classical
  exact Finset.univ.sup (fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)

noncomputable def value (g : BipartiteGame L R E A) : ℝ :=
  (maxSatisfied g : ℝ) / Fintype.card E

theorem satisfiedCount_le_maxSatisfied (g : BipartiteGame L R E A)
    (a : L → A) (b : R → A) : satisfiedCount g a b ≤ maxSatisfied g := by
  classical
  exact Finset.le_sup (f := fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)
    (Finset.mem_univ (a, b))

theorem maxSatisfied_attained [Nonempty A] (g : BipartiteGame L R E A) :
    ∃ a b, satisfiedCount g a b = maxSatisfied g := by
  classical
  obtain ⟨⟨a, b⟩, _, hab⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty
    (fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)
  exact ⟨a, b, hab.symm⟩

end BipartiteGame

namespace Subdivision

variable {V E A : Type*}

def extendRight (g : OccurrenceGame V E A) (a : V → A) : Right E → A :=
  fun eb => a (g.source eb.1)

variable [DecidableEq A]

theorem local_count_le (ρ : Equiv.Perm A) (u p q r v : A) :
    (if u = p then 1 else 0) + (if q = p then 1 else 0) +
      (if q = r then 1 else 0) + (if ρ.symm v = r then 1 else 0) ≤
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  by_cases h₀ : u = p <;> by_cases h₁ : q = p <;>
    by_cases h₂ : q = r <;> by_cases h₃ : ρ.symm v = r <;>
    by_cases h : ρ u = v <;> simp_all [Equiv.symm_apply_eq]

theorem local_count_extend (ρ : Equiv.Perm A) (u v : A) :
    (if u = u then 1 else 0) + (if u = u then 1 else 0) +
      (if u = u then 1 else 0) + (if ρ.symm v = u then 1 else 0) =
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  by_cases h : ρ u = v
  · have h' : ρ.symm v = u := by rw [← h, ρ.symm_apply_apply]
    simp [h, h']
  · have h' : ρ.symm v ≠ u := by
      intro he
      apply h
      rw [← he, ρ.apply_symm_apply]
    simp [h, h']

theorem count_on_occurrence_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i) (a ((game g).left (e, i))) =
        b ((game g).right (e, i)) then 1 else 0) ≤
      3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  exact local_count_le (g.permutation e)
      (a (Sum.inl (g.source e))) (b (e, false)) (a (Sum.inr e))
      (b (e, true)) (a (Sum.inl (g.target e)))

theorem count_on_occurrence_extend (g : OccurrenceGame V E A) (a : V → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i)
      (extendLeft g a ((game g).left (e, i))) =
        extendRight g a ((game g).right (e, i)) then 1 else 0) =
      3 + (if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  simpa [game, permutation, left, right, extendLeft, extendRight] using
    local_count_extend (g.permutation e) (a (g.source e)) (a (g.target e))

variable [Fintype E]

theorem satisfiedCount_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) :
    (game g).satisfiedCount a b ≤
      3 * Fintype.card E + g.satisfiedCount (restrict a) := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ e, (3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat)) :=
      Finset.sum_le_sum (fun e _ => count_on_occurrence_le g a b e)
    _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]

theorem satisfiedCount_extend (g : OccurrenceGame V E A) (a : V → A) :
    (game g).satisfiedCount (extendLeft g a) (extendRight g a) =
      3 * Fintype.card E + g.satisfiedCount a := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  simp_rw [count_on_occurrence_extend]
  simp [Finset.sum_add_distrib, Nat.mul_comm]

variable [Fintype V] [Fintype A] [Nonempty A]

theorem maxSatisfied_eq (g : OccurrenceGame V E A) :
    (game g).maxSatisfied = 3 * Fintype.card E + g.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro ab _
    exact (satisfiedCount_le g ab.1 ab.2).trans
      (Nat.add_le_add_left (g.satisfiedCount_le_maxSatisfied (restrict ab.1)) _)
  · obtain ⟨a, ha⟩ := g.maxSatisfied_attained
    rw [← ha, ← satisfiedCount_extend]
    exact BipartiteGame.satisfiedCount_le_maxSatisfied _ _ _

theorem value_eq [Nonempty E] (g : OccurrenceGame V E A) :
    (game g).value = 1 - (1 - g.value) / 4 := by
  have hE : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [BipartiteGame.value, maxSatisfied_eq, edge_count, OccurrenceGame.value]
  push_cast
  field_simp [hE]
  ring

end Subdivision

end DFVSGames.Explicit


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ProductTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.ProductTarget

open DFVSGames.Foundations
open Target
open MachineOutputContract
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

theorem render_get (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M)
    (i : Fin (render G vertices edges tables hM).constraints.length) :
    (render G vertices edges tables hM).constraints[i] =
      row G vertices edges tables ⟨i.val, by simpa using i.isLt⟩ := by
  change (List.ofFn (row G vertices edges tables))[i.val]'(by simpa using i.isLt) = _
  exact List.getElem_ofFn (by simpa using i.isLt)

def render_simpleBipartite (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ≃ Fin N) (edges : Fin M ≃ E)
    (tables : E → PermutationTable q) (hM : 0 < M) :
    SimpleBipartite (render G vertices edges tables hM) where
  side v := Sum.elim (fun _ => false) (fun _ => true) (vertices.symm v)
  sourceSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inl]
  targetSide i := by simp only [render_get, row, Equiv.symm_apply_apply, Sum.elim_inr]
  endpoints_injective := by
    intro i j hij
    have hi : i.val < M := by simpa using i.isLt
    have hj : j.val < M := by simpa using j.isLt
    have hrows :
        ((row G vertices edges tables ⟨i.val, hi⟩).source,
          (row G vertices edges tables ⟨i.val, hi⟩).target) =
        ((row G vertices edges tables ⟨j.val, hj⟩).source,
          (row G vertices edges tables ⟨j.val, hj⟩).target) := by
      simp only [render_get] at hij
      exact hij
    have hedge : edges ⟨i.val, hi⟩ = edges ⟨j.val, hj⟩ := by
      apply G.simple
      apply Prod.ext
      · exact Sum.inl.inj (vertices.injective (congrArg Prod.fst hrows))
      · exact Sum.inr.inj (vertices.injective (congrArg Prod.snd hrows))
    exact Fin.ext (congrArg (fun k : Fin M => k.val) (edges.injective hedge))

end DFVSGames.Explicit.ProductTarget


namespace DFVSGames.Explicit.SubdivisionTarget

open DFVSGames.Foundations Target
open MachineOutputContract
open scoped BigOperators

theorem tables_correspond {q : Nat} (H : Instance q)
    (ei : Fin H.constraints.length × Fin 4) :
    permutationEquiv (tables H ei) = (Subdivision.game (ofInstance H)).permutation ei := by
  ext a
  by_cases hi : ei.2 = 3 <;>
    simp [tables, permutationEquiv, Subdivision.game, Subdivision.permutation, ofInstance,
      MachineSubdivisionRows.inverseTable, MachineSubdivisionRows.identityTable, hi]

def vertexFields {q : Nat} (H : Instance q) (e : Fin H.constraints.length) :
    Fin 5 → Fin (H.vertices + 3 * H.constraints.length) :=
  ![numericVertexEquiv _ _ (Sum.inl (Sum.inl H.constraints[e].source)),
    numericVertexEquiv _ _ (Sum.inr (e, false)),
    numericVertexEquiv _ _ (Sum.inl (Sum.inr e)),
    numericVertexEquiv _ _ (Sum.inr (e, true)),
    numericVertexEquiv _ _ (Sum.inl (Sum.inl H.constraints[e].target))]

theorem vertexFields_val {q : Nat} (H : Instance q) (e : Fin H.constraints.length)
    (j : Fin 5) :
    (vertexFields H e j).val = MachineSubdivisionRows.subdivisionVertexWords
      H.vertices H.constraints.length H.constraints[e].source.val
        H.constraints[e].target.val e.val j := by
  fin_cases j <;> simp [vertexFields, MachineSubdivisionRows.subdivisionVertexWords]

theorem rows_eq {q : Nat} (H : Instance q) (e : Fin H.constraints.length) :
    List.ofFn (fun i : Fin 4 => ProductTarget.row (Subdivision.game (ofInstance H))
      (numericVertexEquiv H.vertices H.constraints.length)
      (numericEdgeEquiv H.constraints.length) (tables H)
      ((numericEdgeEquiv H.constraints.length).symm (e, i))) =
    MachineSubdivisionRows.rows (vertexFields H e) H.constraints[e].permutation := by
  simp [List.ofFn_succ, ProductTarget.row, Subdivision.game, Subdivision.left,
    Subdivision.right, ofInstance, tables, vertexFields, MachineSubdivisionRows.rows]

def simpleBipartite {q : Nat} (H : Instance q) : SimpleBipartite (subdivide H) :=
  ProductTarget.render_simpleBipartite _ _ _ _ _

end DFVSGames.Explicit.SubdivisionTarget


namespace DFVSGames.Explicit.SubdivisionEncoding

open DFVSGames.Foundations Target Complexity
open SubdivisionTarget

theorem subdivide_constraints {q : Nat} (H : Instance q) :
    (subdivide H).constraints =
      (List.ofFn (fun e : Fin H.constraints.length =>
        MachineSubdivisionRows.rows (vertexFields H e)
          H.constraints[e].permutation)).flatten := by
  change List.ofFn _ = _
  rw [List.ofFn_mul']
  congr 1
  apply congrArg List.ofFn
  funext e
  rw [← rows_eq H e]
  apply congrArg List.ofFn
  funext i
  congr 1
  apply Fin.ext
  simp only [numericEdgeEquiv_symm_val]

theorem subdivide_constraints_flatMap {q : Nat} (H : Instance q) :
    (subdivide H).constraints = (List.finRange H.constraints.length).flatMap
      (fun e => MachineSubdivisionRows.rows (vertexFields H e)
        H.constraints[e].permutation) := by
  rw [subdivide_constraints, List.ofFn_eq_map]
  rfl

theorem subdivide_gameWords {q : Nat} (H : Instance q) :
    gameWords (subdivide H) =
      [H.vertices + 3 * H.constraints.length, q, 4 * H.constraints.length] ++
      (List.finRange H.constraints.length).flatMap (fun e =>
        (MachineSubdivisionRows.rows (vertexFields H e)
          H.constraints[e].permutation).flatMap constraintWords) := by
  change [H.vertices + 3 * H.constraints.length, q, (subdivide H).constraints.length] ++
    (subdivide H).constraints.flatMap
      (@constraintWords (H.vertices + 3 * H.constraints.length) q) = _
  rw [subdivide_length, subdivide_constraints_flatMap, List.flatMap_assoc]

theorem encodeWords_flatMap_inline_SubdivisionEncoding {X : Type*} (xs : List X) (f : X → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem subdivide_gameBits {q : Nat} (H : Instance q) :
    gameBits (subdivide H) =
      encodeWords [H.vertices + 3 * H.constraints.length, q, 4 * H.constraints.length] ++
      (List.finRange H.constraints.length).flatMap (fun e =>
        MachineSubdivisionRows.rowBits (vertexFields H e) H.constraints[e].permutation) := by
  rw [gameBits, subdivide_gameWords, encodeWords_append, encodeWords_flatMap_inline_SubdivisionEncoding]
  rfl

end DFVSGames.Explicit.SubdivisionEncoding


namespace DFVSGames.Explicit.MachineSubdivisionCorrespondence

open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open MachineSubdivisionLoopFrame

def Involutive {q : Nat} (H : Instance q) : Prop :=
  ∀ e : Fin H.constraints.length,
    MachineSubdivisionRows.inverseTable H.constraints[e].permutation = H.constraints[e].permutation

theorem inverseTable_eq {q : Nat} (p : PermutationTable q)
    (same : p.inverseImages = p.images) : MachineSubdivisionRows.inverseTable p = p := by
  cases p with
  | mk images inverseImages left right =>
    dsimp at same
    cases same
    rfl

theorem rowBits_eq_semantic {q : Nat} (H : Instance q) (e : Fin H.constraints.length)
    (involutive : Involutive H) :
    rowBits H.constraints.length e.val H.constraints[e] =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
  have words := MachineSubdivisionBodySpec.rowBits_eq_dynamic
    (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation
  have vertices (j : Fin 5) := SubdivisionTarget.vertexFields_val H e j
  simp only [MachineSubdivisionRows.subdivisionVertexWords] at vertices
  have dynamic : MachineSubdivisionDynamicRows.rowBits
      (SubdivisionTarget.vertexFields H e) H.constraints[e].permutation =
      MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
        H.constraints[e].permutation := by
    simp only [MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionRows.rowBits,
      MachineSubdivisionDynamicRows.rows, MachineSubdivisionRows.rows, involutive e]
  rw [← dynamic, ← words]
  simp only [vertices, MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem outputRows_eq_ofFn {n q : Nat} (Q e : Nat) (edges : List (Constraint n q)) :
    outputRows Q e edges =
      (List.ofFn (fun i : Fin edges.length => rowBits Q (e + i.val) edges[i])).flatten := by
  induction edges generalizing e with
  | nil => rfl
  | cons edge edges ih =>
    rw [outputRows, ih, List.ofFn_succ]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem outputRows_eq_semantic {q : Nat} (H : Instance q) (involutive : Involutive H) :
    outputRows H.constraints.length 0 H.constraints =
      (List.finRange H.constraints.length).flatMap (fun e =>
        MachineSubdivisionRows.rowBits (SubdivisionTarget.vertexFields H e)
          H.constraints[e].permutation) := by
  rw [outputRows_eq_ofFn]
  simp only [Nat.zero_add, rowBits_eq_semantic H _ involutive, List.ofFn_eq_map,
    List.flatMap_def]

theorem output_eq_gameBits {q : Nat} (H : Instance q) (involutive : Involutive H) :
    MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints =
      gameBits (SubdivisionTarget.subdivide H) := by
  rw [SubdivisionEncoding.subdivide_gameBits, outputRows_eq_semantic H involutive]
  rfl

end DFVSGames.Explicit.MachineSubdivisionCorrespondence


namespace DFVSGames.Explicit.MachineSubdivisionRuntime

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame
open MachineSubdivisionCorrespondence

noncomputable section

theorem input_eq {q : Nat} (H : Instance q) :
    gameBits H = encodeWords [H.vertices, q, H.constraints.length] ++ bodyBits H.constraints := by
  simp only [gameBits, gameWords, bodyBits, encodeWords_append]

theorem input_size {q : Nat} (H : Instance q) :
    H.vertices ≤ (gameBits H).length ∧ H.constraints.length ≤ (gameBits H).length := by
  rw [input_eq]
  simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

def finalTapes {q : Nat} (H : Instance q) : Tape → List Bool :=
  frame H.constraints.length H.constraints.length ([] : List (Constraint H.vertices q))
    (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
      outputRows H.constraints.length 0 H.constraints)

theorem final_outputEmpty {q : Nat} (H : Instance q) : finalTapes H .output = [] := rfl

theorem final_accumulator {q : Nat} (H : Instance q) (involutive : Involutive H) :
    finalTapes H .accumulator = (gameBits (SubdivisionTarget.subdivide H)).reverse := by
  change (MachineSubdivisionEmission.headerBits H.vertices q H.constraints.length ++
    outputRows H.constraints.length 0 H.constraints).reverse = _
  rw [output_eq_gameBits H involutive]

end
end DFVSGames.Explicit.MachineSubdivisionRuntime


namespace DFVSGames.Explicit.MachineSubdivisionCompose

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open MachineSubdivisionCorrespondence

noncomputable section

variable {α : Type} {q : Nat} {encode : α → List Bool} {f : α → Instance q}

def certifiedOutput (involutive : ∀ a, Involutive (f a)) (a : α) :
    {H : Instance q // Involutive H} := ⟨f a, involutive a⟩

def certify (upstream : TM2ComputableInPolyTime encode gameBits f)
    (involutive : ∀ a, Involutive (f a)) :
    TM2ComputableInPolyTime encode (fun H : {H : Instance q // Involutive H} => gameBits H.val)
      (certifiedOutput involutive) where
  tm := upstream.tm
  inputAlphabet := upstream.inputAlphabet
  outputAlphabet := upstream.outputAlphabet
  time := upstream.time
  outputsFun := upstream.outputsFun

end
end DFVSGames.Explicit.MachineSubdivisionCompose

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Basic
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem probability_nonnegative (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    0 ≤ μ.probability event := by
  apply Finset.sum_nonneg
  intro x _
  split
  · exact μ.nonnegative x
  · exact le_rfl

theorem probability_le_one (μ : FiniteDistribution Ω) (event : Ω → Bool) :
    μ.probability event ≤ 1 := by
  rw [← μ.normalized]
  apply Finset.sum_le_sum
  intro x _
  split
  · exact le_rfl
  · exact μ.nonnegative x

theorem probability_mono (μ : FiniteDistribution Ω) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    μ.probability event ≤ μ.probability event' := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · simp [hx, h x hx]
  · simp [hx]
    split
    · exact μ.nonnegative x
    · exact le_rfl

theorem probability_pushforward (μ : FiniteDistribution Ω) (f : Ω → Γ)
    (event : Γ → Bool) :
    (μ.pushforward f).probability event = μ.probability (fun x => event (f x)) := by
  classical
  simp only [probability, pushforward]
  calc
    _ = ∑ y, ∑ x, if f x = y then (if event y then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : event y = true <;> simp [hy]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem probability_transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ)
    (event : Γ → Bool) :
    (μ.transport equiv).probability event = μ.probability (fun x => event (equiv x)) := by
  unfold probability transport
  exact Fintype.sum_equiv equiv.symm _ _ (fun _ => by simp)

theorem probability_iid_all (μ : FiniteDistribution Ω) (event : Ω → Bool) (n : Nat) :
    (μ.iid n).probability (fun x => decide (∀ i, event (x i) = true)) =
      μ.probability event ^ n := by
  classical
  unfold probability iid
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq]
  by_cases h : ∀ i, event (x i) = true
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

theorem success_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : 0 ≤ G.success strategy :=
  G.questions.probability_nonnegative _

theorem success_le_one (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ 1 :=
  G.questions.probability_le_one _

def repeatStrategy (strategy : Strategy Q₁ Q₂ A₁ A₂) (n : Nat) :
    Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) :=
  (fun x i => strategy.1 (x i), fun y i => strategy.2 (y i))

theorem success_repeatStrategy (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) (n : Nat) :
    (G.repetition n).success (repeatStrategy strategy n) = G.success strategy ^ n := by
  unfold success
  change ((G.questions.iid n).transport (tupleQuestionEquiv n)).probability _ = _
  rw [FiniteDistribution.probability_transport]
  exact G.questions.probability_iid_all (G.wins strategy) n

end Game

end

end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ G.value := by
  classical
  exact Finset.le_sup' G.success (Finset.mem_univ strategy)

theorem value_le_iff (G : Game Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    G.value ≤ bound ↔ ∀ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy ≤ bound := by
  classical
  simp [value, Finset.sup'_le_iff]

theorem exists_optimal_strategy (G : Game Q₁ Q₂ A₁ A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂, G.success strategy = G.value := by
  classical
  obtain ⟨strategy, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Strategy Q₁ Q₂ A₁ A₂))) Finset.univ_nonempty G.success
  exact ⟨strategy, h.symm⟩

theorem value_le_one (G : Game Q₁ Q₂ A₁ A₂) : G.value ≤ 1 :=
  (G.value_le_iff 1).2 G.success_le_one

end Game

end

end DFVSGames.Foundations.Games


namespace DFVSGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

theorem iid_pushforward {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f : Ω → Γ) (n : Nat) :
    (μ.pushforward f).iid n =
      (μ.iid n).pushforward (fun answers i => f (answers i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [iid, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f (x i)) = y
  · have hp : ∀ i, f (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, f (x i) = y i := fun hp => h (funext hp)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem iid_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (n : Nat) :
    (uniform Ω).iid n = uniform (Fin n → Ω) := by
  classical
  apply eq_of_weight_eq
  intro x
  simp [iid, uniform, Nat.cast_pow, one_div]

end
end DFVSGames.Foundations.Games.FiniteDistribution


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Product
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit

open DFVSGames.Foundations.Games
open scoped BigOperators

namespace BipartiteGame

variable {L R E A : Type*}

noncomputable section

variable [Fintype L] [Fintype R] [Fintype E] [Fintype A] [Nonempty E]

theorem toGame_isProjection (G : BipartiteGame L R E A) :
    DFVSGames.Repetition.IsProjection G.toGame := by
  classical
  intro x y a b b' hb hb'
  simp only [toGame, decide_eq_true_eq] at hb hb'
  obtain ⟨e, heL, heR, he⟩ := hb
  obtain ⟨f, hfL, hfR, hf⟩ := hb'
  have hef : e = f := G.simple (Prod.ext (heL.trans hfL.symm) (heR.trans hfR.symm))
  subst f
  exact he.trans hf.symm

def occurrenceSuccess (G : BipartiteGame L R E A)
    (strategy : Strategy L R A A) : ℝ := by
  classical
  exact (FiniteDistribution.uniform E).probability
    (fun e => decide (G.Satisfied strategy.1 strategy.2 e))

theorem toGame_success (G : BipartiteGame L R E A)
    (strategy : Strategy L R A A) :
    G.toGame.success strategy = G.occurrenceSuccess strategy := by
  classical
  unfold Game.success occurrenceSuccess
  change ((FiniteDistribution.uniform E).pushforward _).probability _ = _
  rw [FiniteDistribution.probability_pushforward]
  congr 1
  funext e
  apply Bool.eq_iff_iff.mpr
  change G.toGame.accepts (G.left e) (G.right e)
      (strategy.1 (G.left e)) (strategy.2 (G.right e)) = true ↔
    decide (G.Satisfied strategy.1 strategy.2 e) = true
  constructor
  · intro h
    exact decide_eq_true ((G.toGame_accepts_on_edge e _ _).mp h)
  · intro h
    exact (G.toGame_accepts_on_edge e _ _).mpr (of_decide_eq_true h)

theorem toGame_success_eq_satisfiedCount [DecidableEq A]
    (G : BipartiteGame L R E A) (strategy : Strategy L R A A) :
    G.toGame.success strategy =
      (G.satisfiedCount strategy.1 strategy.2 : ℝ) / Fintype.card E := by
  classical
  rw [toGame_success, satisfiedCount_eq_sum_satisfied]
  unfold occurrenceSuccess FiniteDistribution.probability FiniteDistribution.uniform
  simp only [decide_eq_true_eq, Nat.cast_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : G.Satisfied strategy.1 strategy.2 e <;> simp [h]

theorem product_success_eq_repetition (G : BipartiteGame L R E A) (t : ℕ)
    (strategy : Strategy (Fin t → L) (Fin t → R) (Fin t → A) (Fin t → A)) :
    (G.product t).toGame.success strategy = (G.toGame.repetition t).success strategy := by
  classical
  let : DecidableEq (Fin t → A) := fun a b => Classical.propDecidable (a = b)
  rw [toGame_success]
  unfold occurrenceSuccess Game.success
  change (FiniteDistribution.uniform (Fin t → E)).probability _ =
    ((G.toGame.questions.iid t).transport (Game.tupleQuestionEquiv t)).probability _
  rw [FiniteDistribution.probability_transport]
  change _ = (((FiniteDistribution.uniform E).pushforward
    (fun e => (G.left e, G.right e))).iid t).probability _
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.probability_pushforward,
    FiniteDistribution.iid_uniform]
  congr 1
  funext edges
  apply Bool.eq_iff_iff.mpr
  change _ ↔
    (G.toGame.repetition t).accepts (fun i => G.left (edges i))
      (fun i => G.right (edges i))
      (strategy.1 (fun i => G.left (edges i)))
      (strategy.2 (fun i => G.right (edges i))) = true
  rw [decide_eq_true_eq, Game.repetition_accepts_iff]
  constructor
  · intro h i
    apply (G.toGame_accepts_on_edge (edges i) _ _).mpr
    exact congrFun h i
  · intro h
    funext i
    exact (G.toGame_accepts_on_edge (edges i) _ _).mp (h i)

theorem product_coordinate_success (G : BipartiteGame L R E A) (t : ℕ)
    (strategy : Strategy L R A A) :
    (G.product t).toGame.success (Game.repeatStrategy strategy t) =
      G.toGame.success strategy ^ t := by
  rw [product_success_eq_repetition, Game.success_repeatStrategy]

theorem one_sub_mul_one_sub_le_pow {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) (t : ℕ) :
    1 - (t : ℝ) * (1 - p) ≤ p ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hmul := mul_le_mul_of_nonneg_right ih hp0
      have hnonneg : 0 ≤ (t : ℝ) * (1 - p) ^ 2 := by positivity
      rw [pow_succ]
      push_cast
      nlinarith

theorem product_coordinate_completeness (G : BipartiteGame L R E A) (t : ℕ)
    (strategy : Strategy L R A A) {error : ℝ}
    (hcomplete : 1 - error ≤ G.toGame.success strategy) :
    1 - (t : ℝ) * error ≤
      (G.product t).toGame.success (Game.repeatStrategy strategy t) := by
  rw [product_coordinate_success]
  have hbound := one_sub_mul_one_sub_le_pow
    (G.toGame.success_nonnegative strategy) (G.toGame.success_le_one strategy) t
  have hmul := mul_le_mul_of_nonneg_left hcomplete (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  linarith

variable [Nonempty A]

theorem toGame_value [DecidableEq A] (G : BipartiteGame L R E A) :
    G.toGame.value = G.value := by
  apply le_antisymm
  · apply (G.toGame.value_le_iff _).2
    intro strategy
    rw [toGame_success_eq_satisfiedCount, value]
    exact div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (G.satisfiedCount_le_maxSatisfied strategy.1 strategy.2))
      (Nat.cast_nonneg _)
  · obtain ⟨a, b, hab⟩ := G.maxSatisfied_attained
    have hs := G.toGame.success_le_value (a, b)
    rw [toGame_success_eq_satisfiedCount, hab] at hs
    exact hs

theorem product_value_eq_repetition (G : BipartiteGame L R E A) (t : ℕ) :
    (G.product t).toGame.value = (G.toGame.repetition t).value := by
  apply le_antisymm
  · apply ((G.product t).toGame.value_le_iff _).2
    intro strategy
    rw [product_success_eq_repetition]
    exact (G.toGame.repetition t).success_le_value strategy
  · apply ((G.toGame.repetition t).value_le_iff _).2
    intro strategy
    rw [← product_success_eq_repetition]
    exact (G.product t).toGame.success_le_value strategy

theorem product_completeness (G : BipartiteGame L R E A) (t : ℕ) {error : ℝ}
    (hcomplete : 1 - error ≤ G.toGame.value) :
    1 - (t : ℝ) * error ≤ (G.product t).toGame.value := by
  obtain ⟨strategy, hstrategy⟩ := G.toGame.exists_optimal_strategy
  have hs := G.product_coordinate_completeness t strategy (hstrategy.symm ▸ hcomplete)
  exact hs.trans ((G.product t).toGame.success_le_value _)

end

noncomputable section

variable {B : Type*} [Fintype L] [Fintype R] [Fintype E]
  [Fintype A] [Fintype B] [Nonempty E]

theorem relabel_success (G : BipartiteGame L R E A) (e : A ≃ B)
    (strategy : Strategy L R B B) :
    (G.relabel e).toGame.success strategy =
      G.toGame.success (fun x => e.symm (strategy.1 x), fun y => e.symm (strategy.2 y)) := by
  classical
  rw [toGame_success, toGame_success]
  unfold occurrenceSuccess
  congr 1
  funext f
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have h' := of_decide_eq_true h
    apply decide_eq_true
    apply e.injective
    simpa only [Satisfied, relabel, Equiv.trans_apply, Equiv.apply_symm_apply] using h'
  · intro h
    have h' := of_decide_eq_true h
    apply decide_eq_true
    simpa only [Satisfied, relabel, Equiv.trans_apply, Equiv.apply_symm_apply] using congrArg e h'

theorem relabel_success_forward (G : BipartiteGame L R E A) (e : A ≃ B)
    (strategy : Strategy L R A A) :
    (G.relabel e).toGame.success
      (fun x => e (strategy.1 x), fun y => e (strategy.2 y)) =
      G.toGame.success strategy := by
  rw [relabel_success]
  congr 1
  apply Prod.ext <;> funext x <;> simp

theorem relabel_value [Nonempty A] [Nonempty B]
    (G : BipartiteGame L R E A) (e : A ≃ B) :
    (G.relabel e).toGame.value = G.toGame.value := by
  apply le_antisymm
  · apply ((G.relabel e).toGame.value_le_iff _).2
    intro strategy
    rw [relabel_success]
    exact G.toGame.success_le_value _
  · apply (G.toGame.value_le_iff _).2
    intro strategy
    rw [← G.relabel_success_forward e strategy]
    exact (G.relabel e).toGame.success_le_value _

end

def binaryProductEquiv (ell t : ℕ) :
    (Fin t → Fin ell → ZMod 2) ≃+ (Fin (ell * t) → ZMod 2) where
  toFun a j := a ((finProdFinEquiv.symm j : Fin ell × Fin t).2)
    ((finProdFinEquiv.symm j : Fin ell × Fin t).1)
  invFun a i j := a (finProdFinEquiv (j, i))
  left_inv a := by funext i j; simp
  right_inv a := by
    funext j
    change a (finProdFinEquiv (finProdFinEquiv.symm j : Fin ell × Fin t)) = a j
    rw [Equiv.apply_symm_apply]
  map_add' _ _ := rfl

end BipartiteGame

end DFVSGames.Explicit


namespace DFVSGames.Explicit.ProductPaddedOutput

open DFVSGames.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

namespace Embedded

variable {L R E : Type*} {q N M : ℕ}

theorem render_get (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (i : Fin (render G vertices edges hM).constraints.length) :
    (render G vertices edges hM).constraints[i] =
      row G vertices edges ⟨i.val, by simpa using i.isLt⟩ := by
  change (List.ofFn (row G vertices edges))[i.val]'(by simpa using i.isLt) = _
  exact List.getElem_ofFn (by simpa using i.isLt)

def simpleBipartite (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (side : Fin N → Bool)
    (leftSide : ∀ x, side (vertices (Sum.inl x)) = false)
    (rightSide : ∀ y, side (vertices (Sum.inr y)) = true) :
    SimpleBipartite (render G vertices edges hM) where
  side := side
  sourceSide i := by simp only [render_get, row, leftSide]
  targetSide i := by simp only [render_get, row, rightSide]
  endpoints_injective := by
    intro i j hij
    have hi : i.val < M := by simpa using i.isLt
    have hj : j.val < M := by simpa using j.isLt
    have hrows :
        ((row G vertices edges ⟨i.val, hi⟩).source,
          (row G vertices edges ⟨i.val, hi⟩).target) =
        ((row G vertices edges ⟨j.val, hj⟩).source,
          (row G vertices edges ⟨j.val, hj⟩).target) := by
      simp only [render_get] at hij
      exact hij
    have he : edges ⟨i.val, hi⟩ = edges ⟨j.val, hj⟩ := by
      apply G.simple
      apply Prod.ext
      · exact Sum.inl.inj (vertices.injective (congrArg Prod.fst hrows))
      · exact Sum.inr.inj (vertices.injective (congrArg Prod.snd hrows))
    exact Fin.ext (congrArg (fun k : Fin M => k.val) (edges.injective he))


variable [Fintype L] [Fintype R] [Fintype E]

omit [Fintype L] [Fintype R] in
@[simp] theorem extendLabelings_left [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) (x : L) :
    extendLabelings vertices left right (vertices (Sum.inl x)) = left x := by
  exact vertices.injective.extend_apply _ _ _

omit [Fintype L] [Fintype R] in
@[simp] theorem extendLabelings_right [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) (y : R) :
    extendLabelings vertices left right (vertices (Sum.inr y)) = right y := by
  exact vertices.injective.extend_apply _ _ _

end Embedded

variable {q : ℕ} (H : Instance q) (presentation : SimpleBipartite H)

local instance productConstraintIndicesNonempty : Nonempty (Fin H.constraints.length) :=
  ⟨⟨0, H.constraintCount_positive⟩⟩

def side (t : ℕ) (ht : 0 < t) (v : Fin (H.vertices ^ t)) : Bool :=
  presentation.side (finFunctionFinEquiv.symm v ⟨0, ht⟩)

theorem side_left (t : ℕ) (ht : 0 < t) (x : Fin t → Left H presentation) :
    side H presentation t ht (vertices H presentation t ht (Sum.inl x)) = false := by
  change presentation.side
    (finFunctionFinEquiv.symm (finFunctionFinEquiv (fun index => (x index).val))
      ⟨0, ht⟩) = false
  simpa only [Equiv.symm_apply_apply] using (x ⟨0, ht⟩).property

theorem side_right (t : ℕ) (ht : 0 < t) (y : Fin t → Right H presentation) :
    side H presentation t ht (vertices H presentation t ht (Sum.inr y)) = true := by
  change presentation.side
    (finFunctionFinEquiv.symm (finFunctionFinEquiv (fun index => (y index).val))
      ⟨0, ht⟩) = true
  simpa only [Equiv.symm_apply_apply] using (y ⟨0, ht⟩).property

def simpleBipartite (t : ℕ) (ht : 0 < t) : SimpleBipartite (output H presentation t ht) :=
  Embedded.simpleBipartite _ _ _ _ (side H presentation t ht)
    (side_left H presentation t ht) (side_right H presentation t ht)

theorem outputRow_images (t : ℕ) (ht : 0 < t)
    (i : Fin (H.constraints.length ^ t)) (a : Fin (q ^ t)) :
    (outputRow H presentation t ht i).permutation.images[a] =
      finFunctionFinEquiv (fun j =>
        H.constraints[finFunctionFinEquiv.symm i j].permutation.images[
          finFunctionFinEquiv.symm a j]) := by
  simp [outputRow, Embedded.row, graph, BipartiteGame.relabel, BipartiteGame.product,
    SimpleBipartite.toBipartiteGame, permutationEquiv, fullTable]

theorem output_gameWords (t : ℕ) (ht : 0 < t) :
    Complexity.gameWords (output H presentation t ht) =
      [H.vertices ^ t, q ^ t, H.constraints.length ^ t] ++
        (List.ofFn (outputRow H presentation t ht)).flatMap Complexity.constraintWords := by
  simp only [Complexity.gameWords, output_vertices, output_constraints, List.length_ofFn]

def finalCoordinates {ell : ℕ} (coordinates : Fin q ≃ (Fin ell → ZMod 2)) (t : ℕ) :
    Fin (q ^ t) ≃ (Fin (ell * t) → ZMod 2) :=
  finFunctionFinEquiv.symm.trans
    ((Equiv.piCongrRight (fun _ : Fin t => coordinates)).trans
      (BipartiteGame.binaryProductEquiv ell t).toEquiv)

theorem finalCoordinates_apply {ell : ℕ}
    (coordinates : Fin q ≃ (Fin ell → ZMod 2)) (t : ℕ) (a : Fin (q ^ t)) :
    finalCoordinates coordinates t a = BipartiteGame.binaryProductEquiv ell t
      (fun i => coordinates (finFunctionFinEquiv.symm a i)) := rfl

end DFVSGames.Explicit.ProductPaddedOutput


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLookupSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineLookupSpec

theorem encoded_selected_split (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    encodeWords values = encodeWords (values.take i) ++ encodeWord value ++
      encodeWords (values.drop (i + 1)) := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  have hs : values = values.take i ++ value :: values.drop (i + 1) := by
    calc
      values = values.take i ++ values.drop i := (List.take_append_drop i values).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hv]
  simpa only [encodeWords_append, encodeWords, List.append_assoc] using
    congrArg encodeWords hs

def scannedBits (values : List Nat) (i : Nat) : Nat :=
  (encodeWords (values.take (i + 1))).length

theorem encoded_prefix_length_le (values : List Nat) (i : Nat) :
    (encodeWords (values.take i)).length ≤ (encodeWords values).length := by
  have hs : encodeWords (values.take i) ++ encodeWords (values.drop i) =
      encodeWords values := by
    rw [← encodeWords_append, List.take_append_drop]
  have hl := congrArg List.length hs
  simp only [List.length_append] at hl
  omega

theorem scannedBits_le (values : List Nat) (i : Nat) :
    scannedBits values i ≤ (encodeWords values).length :=
  encoded_prefix_length_le values (i + 1)

theorem scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    scannedBits values i = (encodeWords (values.take i)).length + value + 1 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  simp [scannedBits, List.take_succ_eq_append_getElem hi, hv, encodeWords,
    Nat.add_assoc]

theorem selected_scan_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWords (values.take i)).length + value + 1 ≤
      (encodeWords values).length := by
  rw [← scannedBits_of_some values i value h]
  exact scannedBits_le values i

theorem output_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord value).length ≤ (encodeWords values).length := by
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

theorem index_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord i).length ≤ (encodeWords values).length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  have hp : i ≤ (encodeWords (values.take i)).length := by
    simp only [encodeWords_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

theorem steps_le_encoded_length_strong (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero =>
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega
    | succ i =>
      have ht := ih i
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_lt (values : List Nat) (i : Nat)
    (h : i < values.length) :
    steps values i = scannedBits values i + i + 2 := by
  induction values generalizing i with
  | nil => simp at h
  | cons n ns ih =>
    cases i with
    | zero => simp [steps, scannedBits, encodeWords, Nat.add_assoc]
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [scannedBits] at ht
      simp only [steps, scannedBits, List.take_succ_cons, encodeWords,
        List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    steps values i = scannedBits values i + i + 2 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  exact steps_eq_scannedBits_of_lt values i hi

theorem steps_le_input_encoding_size (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * (encodeWord i).length := by
  have h := steps_le_encoded_length_strong values i
  rw [encodeWord_length]
  omega

end DFVSGames.Foundations.Complexity.MachineLookupSpec


namespace DFVSGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem discardStep_delimiter (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (false :: suffix)⟩ =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (false :: suffix))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

theorem discardStep_true (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (input : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), Function.update base source (true :: input)⟩ =
      some ⟨some loopLabel, (ambient, some true), Function.update base source input⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (Function.update base source (true :: input))) = _
  rw [atLoop]
  simp [discard, TM2.stepAux]

theorem discardTrace_update (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register),
        Function.update base source (encodeWord n ++ suffix)⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  induction n generalizing register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
      discardStep_delimiter source loopLabel returnLabel program atLoop
        base suffix ambient register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        Function.update base source (true :: (encodeWord n ++ suffix))⟩) = _
    rw [discardStep_true source loopLabel returnLabel program atLoop, ih]

theorem discardTrace (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩ := by
  have hbase : Function.update base source (encodeWord n ++ suffix) = base := by
    funext p
    by_cases hp : p = source
    · subst p; simp [hinput]
    · simp [hp]
  have h := discardTrace_update source loopLabel returnLabel program atLoop
    base n suffix ambient register
  rw [hbase] at h
  exact h

def discardInTime (source : K) (loopLabel returnLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = discard source loopLabel returnLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨some returnLabel, (ambient, none), Function.update base source suffix⟩)
      (n + 1) where
  steps := n + 1
  evals_in_steps := discardTrace source loopLabel returnLabel program atLoop
    base n suffix hinput ambient register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineLookup


namespace DFVSGames.Foundations.Complexity.MachineSubroutine

open Turing

variable {K Λ Λ' σ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement labels exit q) state tapes =
      configuration labels exit (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [statement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [statement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => cases exit <;> rfl

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit a) =
      some (configuration labels exit b) := by
  cases a with
  | mk l state tapes =>
      cases l with
      | none => simp [TM2.step] at h
      | some l =>
          have hb : TM2.stepAux (source l) state tapes = b := Option.some.inj h
          rw [← hb]
          change some (TM2.stepAux (target (labels l)) state tapes) = _
          rw [atLabels, stepAux_simulation]

theorem trace (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (steps : Nat) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration labels exit a)) = some (configuration labels exit b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) steps a b run

def execution (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit a) (some (configuration labels exit b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit) (step_simulation labels exit source target atLabels) run

end DFVSGames.Foundations.Complexity.MachineSubroutine


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem preservingLookup_steps_le (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) :
    2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 ≤
      5 * (encodeWords values).length + 3 := by
  have ht := MachineLookupSpec.steps_le_input_encoding_size values i
  have hi := MachineLookupSpec.index_length_le values i value selected
  omega

end DFVSGames.Foundations.Complexity.MachinePreservingLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAffineLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def steps (values : List Nat) (a coefficient offset : Nat) : Nat :=
  (2 * (a + 1) + 1) +
    (2 * ((encodeWords values).length + 1) +
      MachineLookupSpec.steps values (coefficient * a + offset) + 1)

theorem steps_le (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value) :
    steps values a coefficient offset ≤ 2 * a + 5 * (encodeWords values).length + 6 := by
  have h := MachinePreservingLookup.preservingLookup_steps_le values
    (coefficient * a + offset) value selected
  unfold steps
  omega

theorem steps_le_table (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value)
    (ha : a ≤ (encodeWords values).length) :
    steps values a coefficient offset ≤ 7 * (encodeWords values).length + 6 := by
  have h := steps_le values a coefficient offset value selected
  omega

end DFVSGames.Foundations.Complexity.MachineAffineLookup


namespace DFVSGames.Explicit.MachineProductGather

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def steps (values : List Nat) (coefficient : Nat) :
    (width : Nat) → (Fin width → Nat) → (Fin width → Nat) → Nat
  | 0, _, _ => 1
  | width + 1, indices, offsets =>
    MachineAffineLookup.steps values (indices 0) coefficient (offsets 0) +
      steps values coefficient width (fun i => indices i.succ) (fun i => offsets i.succ)

theorem steps_le (values : List Nat) (coefficient width magnitude : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (bounded : ∀ i, indices i ≤ magnitude) :
    steps values coefficient width indices offsets ≤
      width * (2 * magnitude + 5 * (encodeWords values).length + 6) + 1 := by
  induction width with
  | zero => simp [steps]
  | succ width ih =>
    have first := MachineAffineLookup.steps_le values (indices 0) coefficient (offsets 0)
      (fields 0) (selected 0)
    have rest := ih (fun i => indices i.succ) (fun i => offsets i.succ)
      (fun i => fields i.succ) (fun i => selected i.succ) (fun i => bounded i.succ)
    have hb := bounded 0
    rw [steps, Nat.add_mul, Nat.one_mul]
    omega

end DFVSGames.Explicit.MachineProductGather


namespace DFVSGames.Foundations.Complexity.MachineCountedLoop

open Turing
open scoped BigOperators
open MachineUnaryCounter

variable {K Λ σ : Type} [DecidableEq K]

def guardConfiguration (counter : K) (guardLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some guardLabel, (ambient n, register n), counterTapes counter (base n) n suffix⟩

def bodyConfiguration (counter : K) (bodyLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (n + 1), none), counterTapes counter (base (n + 1)) n suffix⟩

def exitConfiguration (counter : K) (exitLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none), counterTapes counter (base 0) 0 suffix⟩

def BodyTraces (counter : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n →
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some (bodyConfiguration counter bodyLabel suffix ambient base r)) =
      some (guardConfiguration counter guardLabel suffix ambient register base r)

theorem loopTrace (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodyTraces : BodyTraces counter guardLabel bodyLabel program suffix
      ambient register base cost n) :
    (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
      (some (guardConfiguration counter guardLabel suffix ambient register base n)) =
      some (exitConfiguration counter exitLabel suffix ambient base) := by
  revert bodyTraces
  induction n with
  | zero =>
      intro _
      simpa only [totalSteps_zero, guardConfiguration, exitConfiguration] using
        guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
          (base 0) suffix (ambient 0) (register 0)
  | succ n ih =>
      intro bodyTraces
      rw [totalSteps_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n + cost n]
        (TM2.step program
          ⟨some guardLabel, (ambient (n + 1), register (n + 1)),
            counterTapes counter (base (n + 1)) (n + 1) suffix⟩) = _
      rw [guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
        (base (n + 1)) n suffix (ambient (n + 1)) (register (n + 1)),
        Function.iterate_add_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
        ((MachineComposition.advance (TM2.step program))^[cost n]
          (some (bodyConfiguration counter bodyLabel suffix ambient base n))) = _
      rw [bodyTraces n (Nat.lt_succ_self n)]
      exact ih (fun r hr => bodyTraces r (Nat.lt_trans hr (Nat.lt_succ_self n)))

end DFVSGames.Foundations.Complexity.MachineCountedLoop


namespace DFVSGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

theorem output_encodeWord_inline_MachineUnaryMultiply (a : ℕ) :
    Reduction.MachineTransducer.output transition payload () (encodeWord a) =
      List.replicate a true := by
  induction a with
  | zero => simp [encodeWord, Reduction.MachineTransducer.output, payload]
  | succ a ih =>
    simpa only [encodeWord, List.replicate_succ, List.cons_append,
      Reduction.MachineTransducer.output, payload, Bool.cond_true, transition,
      ite_true, if_true, List.singleton_append, List.nil_append] using congrArg (List.cons true) ih

theorem prepend_payload_inline_MachineUnaryMultiply (a p : ℕ) (suffix : List Bool) :
    List.replicate a true ++ (encodeWord p ++ suffix) = encodeWord (a + p) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

def loopBase (slots : Fin 5 ↪ K) (base : K → List Bool) (a b r : ℕ) : K → List Bool :=
  resultTapes slots base (a * (b - r))

end DFVSGames.Foundations.Complexity.MachineUnaryMultiply

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineUnaryAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

def value (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => radix * value radix digits n + digits n

def prefixSteps (radix : Nat) (digits : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSteps radix digits n + stepCost radix (value radix digits n) (digits n)

def stageTapes (slots : Layout width ↪ K) (base : K → List Bool) (n acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl (accumulator (parity n)))) (encodeWord acc)

structure Clean (slots : Layout width ↪ K) (base : K → List Bool) : Prop where
  accA : base (slots (.inl 1)) = []
  accB : base (slots (.inl 2)) = []
  counter : base (slots (.inl 4)) = []
  scratch : base (slots (.inl 5)) = []

omit [DecidableEq K] in
theorem Clean.acc {slots : Layout width ↪ K} {base : K → List Bool}
    (clean : Clean slots base) (flip : Bool) : base (slots (.inl (accumulator flip))) = [] := by
  cases flip
  · exact clean.accA
  · exact clean.accB

def steps (radix : Nat) (digits : Nat → Nat) (width : Nat) : Nat :=
  prefixSteps radix digits width + 2 * value radix digits width + 5

omit [DecidableEq K] in
theorem value_eq_foldl (radix : Nat) (digits : Nat → Nat) (n : Nat) :
    value radix digits n =
      ((List.range n).map digits).foldl (fun acc digit => radix * acc + digit) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [value, List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_singleton, List.foldl_cons, List.foldl_nil, ← ih]

omit [DecidableEq K] in

theorem value_add_one_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) : value radix digits n + 1 ≤ (magnitude + 1) ^ n := by
  induction n with
  | zero => simp [value]
  | succ n ih =>
    have hn' : n < width := by omega
    have hm := Nat.mul_le_mul_right (value radix digits n) radixBound
    calc
      value radix digits (n + 1) + 1 ≤ (magnitude + 1) * (value radix digits n + 1) := by
        rw [value]
        have hd := digitBound n hn'
        nlinarith
      _ ≤ (magnitude + 1) * (magnitude + 1) ^ n :=
        Nat.mul_le_mul_left _ (ih (by omega))
      _ = (magnitude + 1) ^ (n + 1) := by rw [pow_succ]; ac_rfl

omit [DecidableEq K] in
theorem value_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) : value radix digits n ≤ (magnitude + 1) ^ width := by
  have h := value_add_one_le radix digits width magnitude radixBound digitBound n hn
  exact (Nat.le_trans (Nat.le_add_right _ _) h).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) hn)

omit [DecidableEq K] in
theorem prefixSteps_le (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude)
    (n : Nat) (hn : n ≤ width) :
    prefixSteps radix digits n ≤ n * perDigitBound width magnitude := by
  induction n with
  | zero => simp [prefixSteps]
  | succ n ih =>
    have hn' : n < width := by omega
    have ha := value_le radix digits width magnitude radixBound digitBound n (by omega)
    have hc := stepCost_le radix (value radix digits n) (digits n) width magnitude
      radixBound ha (digitBound n hn')
    rw [prefixSteps]
    calc
      prefixSteps radix digits n + stepCost radix (value radix digits n) (digits n) ≤
          n * perDigitBound width magnitude + perDigitBound width magnitude :=
        Nat.add_le_add (ih (by omega)) hc
      _ = (n + 1) * perDigitBound width magnitude := by rw [Nat.add_mul, Nat.one_mul]

omit [DecidableEq K] in
@[simp] theorem timePolynomial_eval (width magnitude : Nat) :
    (timePolynomial width).eval magnitude =
      width * perDigitBound width magnitude + 2 * (magnitude + 1) ^ width + 5 := by
  simp [timePolynomial, perDigitBound]

omit [DecidableEq K] in
theorem steps_le_timePolynomial (radix : Nat) (digits : Nat → Nat) (width magnitude : Nat)
    (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    steps radix digits width ≤ (timePolynomial width).eval magnitude := by
  have hp := prefixSteps_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  have hv := value_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  rw [timePolynomial_eval]
  unfold steps
  omega

open scoped BigOperators

theorem resultTapes_other (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat)
    (k : K) (hk : k ≠ slots (.inl 3)) : resultTapes slots base acc k = base k := by
  simp [resultTapes, hk]

end DFVSGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductField
attribute [-instance] _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineProductField

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

def hornerRole : MachineHorner.Layout width → Layout width
  | .inl 0 => .inr 0
  | .inl 1 => .inr 1
  | .inl 2 => .inr 2
  | .inl 3 => .inr 5
  | .inl 4 => .inr 3
  | .inl 5 => .inr 4
  | .inr i => .inl (.inr (.inr i.rev))

theorem hornerRole_injective : Function.Injective (hornerRole (width := width)) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [hornerRole]
    | inr b => fin_cases a <;> simp [hornerRole] at h
  | inr a =>
    cases b with
    | inl b => fin_cases b <;> simp [hornerRole] at h
    | inr b => simpa [hornerRole] using h

def hornerSlots (slots : Layout width ↪ K) : MachineHorner.Layout width ↪ K :=
  Function.Embedding.trans ⟨hornerRole, hornerRole_injective⟩ slots

end DFVSGames.Explicit.MachineProductField


namespace DFVSGames.Explicit.MachineProductRow

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

def appendField (slots : Layout width ↪ K) (value : Nat) (base : K → List Bool) : K → List Bool :=
  Function.update base (outputTape slots) ((encodeWord value).reverse ++ base (outputTape slots))

def rowBits (values : Command width → Nat) (commands : List (Command width)) : List Bool :=
  commands.flatMap (fun command => encodeWord (values command))

def result (slots : Layout width ↪ K) (values : Command width → Nat)
    (command : Command width) (base : K → List Bool) : K → List Bool :=
  appendField slots (values command) base

theorem resultOf_eq (slots : Layout width ↪ K) (values : Command width → Nat)
    (commands : List (Command width)) (base : K → List Bool) :
    MachineFiniteSequence.resultOf (result slots values) commands base =
      Function.update base (outputTape slots)
        ((rowBits values commands).reverse ++ base (outputTape slots)) := by
  induction commands generalizing base with
  | nil => simp [MachineFiniteSequence.resultOf, rowBits]
  | cons command commands ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    simp [result, appendField, rowBits, List.reverse_append, List.append_assoc]

structure Ready (slots : Layout width ↪ K) (table : List Nat) (indices : Fin width → Nat)
    (radices : Bool → Nat) (base : K → List Bool) : Prop where
  work : ∀ useAlphabet, MachineProductField.Ready (fieldSlots slots useAlphabet) base
  tableWord : base (slots (.inl (.inl (.inl 0)))) = encodeWords table
  sourceWords : ∀ i, base (slots (.inl (.inl (.inr (.inl i))))) = encodeWord (indices i)
  radixWords : ∀ b, base (fieldSlots slots b (.inr 0)) = encodeWord (radices b)

theorem Ready.appendField (slots : Layout width ↪ K) (table : List Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat) (base : K → List Bool)
    (ready : Ready slots table indices radices base) (value : Nat) :
    Ready slots table indices radices (appendField slots value base) := by
  constructor
  · intro b
    have h := MachineProductField.Ready.output_update (fieldSlots slots b) base (ready.work b)
      ((encodeWord value).reverse ++ base (outputTape slots))
    exact h
  · rw [MachineProductRow.appendField, outputTape, Function.update_of_ne (slots.injective.ne (by simp))]
    exact ready.tableWord
  · intro i
    rw [MachineProductRow.appendField, outputTape, Function.update_of_ne (slots.injective.ne (by simp))]
    exact ready.sourceWords i
  · intro b
    rw [MachineProductRow.appendField, Function.update_of_ne]
    · exact ready.radixWords b
    · apply slots.injective.ne
      cases b <;> simp [fieldRole]

end DFVSGames.Explicit.MachineProductRow


namespace DFVSGames.Explicit.ProductMachineSemantics

open DFVSGames.Foundations
open Target
open Complexity
open MachineOutputContract

variable {n q t : ℕ}

theorem row_table_lookup (constraints : List (Constraint n q))
    (e : Fin constraints.length) (field : Fin (q + 2)) :
    (constraints.flatMap constraintWords)[(q + 2) * e.val + field.val]? =
      (constraintWords constraints[e])[field.val]? := by
  induction constraints with
  | nil => exact Fin.elim0 e
  | cons c constraints ih =>
    refine Fin.cases ?_ (fun i => ?_) e
    · simp [List.flatMap_cons, List.getElem?_append, constraintWords_length, field.isLt]
    · rw [List.flatMap_cons, List.getElem?_append]
      have hlarge : ¬ (q + 2) * i.succ.val + field.val < (constraintWords c).length := by
        simp only [Fin.val_succ, constraintWords_length, Nat.mul_succ]
        omega
      rw [ite_eq_right hlarge]
      have hindex : (q + 2) * i.succ.val + field.val - (constraintWords c).length =
          (q + 2) * i.val + field.val := by
        simp only [Fin.val_succ, constraintWords_length, Nat.mul_succ]
        omega
      rw [hindex]
      exact ih i

theorem inputTable_source (H : Instance q) (e : Fin H.constraints.length) :
    (inputTable H)[(q + 2) * e.val]? = some H.constraints[e].source.val := by
  have h := row_table_lookup H.constraints e (⟨0, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords] using h

theorem inputTable_target (H : Instance q) (e : Fin H.constraints.length) :
    (inputTable H)[(q + 2) * e.val + 1]? = some H.constraints[e].target.val := by
  have h := row_table_lookup H.constraints e (⟨1, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords] using h

theorem inputTable_image (H : Instance q) (e : Fin H.constraints.length) (a : Fin q) :
    (inputTable H)[(q + 2) * e.val + (2 + a.val)]? =
      some (H.constraints[e].permutation.images[a]).val := by
  have h := row_table_lookup H.constraints e (⟨2 + a.val, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords, tableWords, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

theorem horner_ofFin {radix : ℕ} (fields : Fin t → Fin radix) :
    MachineHorner.value radix (reverseDigits (fun i => (fields i : ℕ))) t =
      (finFunctionFinEquiv fields : ℕ) := by
  rw [MachineHorner.value_eq_foldl, reverseDigits_words,
    ← ProductTarget.address_eq_horner]

def fields (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (command : MachineProductRow.Command t) : Fin t → ℕ := fun j =>
  ((inputTable H)[(q + 2) * (edges j).val + command.2 j]?).getD 0

def fieldValue (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (command : MachineProductRow.Command t) : ℕ :=
  MachineHorner.value (if command.1 then q else H.vertices)
    (reverseDigits (fields H edges command)) t

theorem source_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fields H edges (sourceCommand t) = fun j => H.constraints[edges j].source.val := by
  funext j
  simp [fields, sourceCommand, inputTable_source]

theorem target_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fields H edges (targetCommand t) = fun j => H.constraints[edges j].target.val := by
  funext j
  simp [fields, targetCommand, inputTable_target]

theorem image_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (a : Fin (q ^ t)) :
    fields H edges (imageCommand q t a) = fun j =>
      (H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j]).val := by
  funext j
  unfold fields imageCommand
  rw [inputTable_image H (edges j) (finFunctionFinEquiv.symm a j)]
  rfl

theorem selected (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (c : MachineProductRow.Command t) (hc : c ∈ commands q t) (i : Fin t) :
    (inputTable H)[(q + 2) * (edges i).val + c.2 i]? =
      some (fields H edges c i) := by
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [fields, sourceCommand, inputTable_source]
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [fields, targetCommand, inputTable_target]
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  rw [image_fields]
  exact inputTable_image H (edges i) (finFunctionFinEquiv.symm a i)

theorem fields_lt (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (c : MachineProductRow.Command t) (hc : c ∈ commands q t) (i : Fin t) :
    fields H edges c i < if c.1 then q else H.vertices := by
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [source_fields]
    exact H.constraints[edges i].source.isLt
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [target_fields]
    exact H.constraints[edges i].target.isLt
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  rw [image_fields]
  exact (H.constraints[edges i].permutation.images[finFunctionFinEquiv.symm a i]).isLt

theorem source_value (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fieldValue H edges (sourceCommand t) =
      (finFunctionFinEquiv (fun j => H.constraints[edges j].source) : ℕ) := by
  unfold fieldValue
  rw [source_fields]
  exact horner_ofFin (fun j => H.constraints[edges j].source)

theorem target_value (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fieldValue H edges (targetCommand t) =
      (finFunctionFinEquiv (fun j => H.constraints[edges j].target) : ℕ) := by
  unfold fieldValue
  rw [target_fields]
  exact horner_ofFin (fun j => H.constraints[edges j].target)

theorem image_value (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (a : Fin (q ^ t)) :
    fieldValue H edges (imageCommand q t a) =
      (finFunctionFinEquiv (fun j =>
        H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j]) : ℕ) := by
  unfold fieldValue
  rw [image_fields]
  exact horner_ofFin (fun j =>
    H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j])

theorem encodeWords_map_inline_ProductMachineSemantics {X : Type*} (xs : List X) (f : X → ℕ) :
    encodeWords (xs.map f) = xs.flatMap (fun x => encodeWord (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih]

theorem rowBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) (i : Fin (H.constraints.length ^ t)) :
    MachineProductRow.rowBits (fieldValue H (finFunctionFinEquiv.symm i)) (commands q t) =
      encodeWords (constraintWords (ProductPaddedOutput.outputRow H presentation t ht i)) := by
  have hsource : fieldValue H (finFunctionFinEquiv.symm i) (sourceCommand t) =
      (ProductPaddedOutput.outputRow H presentation t ht i).source.val := source_value _ _
  have htarget : fieldValue H (finFunctionFinEquiv.symm i) (targetCommand t) =
      (ProductPaddedOutput.outputRow H presentation t ht i).target.val := target_value _ _
  have himage (a : Fin (q ^ t)) :
      fieldValue H (finFunctionFinEquiv.symm i) (imageCommand q t a) =
      ((ProductPaddedOutput.outputRow H presentation t ht i).permutation.images[a]).val := by
    rw [ProductPaddedOutput.outputRow_images]
    exact image_value _ _ _
  simp only [MachineProductRow.rowBits, commands, List.flatMap_cons, List.flatMap_map,
    hsource, htarget, himage, constraintWords, encodeWords_append, encodeWords,
    List.append_nil, List.append_assoc]
  congr 2
  have htable : tableWords (ProductPaddedOutput.outputRow H presentation t ht i).permutation =
      (List.finRange (q ^ t)).map
        (fun a => ((ProductPaddedOutput.outputRow H presentation t ht i).permutation.images[a]).val) := by
    apply List.ext_getElem
    · simp [tableWords]
    · intro j hj hk
      simp [tableWords, Fin.getElem_fin]
  rw [htable, encodeWords_map_inline_ProductMachineSemantics]

theorem encodeWords_flatMap_inline_ProductMachineSemantics {X : Type*} (xs : List X) (f : X → List ℕ) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords_append, ih]

def allRowsBits (H : Instance q) (t : ℕ) : List Bool :=
  (List.finRange (H.constraints.length ^ t)).flatMap (fun i =>
    MachineProductRow.rowBits (fieldValue H (finFunctionFinEquiv.symm i)) (commands q t))

theorem allRowsBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    allRowsBits H t = encodeWords
      ((ProductPaddedOutput.output H presentation t ht).constraints.flatMap constraintWords) := by
  change allRowsBits H t = encodeWords
    ((List.ofFn (ProductPaddedOutput.outputRow H presentation t ht)).flatMap constraintWords)
  unfold allRowsBits
  simp_rw [rowBits_eq H presentation t ht]
  have hrows : List.ofFn (ProductPaddedOutput.outputRow H presentation t ht) =
      (List.finRange (H.constraints.length ^ t)).map
        (ProductPaddedOutput.outputRow H presentation t ht) := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  rw [hrows, List.flatMap_map, encodeWords_flatMap_inline_ProductMachineSemantics]

theorem gameBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    encodeWords [H.vertices ^ t, q ^ t, H.constraints.length ^ t] ++ allRowsBits H t =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  rw [gameBits, ProductPaddedOutput.output_gameWords, encodeWords_append,
    allRowsBits_eq H presentation t ht, ProductPaddedOutput.output_constraints]
  rfl

end DFVSGames.Explicit.ProductMachineSemantics

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineProductPower

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {exponent : Nat}

theorem value_eq (radix exponent : Nat) : MachineHorner.value radix digits (exponent + 1) = radix ^ exponent := by
  induction exponent with
  | zero => simp [MachineHorner.value, digits]
  | succ exponent ih =>
    rw [MachineHorner.value, ih]
    simp [digits, pow_succ, Nat.mul_comm]

abbrev Label (exponent : Nat) := MachineHorner.Label (exponent + 1) ⊕ Unit

def steps (radix exponent : Nat) : Nat :=
  MachineHorner.steps radix digits (exponent + 1) + radix ^ exponent + 2

noncomputable def timePolynomial (exponent : Nat) : Polynomial Nat :=
  MachineHorner.timePolynomial (exponent + 1) +
    (Polynomial.X + 1) ^ exponent + 2

theorem steps_le (radix exponent magnitude : Nat) (bounded : radix ≤ magnitude)
    (positive : 1 ≤ magnitude) : steps radix exponent ≤ (timePolynomial exponent).eval magnitude := by
  have digitBound : ∀ i, i < exponent + 1 → digits i ≤ magnitude := by
    intro i hi; unfold digits; split <;> omega
  have h := MachineHorner.steps_le_timePolynomial radix digits (exponent + 1) magnitude bounded digitBound
  have hp : radix ^ exponent ≤ (magnitude + 1) ^ exponent :=
    Nat.pow_le_pow_left (by omega) _
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold steps
  omega

end DFVSGames.Explicit.MachineProductPower


namespace DFVSGames.Foundations.Complexity.MachineInitialHeaders

open Turing
open Reduction.MachineTransfer
open Reduction.MachineSubstitution
open MachineCopy

variable {K Λ σ : Type} [DecidableEq K]

theorem literalTrace (output : K) (word : List Bool) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabel : program label = pushWord output word (exitAt output exit))
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some label, (ambient, register), base⟩) =
      some ⟨exit, (ambient, register),
        Function.update base output (word.reverse ++ base output)⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some]
  change some (TM2.stepAux (program label) _ _) = _
  rw [atLabel, stepAux_pushWord]
  cases exit <;> rfl

end DFVSGames.Foundations.Complexity.MachineInitialHeaders


namespace DFVSGames.Explicit.MachineProductSeed

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer
open DFVSGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (commands : List (Command K)) := MachineFiniteSequence.Label LocalLabel commands

def entry (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel (fun _ => ()) commands labels exit

def localInstruction (command : Command K) (_ : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  pushWord command.1 command.2.reverse (exitAt command.1 exit)

def instruction (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ) :
    Label commands → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction LocalLabel (fun _ => ()) localInstruction commands labels exit

def finalTapes (commands : List (Command K)) (base : K → List Bool) : K → List Bool :=
  MachineFiniteSequence.resultOf result commands base

@[simp] theorem sequence_steps (commands : List (Command K)) (base : K → List Bool) :
    MachineFiniteSequence.steps result (fun _ _ => 1) commands base = commands.length := by
  induction commands generalizing base with
  | nil => rfl
  | cons command commands ih =>
    simp only [MachineFiniteSequence.steps, ih, List.length_cons]
    omega

theorem seedTrace (commands : List (Command K)) (labels : Label commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction commands labels exit l)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[commands.length]
      (some ⟨entry commands labels exit, (ambient, register), base⟩) =
      some ⟨exit, (ambient, register), finalTapes commands base⟩ := by
  have h := MachineFiniteSequence.trace LocalLabel (fun _ => ()) localInstruction
    result (fun _ _ => 1) program (fun _ => True) (fun _ => (ambient, register)) id commands
    (by intros; trivial)
    (by
      intro command hc localLabels localExit atLocal tapes ht
      have h := MachineInitialHeaders.literalTrace command.1 command.2.reverse
        (localLabels ()) localExit program (atLocal ()) tapes ambient register
      simpa only [List.reverse_reverse, id_eq, result] using h)
    labels exit atLabels base trivial
  simpa only [sequence_steps, entry, finalTapes, id_eq] using h

theorem finalTapes_frame (commands : List (Command K)) (base : K → List Bool)
    (k : K) (outside : ∀ command ∈ commands, k ≠ command.1) :
    finalTapes commands base k = base k := by
  induction commands generalizing base with
  | nil => rfl
  | cons command commands ih =>
    change finalTapes commands (result command base) k = base k
    rw [ih _ (fun c hc => outside c (by simp [hc]))]
    exact Function.update_of_ne (outside command (by simp)) _ _

theorem finalTapes_field (commands : List (Command K))
    (nodup : (commands.map Prod.fst).Nodup) (base : K → List Bool)
    (command : Command K) (member : command ∈ commands) :
    finalTapes commands base command.1 = command.2 ++ base command.1 := by
  induction commands generalizing base with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at nodup
    rcases List.mem_cons.mp member with rfl | member
    · change finalTapes rest (result command base) command.1 = _
      rw [finalTapes_frame rest _ command.1]
      · simp [result]
      · intro c hc he
        exact nodup.1 (List.mem_map.mpr ⟨c, hc, he.symm⟩)
    · have ne : command.1 ≠ first.1 := by
        intro h
        exact nodup.1 (List.mem_map.mpr ⟨command, member, h⟩)
      change finalTapes rest (result first base) command.1 = _
      rw [ih nodup.2 _ member, result, Function.update_of_ne ne]

end DFVSGames.Explicit.MachineProductSeed


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FieldArray
attribute [-instance] _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceFieldArray

open Turing
open DFVSGames.Foundations.Complexity SourceMachine

variable {K Λ σ : Type} [DecidableEq K]

def sequenceTapes (source : K) (destination : Nat → K) (base : K → List Bool)
    (offset : Nat) (values : List Nat) (suffix : List Bool) : K → List Bool :=
  match values with
  | [] => base
  | n :: rest => sequenceTapes source destination
      (afterField source (destination offset) base n (encodeWords rest ++ suffix))
      (offset + 1) rest suffix

theorem sequence_time_eq_length (values : List Nat) :
    values.sum + 2 * values.length + 1 = (encodeWords values).length + values.length + 1 := by
  rw [encodeWords_length]
  omega

theorem sequenceTapes_other (source : K) (destination : Nat → K)
    (p : K) (hpS : p ≠ source) (base : K → List Bool) (offset : Nat)
    (values : List Nat) (suffix : List Bool)
    (hpD : ∀ r, r < values.length → p ≠ destination (offset + r)) :
    sequenceTapes source destination base offset values suffix p = base p := by
  induction values generalizing base offset with
  | nil => rfl
  | cons n rest ih =>
    have hp0 : p ≠ destination offset := by simpa using hpD 0 (by simp)
    have htail : ∀ r, r < rest.length → p ≠ destination (offset + 1 + r) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpD (r + 1) (by simp; omega)
    rw [sequenceTapes, ih _ (offset + 1) htail]
    exact fieldTapes_other source (destination offset) p hpS hp0 _ _ _

theorem sequenceTapes_source (source : K) (destination : Nat → K)
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (hinput : base source = encodeWords values ++ suffix) :
    sequenceTapes source destination base offset values suffix source = suffix := by
  induction values generalizing base offset with
  | nil => simpa [sequenceTapes, encodeWords] using hinput
  | cons n rest ih =>
    have hsep0 : source ≠ destination offset := by simpa using hsep 0 (by simp)
    have htail : ∀ r, r < rest.length → source ≠ destination (offset + 1 + r) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsep (r + 1) (by simp; omega)
    apply ih _ (offset + 1) htail
    simp [afterField, hsep0]

theorem sequenceTapes_selected (source : K) (destination : Nat → K)
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (j : Nat) (hj : j < values.length)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (hdist : ∀ r s, r < values.length → s < values.length →
      destination (offset + r) = destination (offset + s) → r = s) :
    sequenceTapes source destination base offset values suffix (destination (offset + j)) =
      encodeWord (values[j]'hj) ++ base (destination (offset + j)) := by
  induction values generalizing base offset j with
  | nil => simp at hj
  | cons n rest ih =>
    have hsep0 : source ≠ destination offset := by simpa using hsep 0 (by simp)
    let nextBase := afterField source (destination offset) base n (encodeWords rest ++ suffix)
    cases j with
    | zero =>
      have hframe : ∀ r, r < rest.length → destination offset ≠ destination (offset + 1 + r) := by
        intro r hr heq
        have hh := hdist 0 (r + 1) (by simp) (by simp; omega)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)
        omega
      simp only [sequenceTapes, Nat.add_zero, List.getElem_cons_zero]
      rw [sequenceTapes_other source destination (destination offset) hsep0.symm _
        (offset + 1) rest suffix hframe]
      simp [afterField]
    | succ j =>
      have hj' : j < rest.length := by simpa using hj
      have hsep' : ∀ r, r < rest.length → source ≠ destination (offset + 1 + r) := by
        intro r hr
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsep (r + 1) (by simp; omega)
      have hdist' : ∀ r s, r < rest.length → s < rest.length →
          destination (offset + 1 + r) = destination (offset + 1 + s) → r = s := by
        intro r s hr hs heq
        have hh := hdist (r + 1) (s + 1) (by simp; omega) (by simp; omega)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)
        omega
      have hsrc : destination (offset + 1 + j) ≠ source := (hsep' j hj').symm
      have hdst : destination (offset + 1 + j) ≠ destination offset := by
        intro heq
        have hh := hdist (j + 1) 0 hj (by simp)
          (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq)
        omega
      have hkeep : nextBase (destination (offset + 1 + j)) = base (destination (offset + 1 + j)) :=
        fieldTapes_other source (destination offset) _ hsrc hdst _ _ _
      simp only [sequenceTapes, List.getElem_cons_succ]
      rw [show offset + (j + 1) = offset + 1 + j by omega]
      rw [ih _ (offset + 1) j hj' hsep' hdist']
      exact congrArg (encodeWord rest[j] ++ ·) hkeep

def loopLabel (q j : Nat) : Fin (q + 1) × Bool := (boundedIndex q j, true)

end DFVSGames.Foundations.Hastad.SourceFieldArray


namespace DFVSGames.Foundations.Hastad.SourceClauseLookup

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition SourceMachine

section Discard

variable {K Λ σ : Type} [DecidableEq K]

theorem discardFieldsTrace (source : K) (label : Nat → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (atLoop : ∀ r, r < values.length → program (label (offset + r)) =
      MachineLookup.discard source (label (offset + r)) (label (offset + r + 1)))
    (hinput : base source = encodeWords values ++ suffix) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (label offset), (ambient, none), base⟩) =
      some ⟨some (label (offset + values.length)), (ambient, none),
        Function.update base source suffix⟩ := by
  induction values generalizing base offset with
  | nil =>
    have hbase : Function.update base source suffix = base := by
      have hs : base source = suffix := by simpa only [encodeWords, List.nil_append] using hinput
      funext p
      by_cases hp : p = source
      · subst p; simp [hs]
      · simp [hp]
    simp only [encodeWords, List.length_nil, Nat.add_zero, Function.iterate_zero_apply, hbase]
  | cons n rest ih =>
    have hs : program (label offset) =
        MachineLookup.discard source (label offset) (label (offset + 1)) := by
      simpa only [Nat.add_zero] using atLoop 0 (by simp)
    have hin : base source = encodeWord n ++ (encodeWords rest ++ suffix) := by
      simpa only [encodeWords, List.append_assoc] using hinput
    have first := MachineLookup.discardTrace source (label offset) (label (offset + 1))
      program hs base n (encodeWords rest ++ suffix) hin ambient none
    have htail : ∀ r, r < rest.length → program (label (offset + 1 + r)) =
        MachineLookup.discard source (label (offset + 1 + r))
          (label (offset + 1 + r + 1)) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        atLoop (r + 1) (by simp; omega)
    have second := ih (Function.update base source (encodeWords rest ++ suffix))
      (offset + 1) htail (by simp)
    rw [show (encodeWords (n :: rest)).length = (encodeWords rest).length + (n + 1) by
      simp only [encodeWords, List.length_append, encodeWord_length]
      omega]
    rw [Function.iterate_add_apply, first]
    simpa [Function.update_idem, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

end Discard

end DFVSGames.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_Tape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.SourceEncoding

open DFVSGames.Foundations.Complexity

theorem equationBits_length_le {n : Nat} (e : CloneGap.Equation (Fin n)) :
    (encodeWords (equationWords e)).length ≤ 3 * n + 2 := by
  have hfirst := e.first.isLt
  have hsecond := e.second.isLt
  have hthird := e.third.isLt
  cases hrhs : e.rhs <;> simp [equationWords, hrhs] <;> omega

theorem equationsBits_length_le {n : Nat} (equations : List (CloneGap.Equation (Fin n))) :
    (encodeWords (equations.flatMap equationWords)).length ≤
      equations.length * (3 * n + 2) := by
  induction equations with
  | nil => simp [encodeWords]
  | cons e equations ih =>
      have he := equationBits_length_le e
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end DFVSGames.Reduction.SourceEncoding

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_TestEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineTupleOdometer

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

theorem update_current_inline_MachineTupleOdometer (current remaining : K) (distinct : current ≠ remaining)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt current remaining base input output) current replacement =
      tapesAt current remaining base replacement output := by
  funext k
  by_cases hc : k = current
  · subst k; simp [tapesAt, distinct]
  · by_cases hr : k = remaining
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hc, hr]

theorem update_remaining_inline_MachineTupleOdometer (current remaining : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt current remaining base input output) remaining replacement =
      tapesAt current remaining base input replacement := by
  simp [tapesAt]

section AscendingCycle

open scoped BigOperators

def bodyConfiguration (current remaining : K) (bodyLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (remainder + 1), none),
    digitTapes current remaining (base (remainder + 1)) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def checkConfiguration (current remaining : K) (checkLabel : Λ)
    (maximum remainder : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some checkLabel, (ambient remainder, register remainder),
    digitTapes current remaining (base remainder) (maximum - remainder)
      remainder currentSuffix remainingSuffix⟩

def cycleExit (current remaining : K) (exitLabel : Λ)
    (maximum : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (base : ℕ → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none),
    digitTapes current remaining (base 0) 0 maximum currentSuffix remainingSuffix⟩

def VisitTraces (current remaining : K) (bodyLabel checkLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (maximum count : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) : Prop :=
  ∀ r, r ≤ count → (MachineComposition.advance (TM2.step program))^[cost r]
    (some (bodyConfiguration current remaining bodyLabel maximum r
      currentSuffix remainingSuffix ambient base)) =
    some (checkConfiguration current remaining checkLabel maximum r
      currentSuffix remainingSuffix ambient register base)

end AscendingCycle


open scoped BigOperators

end DFVSGames.Foundations.Complexity.MachineTupleOdometer

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_TupleOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceOdometerSchedule

open Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def currentAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .current ⟨i, h⟩ else .extra accumulator

def remainingAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .remaining ⟨i, h⟩ else .extra accumulator

theorem setDigits_setAcc (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc a base bits) = setAcc a (setDigits m digits base) bits := by
  funext k
  cases k <;> simp [setDigits, setAcc, Function.update_apply]

theorem putDigit_setAcc (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) (bits : List Bool) :
    putDigit i (setAcc a base bits) d r = setAcc a (putDigit i base d r) bits := by
  funext k
  cases k <;> simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
    setAcc, Function.update_apply]

theorem setDigits_putDigit (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (d r : ℕ) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d r := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | remaining i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem setDigits_snoc (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m (Fin.snoc digits d) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d (m - 1 - d) := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | remaining i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem setDigits_snoc_base (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d (m - 1 - d)) =
      setDigits m (Fin.snoc digits d) base := by
  rw [setDigits_putDigit, setDigits_snoc]

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

def blocks {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) (d : ℕ) : List Bool :=
  if h : d < m then allBits (fun c => bits (Fin.snoc c ⟨d, h⟩)) else []

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ) (accumulator : Extra)
    {q : ℕ} (base : Tape u Extra → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc accumulator base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc accumulator base ((bits c).reverse ++ output))))

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (d : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c d i).val) =
      Fin.snoc (fun i => (c i).val) d.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

end DFVSGames.Foundations.Hastad.SourceOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductProgram
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

abbrev State := MachineHorner.State Unit

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

noncomputable section

def headerDestination (t : Nat) : Fin 3 → Tape t
  | 0 => auxiliary t 0
  | 1 => auxiliary t 7
  | 2 => auxiliary t 8

end

end DFVSGames.Explicit.MachineProductProgram


namespace DFVSGames.Explicit.MachineProductHeaders

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

def headerBits {q : Nat} (H : Instance q) (t : Nat) : List Bool :=
  encodeWords [H.vertices ^ t, q ^ t, H.constraints.length ^ t]

def baseTapes {q : Nat} (H : Instance q) (t : Nat) : Tape t → List Bool :=
  frame H t (headerBits H t)

theorem power_outside (t : Nat) (edgeCount : Bool) (i : MachineHorner.Layout (t + 1)) :
    accumulator t ≠ powerSlots t edgeCount i := by
  cases i with
  | inl i => fin_cases i <;> cases edgeCount <;> simp [accumulator, powerSlots, powerRole, auxiliary]
  | inr i => simp [accumulator, powerSlots, powerRole, auxiliary, constantDigit]

theorem frame_power_clean {q : Nat} (H : Instance q) (t : Nat) (emitted : List Bool)
    (edgeCount : Bool) : MachineHorner.Clean (powerSlots t edgeCount) (frame H t emitted) := by
  constructor <;> simp [frame, powerSlots, powerRole, auxiliary]

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

end DFVSGames.Explicit.MachineProductHeaders


namespace DFVSGames.Explicit.MachineProductHeadersRead

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
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

theorem headers_budget {q : Nat} (H : Target.Instance q) (_t : Nat) :
    H.vertices + q + H.constraints.length + 6 ≤ (gameBits H).length + 3 := by
  simp [gameBits, gameWords, List.length_append, encodeWords]
  omega

end
end DFVSGames.Explicit.MachineProductHeadersRead


namespace DFVSGames.Explicit.MachineProductHeaders

open Turing
open DFVSGames.Foundations Target Complexity Hastad
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

end
end DFVSGames.Explicit.MachineProductHeaders


namespace DFVSGames.Explicit.MachineProductHeaders

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

noncomputable section

def steps {q : Nat} (H : Instance q) (t : Nat) : Nat :=
  H.vertices + q + H.constraints.length + 6 + (t + 2) +
    (MachineProductPower.steps H.vertices t + 1 + MachineProductPower.steps H.constraints.length t) +
    (t * (2 * H.constraints.length + 6) + 1)

def timePolynomial (t : Nat) : Polynomial Nat :=
  Polynomial.X + 3 + Polynomial.C (t + 2) +
    Polynomial.C 2 * (MachineProductPower.timePolynomial t).comp (Polynomial.X + 1) + 1 +
    Polynomial.C t * (Polynomial.C 2 * Polynomial.X + 6) + 1

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

end
end DFVSGames.Explicit.MachineProductHeaders


namespace DFVSGames.Explicit.MachineProductBounds

open DFVSGames.Foundations.Complexity

variable {K : Type} [DecidableEq K] {width : Nat}

noncomputable def fieldPolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C width * (7 * Polynomial.X + 6) + 1 +
    MachineHorner.timePolynomial width + (Polynomial.X + 1) ^ width + 2 +
    Polynomial.C (width + 2) * (Polynomial.C width * (Polynomial.X + 1) + 1)

@[simp] theorem fieldPolynomial_eval (width magnitude : Nat) :
    (fieldPolynomial width).eval magnitude =
      width * (7 * magnitude + 6) + 1 + (MachineHorner.timePolynomial width).eval magnitude +
        (magnitude + 1) ^ width + 2 + (width + 2) * (width * (magnitude + 1) + 1) := by
  simp [fieldPolynomial]

end DFVSGames.Explicit.MachineProductBounds


namespace DFVSGames.Explicit.MachineProductLoop

open Turing
open DFVSGames.Foundations
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

end

end DFVSGames.Explicit.MachineProductLoop

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductFinish
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
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

theorem base_ready (H : Target.Instance q) (t : Nat) :
    MachineProductLoop.BaseReady H (MachineProductHeaders.baseTapes H t) := by
  constructor
  · intro bit
    exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rfl
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]
  · simp [MachineProductHeaders.baseTapes, MachineProductHeaders.frame, auxiliary]

theorem allRows_eq (H : Target.Instance q) (t : Nat) :
    (MachineTupleOdometer.tupleOrder H.constraints.length t).flatMap (MachineProductLoop.rowBits (t := t) H) =
      ProductMachineSemantics.allRowsBits H t := by
  simp only [MachineTupleOdometer.tupleOrder, ProductMachineSemantics.allRowsBits,
    List.ofFn_eq_map, List.flatMap_map, MachineProductLoop.rowBits]

end

end DFVSGames.Explicit.MachineProductFinish


namespace DFVSGames.Explicit.MachineProductRuntime

open Turing
open DFVSGames.Foundations Target Complexity Hastad
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

abbrev Input (q : Nat) := Σ H : Instance q, MachineOutputContract.SimpleBipartite H

def construct {q : Nat} (t : Nat) (ht : 0 < t) (H : Input q) : Instance (q ^ t) :=
  ProductPaddedOutput.output H.1 H.2 t ht

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

end

end DFVSGames.Explicit.MachineProductRuntime


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

theorem paddedAmplitude_row [DecidableEq V] (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v ≤ 1) (v : V) :
    rowSquareMass (paddedAmplitude f) v = 1 := by
  have hs : Real.sqrt (1 - rowSquareMass f v) ^ 2 = 1 - rowSquareMass f v :=
    Real.sq_sqrt (sub_nonneg.mpr (hrow v))
  simp only [rowSquareMass] at hs
  simp only [rowSquareMass, Fintype.sum_sum_type, paddedAmplitude]
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ v), hs]
  ring

end
end DFVSGames.Repetition


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

omit [Fintype V] in
theorem pairQuadraticMass_eq_one (ν : FiniteDistribution E) (left right : E → V)
    (f : V → Ω → ℝ) (hrow : ∀ v, rowSquareMass f v = 1) :
    Analytic.quadraticMass (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2) = 1 := by
  unfold Analytic.quadraticMass
  rw [Fintype.sum_prod_type]
  have he (e : E) :
      (∑ ω, ν.weight e * ((f (left e) ω) ^ 2 + (f (right e) ω) ^ 2) / 2) =
        ν.weight e := by
    calc
      _ = ν.weight e *
          ((∑ ω, (f (left e) ω) ^ 2) + (∑ ω, (f (right e) ω) ^ 2)) / 2 := by
        simp only [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.sum_mul]
      _ = ν.weight e := by
        change ν.weight e * (rowSquareMass f (left e) + rowSquareMass f (right e)) / 2 = _
        rw [hrow, hrow]
        ring
  simp_rw [he]
  exact ν.normalized

end
end DFVSGames.Repetition


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_TraceLaw
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.CorrelatedSampling


noncomputable section


variable {α : Type*} [Fintype α]

def rectangleDistribution [Nonempty α] (thresholds : List ℝ) :
    Games.FiniteDistribution (RectangleSeed thresholds α) where
  weight := rectangleWeight thresholds
  nonnegative := rectangleWeight_nonnegative thresholds
  normalized := rectangleWeight_normalized thresholds

end


open scoped BigOperators

end DFVSGames.Foundations.CorrelatedSampling


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SharedSampling
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

def traceSeedLaw {σ : Type*} [Fintype σ] (μ : FiniteDistribution σ) :
    (n : Nat) → FiniteDistribution (TraceSeed σ n)
  | 0 => { weight := fun _ => 1, nonnegative := by intro; norm_num,
           normalized := by simp }
  | n + 1 => μ.product (traceSeedLaw μ n)


open CorrelatedSampling


end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Repetition

open DFVSGames.Foundations.Games
open DFVSGames.Foundations.CorrelatedSampling
open DFVSGames.Foundations.Repetition
open scoped BigOperators

noncomputable section

variable {V S A : Type*} [Fintype V] [Fintype S] [Fintype A]

def partialPairMass (μ : FiniteDistribution S) (accept : V → S → Bool)
    (label : V → S → A) (R : V → V → A → A → Bool) (x y : V) : ℝ :=
  μ.probability (fun s => accept x s && accept y s && R x y (label x s) (label y s))

def partialEdgeMass {E : Type*} (μ : FiniteDistribution S) (accept : V → S → Bool)
    (label : V → S → A) (left right : E → V) (R : E → A → A → Bool) (e : E) : ℝ :=
  μ.probability (fun s => accept (left e) s && accept (right e) s &&
    R e (label (left e) s) (label (right e) s))

def partialLabelScore {E : Type*} [Fintype E] (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool) (f : V → A) : ℝ :=
  ν.probability (fun e => R e (f (left e)) (f (right e)))

omit [Fintype V] [Fintype A] in
theorem partial_mass_bounds_inline_RoundingSampling (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (density : ℝ)
    (hdensity : ∀ v, μ.probability (accept v) = density) (x y : V) :
    0 ≤ partialPairMass μ accept label R x y ∧
    partialPairMass μ accept label R x y ≤ density ∧
    density ≤ μ.probability (fun s => accept x s || accept y s) ∧
    μ.probability (fun s => accept x s || accept y s) +
      partialPairMass μ accept label R x y ≤ 2 * density := by
  refine ⟨μ.probability_nonnegative _, ?_, ?_, ?_⟩
  · rw [← hdensity x]
    apply μ.probability_mono
    intro s hs
    have hp : (accept x s = true ∧ accept y s = true) ∧
        R x y (label x s) (label y s) = true := by simpa using hs
    exact hp.1.1
  · rw [← hdensity x]
    exact μ.probability_mono (fun s hs => by simp [hs])
  · calc
      _ ≤ μ.probability (accept x) + μ.probability (accept y) := by
        unfold partialPairMass FiniteDistribution.probability
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro s _
        cases hx : accept x s <;> cases hy : accept y s <;>
          cases hr : R x y (label x s) (label y s) <;>
          simp [hx, hy, hr] ; linarith [μ.nonnegative s]
      _ = 2 * density := by rw [hdensity x, hdensity y]; ring

omit [Fintype V] [Fintype A] in

theorem partialSample_pair_lower (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (fallback : A) (density : ℝ)
    (hdensity₀ : 0 < density) (hdensity : ∀ v, μ.probability (accept v) = density)
    (x y : V) (n : Nat) :
    2 * (partialPairMass μ accept label R x y / density) - 1 - (1 - density) ^ n ≤
      traceAverage μ.weight n (fun proposals =>
        if R x y (partialSample accept label fallback proposals x)
          (partialSample accept label fallback proposals y) then 1 else 0) := by
  classical
  let union : S → Bool := fun s => accept x s || accept y s
  let good : S → Bool := fun s =>
    accept x s && accept y s && R x y (label x s) (label y s)
  obtain ⟨hg, hgl, hlu, hug⟩ := partial_mass_bounds_inline_RoundingSampling μ accept label R density hdensity x y
  have hu : 0 < eventMass μ.weight union := lt_of_lt_of_le hdensity₀ hlu
  have hm : eventMass μ.weight (fun s => union s && good s) =
      partialPairMass μ accept label R x y := by
    unfold eventMass partialPairMass FiniteDistribution.probability
    apply Finset.sum_congr rfl
    intro s _
    cases hx : accept x s <;> cases hy : accept y s <;> simp [union, good, hx, hy]
  have hfirst := goodFirstMass_lower_bound μ.weight union good
    μ.nonnegative μ.normalized hu n
  rw [hm] at hfirst
  have hactual := traceAverage_mono μ.weight μ.nonnegative n _ _
    (first_good_relation_le_inline_RoundingSampling accept label R fallback x y)
  rw [goodFirstIndicator_law μ.weight _ _ μ.normalized n] at hactual
  have hcompl := eventMass_complement μ.weight union μ.normalized
  have hre : eventMass μ.weight (fun s => !(union s)) ≤ 1 - density := by
    change density ≤ eventMass μ.weight union at hlu
    linarith
  have hp := pow_le_pow_left₀
    (eventMass_nonneg μ.weight (fun s => !(union s)) μ.nonnegative) hre n
  have hr := partial_ratio_bound_inline_RoundingSampling hdensity₀ hg hgl hlu hug
  change 2 * (partialPairMass μ accept label R x y / density) - 1 ≤
    partialPairMass μ accept label R x y / eventMass μ.weight union at hr
  change goodFirstMass μ.weight union good n ≤ _ at hactual
  linarith

end
end DFVSGames.Repetition


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations Games CorrelatedSampling

noncomputable section

variable {V Ω A : Type*} [Fintype V] [Fintype Ω]

def thresholdDistribution [Nonempty Ω] (f : V → Ω → ℝ) :
    FiniteDistribution (ThresholdSeed f) := rectangleDistribution (thresholdLevels f)

theorem threshold_acceptance_mass [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (x : V) :
    (thresholdDistribution f).probability (thresholdAccept f x) = thresholdRate Ω := by
  change eventMass (rectangleWeight (thresholdLevels f))
    (rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2)) = _
  rw [rectangle_acceptance_mass (thresholdLevels f) _
    (square_mem_thresholdLevels f x) (fun ω => sq_nonneg (f x ω))
    (square_le_one_of_row_norm f hnorm x), hnorm x]
  rfl

theorem threshold_good_pair_mass [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (a : V → Ω → A)
    (x y : V) (R : A → A → Prop) [DecidableRel R] :
    (thresholdDistribution f).probability (fun seed =>
      (thresholdAccept f x seed && thresholdAccept f y seed) &&
        decide (R (thresholdLabel f a x seed) (thresholdLabel f a y seed))) =
      thresholdRate Ω * ∑ ω,
        if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0 := by
  classical
  change (∑ seed : RectangleSeed (thresholdLevels f) Ω,
    if (rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2) seed &&
        rectangleAccept (thresholdLevels f) (fun ω => f y ω ^ 2) seed) &&
        decide (R (a x seed.1) (a y seed.1)) then
      rectangleWeight (thresholdLevels f) seed else 0) = _
  have hand := congrFun (rectangle_and (thresholdLevels f)
    (fun ω => f x ω ^ 2) (fun ω => f y ω ^ 2))
  simp_rw [hand]
  rw [Fintype.sum_prod_type]
  have hrow (ω : Ω) :
      (∑ i : Fin (thresholdPartition (thresholdLevels f)).length,
        if rectangleAccept (thresholdLevels f)
            (fun t => min (f x t ^ 2) (f y t ^ 2)) (ω, i) &&
            decide (R (a x ω) (a y ω)) then
          rectangleWeight (thresholdLevels f) (ω, i) else 0) =
        (if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0) /
          (Fintype.card Ω : ℝ) := by
    by_cases hR : R (a x ω) (a y ω)
    · simpa only [hR, decide_true, Bool.and_true, ite_true, if_true] using
        rectangle_row_mass (thresholdLevels f)
          (fun t => min (f x t ^ 2) (f y t ^ 2)) ω
          (min_mem_thresholds _ (square_mem_thresholdLevels f x ω)
            (square_mem_thresholdLevels f y ω))
          (le_min (sq_nonneg _) (sq_nonneg _))
          ((min_le_left _ _).trans (square_le_one_of_row_norm f hnorm x ω))
    · simp [hR]
  simp_rw [hrow]
  simp only [thresholdRate, div_eq_mul_inv, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact mul_comm _ _

theorem threshold_good_pair_mass_bool [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (a : V → Ω → A)
    (x y : V) (R : A → A → Bool) :
    (thresholdDistribution f).probability (fun seed =>
      (thresholdAccept f x seed && thresholdAccept f y seed) &&
        R (thresholdLabel f a x seed) (thresholdLabel f a y seed)) =
      thresholdRate Ω * ∑ ω,
        if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0 := by
  simpa only [Bool.decide_eq_true] using
    threshold_good_pair_mass f hnorm a x y (fun b c => R b c = true)

end

end DFVSGames.Repetition


namespace DFVSGames.Repetition

open scoped BigOperators
open DFVSGames.Foundations.Games

noncomputable section

variable {V A T : Type*} [Fintype V] [Fintype A] [Fintype T]

def rowLaw [Nonempty A] (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (v : V) : FiniteDistribution A := by
  classical
  exact if hz : rowMass h v = 0 then
    { weight := fun a => if a = Classical.choice (inferInstance : Nonempty A) then 1 else 0
      nonnegative := fun a => by split <;> norm_num
      normalized := by simp }
  else
    { weight := fun a => h v a / rowMass h v
      nonnegative := fun a => div_nonneg (hh v a) (rowMass_nonnegative h hh v)
      normalized := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        exact mul_inv_cancel₀ hz }

end

end DFVSGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Collision
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition
open DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

def energy (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Q₁ → A₁ → ℝ) : ℝ :=
  ∑ y, K.outer.weight y * ∑ b, K.apply f y b ^ 2

def assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) : ℝ := K.energy (assignment labels)

def collisionValue [Nonempty A₁] (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty K.assignmentEnergy

def vectorEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) : ℝ := ∑ ω, K.energy (f ω)

theorem energy_nonneg (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) : 0 ≤ K.energy f := by
  exact Finset.sum_nonneg fun y _ => mul_nonneg (K.outer.nonnegative y)
    (Finset.sum_nonneg fun b _ => sq_nonneg _)

theorem assignmentEnergy_le_collisionValue [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    K.assignmentEnergy labels ≤ K.collisionValue := by
  classical
  exact Finset.le_sup' _ (Finset.mem_univ labels)

theorem collisionValue_le_iff [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    K.collisionValue ≤ bound ↔ ∀ labels, K.assignmentEnergy labels ≤ bound := by
  classical
  simp [collisionValue, Finset.sup'_le_iff]

theorem exists_optimal_assignment [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    ∃ labels, K.assignmentEnergy labels = K.collisionValue := by
  classical
  obtain ⟨labels, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Q₁ → A₁))) Finset.univ_nonempty K.assignmentEnergy
  exact ⟨labels, h.symm⟩

theorem collisionValue_nonneg [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : 0 ≤ K.collisionValue := by
  obtain ⟨labels, h⟩ := K.exists_optimal_assignment
  rw [← h]
  exact K.energy_nonneg _

end ProjectionKernel
end
end DFVSGames.Repetition


namespace DFVSGames.Repetition.ProjectionKernel

open Foundations.Games
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

def symmetricDistribution (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    FiniteDistribution (SymmetricEdge Q₁ Q₂) where
  weight e := K.outer.weight e.1 * (K.inner e.1).weight e.2.1 *
    (K.inner e.1).weight e.2.2
  nonnegative e := mul_nonneg
    (mul_nonneg (K.outer.nonnegative _) ((K.inner _).nonnegative _))
    ((K.inner _).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ y, K.outer.weight y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Fintype.sum_prod_type]
        calc
          _ = ∑ x, K.outer.weight y * (K.inner y).weight x := by
            apply Finset.sum_congr rfl
            intro x _
            dsimp only
            rw [← Finset.mul_sum, (K.inner y).normalized, mul_one]
          _ = K.outer.weight y := by
            rw [← Finset.mul_sum, (K.inner y).normalized, mul_one]
      _ = 1 := K.outer.normalized

def symmetricAccept (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (e : SymmetricEdge Q₁ Q₂) (a a' : A₁) : Bool := by
  classical
  exact decide (∃ b, K.accepts e.2.1 e.1 a b = true ∧
    K.accepts e.2.2 e.1 a' b = true)

theorem sum_projection_gates (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (y : Q₂) (x x' : Q₁) (a a' : A₁) (r s : ℝ) :
    (∑ b, (if K.accepts x y a b then r else 0) *
      (if K.accepts x' y a' b then s else 0)) =
        if K.symmetricAccept (y, x, x') a a' then r * s else 0 := by
  classical
  by_cases hex : ∃ b, K.accepts x y a b = true ∧ K.accepts x' y a' b = true
  · obtain ⟨b₀, hb₀, hb₀'⟩ := hex
    have hex' : ∃ b, K.accepts x y a b = true ∧ K.accepts x' y a' b = true :=
      ⟨b₀, hb₀, hb₀'⟩
    simp only [symmetricAccept, hex', decide_true, ite_true, if_true]
    calc
      _ = (if K.accepts x y a b₀ then r else 0) *
          (if K.accepts x' y a' b₀ then s else 0) := by
        apply Finset.sum_eq_single b₀
        · intro b _ hne
          have hb : K.accepts x y a b ≠ true := by
            intro hb
            exact hne (K.projection x y a b b₀ hb hb₀)
          simp [hb]
        · simp
      _ = r * s := by simp [hb₀, hb₀']
  · simp only [symmetricAccept, hex, decide_false, Bool.false_eq_true, ite_false]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : K.accepts x y a b = true
    · have hb' : K.accepts x' y a' b ≠ true := fun hb' => hex ⟨b, hb, hb'⟩
      simp [hb']
    · simp [hb]

theorem apply_single_label (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (f : Q₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => if labels x = a then f x else 0) y b =
      ∑ x, (K.inner y).weight x * (if K.accepts x y (labels x) b then f x else 0) := by
  classical
  unfold apply
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  calc
    _ = ∑ a, if labels x = a then
        (if K.accepts x y (labels x) b then f x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : labels x = a
      · subst a
        simp
      · simp [ha]
    _ = _ := by simp

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition.ProjectionKernel

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

def linearCoefficient (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (t : Q₂ × A₂) (x : Q₁) (a : A₁) : ℝ :=
  (K.inner t.1).weight x * (if K.accepts x t.1 a t.2 then 1 else 0)

theorem apply_eq_linearCoefficient_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply h y b = ∑ x, ∑ a, K.linearCoefficient (y, b) x a * h x a := by
  unfold apply
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : K.accepts x y a b = true <;> simp [linearCoefficient, ha]

theorem energy_eq_linearCoefficient_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Q₁ → A₁ → ℝ) :
    K.energy h = ∑ t : Q₂ × A₂, K.outer.weight t.1 *
      (∑ x, ∑ a, K.linearCoefficient t x a * h x a) ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← K.apply_eq_linearCoefficient_sum, ← Finset.mul_sum]
  rfl

end

end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition
open DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

theorem apply_assignment_nonneg (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) (b : A₂) :
    0 ≤ K.apply (assignment labels) y b := by
  rw [apply_assignment]
  exact (K.inner y).probability_nonnegative (fun x => K.accepts x y (labels x) b)

theorem sum_apply_assignment_le_one (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) :
    (∑ b, K.apply (assignment labels) y b) ≤ 1 := by
  classical
  simp only [apply_assignment]
  rw [Finset.sum_comm, ← (K.inner y).normalized]
  apply Finset.sum_le_sum
  intro x _
  by_cases hex : ∃ b, K.accepts x y (labels x) b = true
  · obtain ⟨b₀, hb₀⟩ := hex
    have hiff : ∀ b, K.accepts x y (labels x) b = true ↔ b = b₀ := by
      intro b
      constructor
      · intro hb
        exact K.projection x y (labels x) b b₀ hb hb₀
      · rintro rfl
        exact hb₀
    simp only [hiff]
    simp
  · have hnone : ∀ b, K.accepts x y (labels x) b ≠ true := by
      intro b hb
      exact hex ⟨b, hb⟩
    simpa [hnone] using (K.inner y).nonnegative x

theorem exists_best_response [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    ∃ answers : Q₂ → A₂, ∀ y b,
      K.apply (assignment labels) y b ≤ K.apply (assignment labels) y (answers y) := by
  classical
  have h : ∀ y, ∃ b : A₂, ∀ b',
      K.apply (assignment labels) y b' ≤ K.apply (assignment labels) y b := by
    intro y
    obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset A₂)) Finset.univ_nonempty
      (fun b => K.apply (assignment labels) y b)
    refine ⟨b, fun b' => ?_⟩
    rw [← hb]
    exact Finset.le_sup' _ (Finset.mem_univ b')
  exact ⟨fun y => Classical.choose (h y), fun y b => Classical.choose_spec (h y) b⟩

end ProjectionKernel
end
end DFVSGames.Repetition


namespace DFVSGames.Repetition.ProjectionKernel

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

theorem distribution_nonempty_inline_RoundingKernel {T : Type*} [Fintype T]
    (μ : FiniteDistribution T) : Nonempty T := by
  by_contra h
  have : IsEmpty T := not_nonempty_iff.mp h
  have hz : (∑ t, μ.weight t) = 0 := by simp
  linarith [μ.normalized]

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition
open DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ I : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype I]

def coefficients (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (y : Q₂) (b : A₂) (x : Q₁) (a : A₁) : ℝ :=
  (K.inner y).weight x * if K.accepts x y a b then 1 else 0

theorem apply_eq_kernelApply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply f y b = kernelApply K.coefficients f y b := by
  classical
  unfold apply kernelApply coefficients
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : K.accepts x y a b = true <;> simp [h]

theorem apply_nonnegative (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (hf : ∀ x a, 0 ≤ f x a) (y : Q₂) (b : A₂) :
    0 ≤ K.apply f y b := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg ((K.inner y).nonnegative x)
  apply Finset.sum_nonneg
  intro a _
  split
  · exact hf x a
  · exact le_rfl

theorem apply_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : I → Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => ∑ i, f i x a) y b = ∑ i, K.apply (f i) y b := by
  simp_rw [apply_eq_kernelApply]
  exact kernelApply_sum _ _ _ _

theorem apply_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => r * f x a) y b = r * K.apply f y b := by
  simp_rw [apply_eq_kernelApply]
  exact kernelApply_smul _ _ _ _ _

def product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    ProjectionKernel (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) where
  outer := K.outer.product H.outer
  inner q := (K.inner q.1).product (H.inner q.2)
  accepts x y a b := K.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2
  projection x y a b b' hb hb' := by
    have h₁ := Bool.and_eq_true_iff.mp hb
    have h₂ := Bool.and_eq_true_iff.mp hb'
    exact Prod.ext (K.projection _ _ _ _ _ h₁.1 h₂.1)
      (H.projection _ _ _ _ _ h₁.2 h₂.2)

theorem coefficients_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    (K.product H).coefficients = tensorKernel K.coefficients H.coefficients := by
  funext yz bc xu ad
  unfold coefficients product tensorKernel FiniteDistribution.product
  by_cases hk : K.accepts xu.1 yz.1 ad.1 bc.1 = true <;>
    by_cases hh : H.accepts xu.2 yz.2 ad.2 bc.2 = true <;> simp [hk, hh]

theorem apply_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (f : (Q₁ × R₁) → (A₁ × B₁) → ℝ)
    (y : Q₂) (z : R₂) (b : A₂) (c : B₂) :
    (K.product H).apply f (y,z) (b,c) =
      K.apply (fun x a => H.apply (fun u d => f (x,u) (a,d)) z c) y b := by
  simp_rw [apply_eq_kernelApply]
  rw [coefficients_product]
  exact kernelApply_tensor _ _ _ _ _ _ _

end ProjectionKernel
end
end DFVSGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_TensorDomination
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition
open DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

def tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁))
    (ω : R₂ × B₂) (x : Q₁) (a : A₁) : ℝ :=
  Real.sqrt (H.outer.weight ω.1) *
    H.apply (fun u d => assignment labels (x,u) (a,d)) ω.1 ω.2

omit [Fintype Q₁] [Fintype A₁] in
theorem tensorSlice_nonnegative (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) (a : A₁) :
    0 ≤ H.tensorSlice labels ω x a := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply H.apply_nonnegative
  intro u d
  unfold assignment
  split
  · exact zero_le_one
  · exact le_rfl

omit [Fintype Q₁] [Fintype R₁] [Fintype B₁] in

theorem sum_assignment_product (labels : (Q₁ × R₁) → (A₁ × B₁))
    (x : Q₁) (u : R₁) (d : B₁) :
    (∑ a, assignment labels (x,u) (a,d)) =
      assignment (fun r => (labels (x,r)).2) u d := by
  classical
  by_cases h : (labels (x,u)).2 = d <;> simp [assignment, Prod.ext_iff, h]

omit [Fintype Q₁] in
theorem tensorSlice_label_mass (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) :
    (∑ a, H.tensorSlice labels ω x a) =
      Real.sqrt (H.outer.weight ω.1) *
        H.apply (assignment (fun r => (labels (x,r)).2)) ω.1 ω.2 := by
  unfold tensorSlice
  rw [← Finset.mul_sum, ← apply_sum]
  simp_rw [sum_assignment_product]

omit [Fintype Q₁] in

theorem vectorMass_tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x =
      H.assignmentEnergy (fun r => (labels (x,r)).2) := by
  classical
  unfold vectorMass assignmentEnergy energy
  simp_rw [tensorSlice_label_mass, mul_pow]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Real.sq_sqrt (H.outer.nonnegative y), Finset.mul_sum]

omit [Fintype Q₁] in
theorem vectorMass_tensorSlice_le [Nonempty B₁]
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x ≤ H.collisionValue := by
  rw [vectorMass_tensorSlice]
  exact H.assignmentEnergy_le_collisionValue _

theorem vectorEnergy_tensorSlice (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) :
    K.vectorEnergy (H.tensorSlice labels) = (K.product H).assignmentEnergy labels := by
  classical
  let p := fun y z b c =>
    K.apply (fun x a => H.apply (fun u d => assignment labels (x,u) (a,d)) z c) y b ^ 2
  have hlhs : K.vectorEnergy (H.tensorSlice labels) =
      ∑ z, ∑ c, ∑ y, ∑ b, K.outer.weight y * H.outer.weight z * p y z b c := by
    simp only [vectorEnergy, energy, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change K.outer.weight y *
      (K.apply (fun x a => Real.sqrt (H.outer.weight z) *
        H.apply (fun u d => assignment labels (x,u) (a,d)) z c) y b) ^ 2 = _
    rw [apply_smul, mul_pow, Real.sq_sqrt (H.outer.nonnegative z)]
    exact (mul_assoc _ _ _).symm
  have hrhs : (K.product H).assignmentEnergy labels =
      ∑ y, ∑ z, ∑ b, ∑ c, K.outer.weight y * H.outer.weight z * p y z b c := by
    simp only [assignmentEnergy, energy, product, FiniteDistribution.product,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    exact congrArg (fun r : ℝ => r ^ 2)
      (apply_product K H (assignment labels) y z b c)
  rw [hlhs, hrhs]
  calc
    (∑ z, ∑ c, ∑ y, ∑ b, K.outer.weight y * H.outer.weight z * p y z b c) =
        ∑ z, ∑ y, ∑ b, ∑ c, K.outer.weight y * H.outer.weight z * p y z b c := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

end ProjectionKernel
end
end DFVSGames.Repetition


namespace DFVSGames.Repetition.ProjectionKernel
open scoped BigOperators
noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

theorem energy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) :
    K.energy (fun x a => r * f x a) = r ^ 2 * K.energy f := by
  unfold energy
  simp_rw [apply_smul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro b _
  exact mul_left_comm _ _ _

theorem vectorEnergy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (r : ℝ) :
    K.vectorEnergy (fun ω x a => r * f ω x a) = r ^ 2 * K.vectorEnergy f := by
  unfold vectorEnergy
  simp_rw [energy_smul]
  exact (Finset.mul_sum _ _ _).symm

theorem vectorEnergy_eq_zero_of_mass_nonpositive
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (hf : ∀ ω x a, 0 ≤ f ω x a)
    (hmass : ∀ x, vectorMass f x ≤ 0) : K.vectorEnergy f = 0 := by
  have hfzero : f = fun _ _ _ => 0 := by
    funext ω x a
    exact entry_eq_zero_of_vectorMass_nonpositive f hf hmass ω x a
  rw [hfzero]
  simp [vectorEnergy, energy, apply]

theorem vectorEnergy_le_of_unit_bound
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (ρ C : ℝ)
    (unit_bound : ∀ f : Ω → Q₁ → A₁ → ℝ,
      (∀ ω x a, 0 ≤ f ω x a) → (∀ x, vectorMass f x ≤ 1) → K.vectorEnergy f ≤ ρ)
    (hC : 0 ≤ C) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ C) :
    K.vectorEnergy f ≤ ρ * C := by
  rcases eq_or_lt_of_le hC with hzero | hpositive
  · have hCzero : C = 0 := hzero.symm
    subst C
    rw [K.vectorEnergy_eq_zero_of_mass_nonpositive f hf hmass, mul_zero]
  · have hsqrt : 0 ≤ (Real.sqrt C)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg C)
    have hscale : ((Real.sqrt C)⁻¹) ^ 2 = C⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hC]
    have hnorm : ∀ x, vectorMass (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a) x ≤ 1 := by
      intro x
      rw [vectorMass_smul, hscale]
      have h := mul_le_mul_of_nonneg_left (hmass x) (inv_nonneg.mpr hC)
      simpa [ne_of_gt hpositive] using h
    have hbound := unit_bound (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a)
      (fun ω x a => mul_nonneg hsqrt (hf ω x a)) hnorm
    rw [vectorEnergy_smul, hscale] at hbound
    have h := mul_le_mul_of_nonneg_left hbound hC
    simpa [← mul_assoc, ne_of_gt hpositive, mul_comm C ρ] using h

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition.ProjectionKernel

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

def reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) : ProjectionKernel R₁ R₂ B₁ B₂ where
  outer := K.outer.transport eQ₂
  inner y := (K.inner (eQ₂.symm y)).transport eQ₁
  accepts x y a b := K.accepts (eQ₁.symm x) (eQ₂.symm y) (eA₁.symm a) (eA₂.symm b)
  projection := by
    intro x y a b b' hb hb'
    exact eA₂.symm.injective (K.projection _ _ _ _ _ hb hb')

theorem apply_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂)
    (f : R₁ → B₁ → ℝ) (y : R₂) (b : B₂) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).apply f y b =
      K.apply (fun x a => f (eQ₁ x) (eA₁ a)) (eQ₂.symm y) (eA₂.symm b) := by
  classical
  unfold apply
  change (∑ x, (K.inner (eQ₂.symm y)).weight (eQ₁.symm x) *
    ∑ a, if K.accepts (eQ₁.symm x) (eQ₂.symm y) (eA₁.symm a) (eA₂.symm b)
      then f x a else 0) = _
  refine Fintype.sum_equiv eQ₁.symm _ _ ?_
  intro x
  simp only [Equiv.apply_symm_apply]
  congr 1
  refine Fintype.sum_equiv eA₁.symm _ _ ?_
  intro a
  simp only [Equiv.apply_symm_apply]

theorem energy_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) (f : R₁ → B₁ → ℝ) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).energy f =
      K.energy (fun x a => f (eQ₁ x) (eA₁ a)) := by
  classical
  unfold energy
  simp_rw [apply_reindex]
  change (∑ y, K.outer.weight (eQ₂.symm y) *
    ∑ b, K.apply (fun x a => f (eQ₁ x) (eA₁ a)) (eQ₂.symm y) (eA₂.symm b) ^ 2) = _
  refine Fintype.sum_equiv eQ₂.symm _ _ ?_
  intro y
  congr 1
  exact Fintype.sum_equiv eA₂.symm _ _ (fun _ => rfl)

theorem assignmentEnergy_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) (labels : R₁ → B₁) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).assignmentEnergy labels =
      K.assignmentEnergy (fun x => eA₁.symm (labels (eQ₁ x))) := by
  classical
  unfold assignmentEnergy
  rw [energy_reindex]
  congr 1
  funext x a
  unfold assignment
  have h : labels (eQ₁ x) = eA₁ a ↔ eA₁.symm (labels (eQ₁ x)) = a := by
    constructor
    · intro ha
      rw [ha, Equiv.symm_apply_apply]
    · intro ha
      calc
        labels (eQ₁ x) = eA₁ (eA₁.symm (labels (eQ₁ x))) :=
          (eA₁.apply_symm_apply _).symm
        _ = eA₁ a := congrArg eA₁ ha
  rw [h]

theorem collisionValue_reindex [Nonempty A₁] [Nonempty B₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).collisionValue = K.collisionValue := by
  classical
  apply le_antisymm
  · apply ((K.reindex eQ₁ eQ₂ eA₁ eA₂).collisionValue_le_iff _).2
    intro labels
    rw [assignmentEnergy_reindex]
    exact K.assignmentEnergy_le_collisionValue _
  · apply (K.collisionValue_le_iff _).2
    intro labels
    have h := (K.reindex eQ₁ eQ₂ eA₁ eA₂).assignmentEnergy_le_collisionValue
      (fun x => eA₁ (labels (eQ₁.symm x)))
    simpa only [assignmentEnergy_reindex, Equiv.symm_apply_apply] using h

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition.ProjectionKernel

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

theorem eq_of_data_eq {K H : ProjectionKernel Q₁ Q₂ A₁ A₂}
    (houter : K.outer = H.outer) (hinner : K.inner = H.inner)
    (haccepts : K.accepts = H.accepts) : K = H := by
  cases K
  cases H
  cases houter
  cases hinner
  cases haccepts
  rfl

theorem repetition_succ (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    K.repetition (n + 1) =
      (K.product (K.repetition n)).reindex
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₂))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₂)) := by
  classical
  apply eq_of_data_eq
  · apply FiniteDistribution.eq_of_weight_eq
    intro y
    change (∏ i : Fin (n + 1), K.outer.weight (y i)) =
      K.outer.weight (y 0) * ∏ i : Fin n, K.outer.weight (y i.succ)
    exact Fin.prod_univ_succ _
  · funext y
    apply FiniteDistribution.eq_of_weight_eq
    intro x
    change (∏ i : Fin (n + 1), (K.inner (y i)).weight (x i)) =
      (K.inner (y 0)).weight (x 0) *
        ∏ i : Fin n, (K.inner (y i.succ)).weight (x i.succ)
    exact Fin.prod_univ_succ _
  · funext x y a b
    apply Bool.eq_iff_iff.mpr
    change (decide (∀ i : Fin (n + 1), K.accepts (x i) (y i) (a i) (b i) = true) = true) ↔
      (K.accepts (x 0) (y 0) (a 0) (b 0) &&
        decide (∀ i : Fin n, K.accepts (x i.succ) (y i.succ) (a i.succ) (b i.succ) = true)) = true
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩
    · rintro ⟨hzero, hsucc⟩ i
      exact Fin.cases hzero hsucc i

theorem collisionValue_repetition_succ [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    (K.repetition (n + 1)).collisionValue =
      (K.product (K.repetition n)).collisionValue := by
  rw [repetition_succ, collisionValue_reindex]

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition

theorem rate_of_squared_collision_recurrence {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (c v : ℕ → ℝ) (hzero : c 0 ≤ 1)
    (hstep : ∀ n, c (n + 1) ≤ (1 - gap ^ 2 / 8) * c n)
    (hvalue : ∀ n, v n ^ 2 ≤ c n) :
    ∀ n, v n ≤ dsRate gap ^ n := by
  have hr : 0 ≤ 1 - gap ^ 2 / 8 := by nlinarith
  have hpow := sequence_le_power hr c hzero hstep
  intro n
  apply le_of_sq_le_sq _ (pow_nonneg (dsRate_nonneg hgap₀ hgap₁) n)
  calc
    v n ^ 2 ≤ c n := hvalue n
    _ ≤ (1 - gap ^ 2 / 8) ^ n := hpow n
    _ ≤ (dsRate gap ^ 2) ^ n :=
      pow_le_pow_left₀ hr (squared_rate_le_dsRate_sq hgap₀ hgap₁) n
    _ = (dsRate gap ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]


open DFVSGames.Foundations.Games
end DFVSGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Explicit
attribute [-instance] _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Decoder.PaddedLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

abbrev RawTuple (J : Finset (Fin k)) (V : Type) :=
  V × ((PositionOutside J → V × V) × (PositionInside J → V))


variable [Fintype V]

def blockKernel : ProjectionChoice → BlockDraw V → ℝ
  | none, .inl ab => uniformWeights (V × V) ab
  | some i, .inr ja => if i = ja.1 then uniformWeights V ja.2 else 0
  | _, _ => 0

def kernelTupleWeight (c : Fin k → ProjectionChoice) (d : Fin k → BlockDraw V) : ℝ :=
  ∏ j, blockKernel (c j) (d j)

theorem not_mem_choiceMask (c : Fin k → ProjectionChoice) (j : Fin k) :
    j ∉ choiceMask c ↔ c j = none := by
  cases h : c j <;> simp [choiceMask, h]


end
end DFVSGames.Decoder.PaddedLaw

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_NoiseEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.TableKeysGame

open DFVSGames.Integration.BinaryLinear DFVSGames.Reduction
open ActualSource Foundations.Target
open scoped BigOperators

abbrev Map (k s d : Nat) := ActualGame.Map k s d

end DFVSGames.Decoder.TableKeysGame

namespace DFVSGames.Decoder.TableKeysPrivateRow

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ActualSource

noncomputable section

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

def targetIntercept (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (z : RawPartnerTarget.RawPoint J) (u : Alphabet s) : Alphabet s :=
  AdviceFibers.observedBase A rows z + u

end

end DFVSGames.Decoder.TableKeysPrivateRow

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_CookLevin_PolynomialMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.CookLevin.PolynomialMachine

theorem coefficientPolynomial_eval (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n = cs.foldr (fun digit value => value * n + digit) 0 := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a rest ih => simp [coefficientPolynomial, ih]

theorem coefficientPolynomial_eval_reverse (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n =
      cs.reverse.foldl (fun value digit => value * n + digit) 0 := by
  rw [coefficientPolynomial_eval, List.foldr_eq_foldl_reverse]

theorem highCoefficients_foldl (p : Polynomial Nat) (n : Nat) :
    (highCoefficients p).foldl (fun value digit => value * n + digit) 0 = p.eval n := by
  calc
    _ = (coefficientPolynomial (coefficients p).val).eval n :=
      (coefficientPolynomial_eval_reverse (coefficients p).val n).symm
    _ = p.eval n := congrArg (fun q : Polynomial Nat => q.eval n) (coefficients p).property

theorem range_map_digit (p : Polynomial Nat) :
    (List.range (width p)).map (digit p) = highCoefficients p := by
  apply List.ext_getElem
  · simp [width]
  · intro i hi hj
    simp [digit, width, hj]

section LiteralFields

open Turing
open DFVSGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_prependFields (word : K → List Bool) (indices : List K)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (prependFields word indices continuation) state tapes =
      TM2.stepAux continuation state (prependFieldsTapes word indices tapes) := by
  induction indices generalizing tapes with
  | nil => rfl
  | cons k rest ih =>
    simp only [prependFields, stepAux_pushWord, List.reverse_reverse, prependFieldsTapes]
    exact ih _

theorem stepAux_popN (k : K) (n : Nat)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (popN k n continuation) state tapes =
      TM2.stepAux continuation state (Function.update tapes k ((tapes k).drop n)) := by
  induction n generalizing tapes with
  | zero => simp [popN]
  | succ n ih =>
    simp only [popN, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.drop_tail]

def clearFieldsTapes (count : K → Nat) : List K → (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes => clearFieldsTapes count rest
      (Function.update tapes k ((tapes k).drop (count k)))

theorem stepAux_clearFields (count : K → Nat) (indices : List K)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (clearFields count indices continuation) state tapes =
      TM2.stepAux continuation state (clearFieldsTapes count indices tapes) := by
  induction indices generalizing tapes with
  | nil => rfl
  | cons k rest ih =>
    simp only [clearFields, stepAux_popN, clearFieldsTapes]
    exact ih _

theorem clearFieldsTapes_apply (count : K → Nat) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    clearFieldsTapes count indices tapes k =
      if k ∈ indices then (tapes k).drop (count k) else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [clearFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [clearFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

end LiteralFields

noncomputable section

theorem prefixValuePolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixValuePolynomial digits i).eval n = MachineHorner.value n digits i := by
  induction i with
  | zero => simp [prefixValuePolynomial, MachineHorner.value]
  | succ i ih => simp [prefixValuePolynomial, MachineHorner.value, ih]

theorem prefixCostPolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixCostPolynomial digits i).eval n = MachineHorner.prefixSteps n digits i := by
  induction i with
  | zero => simp [prefixCostPolynomial, MachineHorner.prefixSteps]
  | succ i ih =>
    simp only [prefixCostPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval, ih,
      MachineHorner.prefixSteps, MachineHorner.stepCost, MachineRadixStep.steps]
    ring

end

end DFVSGames.Foundations.Complexity.CookLevin.PolynomialMachine


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSliceQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Decoder.TransferredDecoding

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ActualSource
open scoped BigOperators Classical

open DFVSGames.Inverse

attribute [local instance] Fintype.ofFinite

local instance homFintype {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective

section Rebase

variable {E K R : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup K] [Module F2 K] [AddCommGroup R] [Module F2 R]

def privateOrigin (A : K →ₗ[F2] R) (rows : AdviceFibers.ObservedRow (E := E) A)
    (Mstar : E →ₗ[F2] K) (hstar : A.comp Mstar = rows.val) : E →ₗ[F2] A.ker :=
  AdviceFibers.kernelDifference A rows.val (AdviceFibers.observedBase A rows)
    (AdviceFibers.observedBase_property A rows) ⟨Mstar, hstar⟩

end Rebase

end DFVSGames.Decoder.TransferredDecoding
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

theorem size_le_mul {k : Nat} (hk : 0 < k) : size k ≤ growth * k := by
  by_cases hk1 : k = 1
  · subst k
    simpa [size, level] using growth_gt_one.le
  · have hk2 : 1 < k := by omega
    have hl : 0 < level k := Nat.clog_pos growth_gt_one hk2
    have hp : growth ^ (level k).pred < k :=
      Nat.pow_pred_clog_lt_self growth_gt_one hk2
    have he : (level k).pred + 1 = level k := Nat.succ_pred_eq_of_pos hl
    calc
      size k = growth ^ ((level k).pred + 1) := by rw [he]; rfl
      _ = growth * growth ^ (level k).pred := by rw [pow_succ, Nat.mul_comm]
      _ ≤ growth * k := Nat.mul_le_mul_left growth hp.le

end DFVSGames.Foundations.PCP.ExpanderFamily


namespace DFVSGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

theorem vertexCount_eq (q n : Nat) : vertexCount q n = (q * q) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vertexCount, ih, pow_succ]

end DFVSGames.Foundations.PCP.ExpanderTables


namespace DFVSGames.Foundations.PCP.PreprocessingLevels

theorem levelLoop_level_le (g k fuel e s : Nat) :
    (levelLoop g k fuel e s).1 ≤ e + fuel := by
  induction fuel generalizing e s with
  | zero => simp only [levelLoop, Nat.add_zero, le_refl]
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · omega
      · have h := ih (e + 1) (s * g)
        omega

theorem levelLoop_power (g k fuel e : Nat) :
    (levelLoop g k fuel e (g ^ e)).2 =
      g ^ (levelLoop g k fuel e (g ^ e)).1 := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · rfl
      · simpa only [pow_succ] using ih (e + 1)

theorem levelLoop_covers (g k fuel e s : Nat) (hg : 1 < g)
    (hs : 0 < s) (hbudget : k ≤ s + fuel) :
    k ≤ (levelLoop g k fuel e s).2 := by
  induction fuel generalizing e s with
  | zero => simpa only [levelLoop, Nat.add_zero] using hbudget
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · assumption
      · apply ih
        · exact Nat.mul_pos hs (by omega)
        · have htwo : 2 ≤ g := by omega
          have hmul : s * 2 ≤ s * g := Nat.mul_le_mul_left s htwo
          omega

theorem levelLoop_le_of_covering_power (g k fuel e j : Nat)
    (he : e ≤ j) (hj : k ≤ g ^ j) :
    (levelLoop g k fuel e (g ^ e)).1 ≤ j := by
  induction fuel generalizing e with
  | zero => exact he
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · exact he
      · rename_i hnot
        have hne : e ≠ j := by
          intro h
          subst e
          exact hnot hj
        have hnext : e + 1 ≤ j := by omega
        simpa only [pow_succ] using ih (e + 1) hnext

end DFVSGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PreprocessingRegularTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks

def internalDegree : Nat := Expanders.baseDegree * Expanders.baseDegree

end DFVSGames.Foundations.PCP.PreprocessingRegularTables


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Preprocessing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

end DFVSGames.Foundations.PCP.Preprocessing
end

namespace DFVSGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def degree : Nat := 2 * ((internalDegree + 1) + internalDegree)

end DFVSGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_VerifierCNF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.VerifierToCNF

open Target

theorem freshIndex_value {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) :
    (freshIndex V e p j).val =
      V.«variables» + ((e.val * (patterns q).length + p.val) * (q - 3) + j.val) := by
  simp [freshIndex, Fin.natAdd, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

end DFVSGames.Foundations.PCP.VerifierToCNF

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

variable {Λ σ : Type}

open DFVSGames.Foundations.PCP

theorem rowsHits_eq_filter (v : Nat) (rs : List Row) :
    rowsHits v rs = (rs.filter (fun r => decide (r.1 = v))).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      by_cases h : r.1 = v <;> simp [rowsHits, h, ih, Nat.add_comm]

end DFVSGames.Foundations.Complexity.MachineCloudCount

namespace DFVSGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open DFVSGames.Foundations.PCP

variable {σ : Type}

theorem coreTime_le (g k f p : Nat) :
    coreTime g k f p ≤ (f + 1) * roundBudget g k := by
  have hB : 3 ≤ roundBudget g k := by unfold roundBudget; omega
  induction f generalizing p with
  | zero => simpa only [coreTime, Nat.zero_add, Nat.one_mul] using hB
  | succ f ih =>
      rw [coreTime]
      by_cases h : k ≤ p
      · rw [ite_eq_left h]
        have hp := prefixTime_le_roundBudget g k p
        have hm := Nat.mul_le_mul_left (f + 1) hB
        have hc : f + 2 ≤ (f + 1) * roundBudget g k := by omega
        calc
          prefixTime k p + (f + 2) ≤ roundBudget g k + (f + 1) * roundBudget g k :=
            Nat.add_le_add hp hc
          _ = (f + 1 + 1) * roundBudget g k := by ring
      · rw [ite_eq_right h]
        have hb := continuingTime_le g k p (by omega)
        have hr := ih (p * g)
        calc
          prefixTime k p + ((p + g * p + 2) + coreTime g k f (p * g)) =
              (prefixTime k p + (p + g * p + 2)) + coreTime g k f (p * g) := by omega
          _ ≤ roundBudget g k + (f + 1) * roundBudget g k := Nat.add_le_add hb hr
          _ = (f + 1 + 1) * roundBudget g k := by ring

theorem totalTime_le (g k : Nat) : totalTime g k ≤ timeBound g k := by
  have h := coreTime_le g k k 1
  calc
    totalTime g k ≤ 1 + 2 * (k + 2) + (k + 1) * roundBudget g k :=
      Nat.add_le_add_left h _
    _ = timeBound g k := by unfold roundBudget timeBound; ring

end DFVSGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineCloudPadding

open Turing
open MachineComposition
open DFVSGames.Foundations.PCP

namespace Placement

variable {K K' Λ Λ' σ : Type}

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | some l => some (labels l)
  | none => exit

def configuration (view : K' → Option K) (labels : Λ → Λ') (exit : Option Λ')
    (extra : K' → List Bool) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K' => Bool) Λ' σ :=
  ⟨label labels exit c.l, c.var, tapes view c.stk extra⟩

end Placement

inductive Label
  | init | countCode (l : MachineCloudCount.Label)
  | branch | powerCode (l : MachineCeilingPower.Label)
  | subtract | restore
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool

end DFVSGames.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_InitialGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.FinalConstants

def windowHalf : Nat := denominator * Preprocessing.sizeFactor
def smoothingScale : Nat := 4 * alphabet * windowHalf
def endpointLength : Nat := smoothingScale ^ 2

end DFVSGames.Foundations.PCP.FinalConstants

namespace DFVSGames.Foundations.PCP.RoundTables

opaque fixedWalkParameter : {n : Nat // n = 2 * FinalConstants.endpointLength} :=
  ⟨2 * FinalConstants.endpointLength, rfl⟩

def walkParameter : Nat := fixedWalkParameter.val

theorem degree_positive : 0 < PreprocessingTables.degree := by
  unfold PreprocessingTables.degree
  omega

end DFVSGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePreservingLookupClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineAppendAt

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

def appendTapes (source destination : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source destination base []
    (base destination ++ base source)

@[simp] theorem appendTapes_source (source destination : K)
    (distinct : source ≠ destination) (base : K → List β) :
    appendTapes source destination base source = [] := by
  simp [appendTapes, distinct]

@[simp] theorem appendTapes_destination (source destination : K) (base : K → List β) :
    appendTapes source destination base destination = base destination ++ base source := by
  simp [appendTapes]

def firstTapes_inline_MachineAppendAt (destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt destination scratch base [] (base destination).reverse

def secondTapes_inline_MachineAppendAt (source destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch (firstTapes_inline_MachineAppendAt destination scratch base) []
    ((base source).reverse ++ (base destination).reverse)

theorem finalTapes_eq_inline_MachineAppendAt (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    Reduction.MachineTransfer.tapesAt scratch destination
      (secondTapes_inline_MachineAppendAt source destination scratch base) [] (base destination ++ base source) =
        appendTapes source destination base := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [appendTapes, secondTapes_inline_MachineAppendAt, firstTapes_inline_MachineAppendAt, Reduction.MachineTransfer.tapesAt,
      sourceDestination, sourceScratch]
  · by_cases hd : k = destination
    · subst k
      simp [appendTapes, Reduction.MachineTransfer.tapesAt]
    · by_cases ht : k = scratch
      · subst k
        simp [appendTapes, Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch,
          Ne.symm destinationScratch, scratchEmpty]
      · simp [appendTapes, secondTapes_inline_MachineAppendAt, firstTapes_inline_MachineAppendAt, Reduction.MachineTransfer.tapesAt,
          hs, hd, ht]

end DFVSGames.Foundations.Complexity.MachineAppendAt


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineRegularExecutionBounds
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

abbrev Label (Λ : Type) (chosen : List K) := Λ ⊕ (MachineDrainMany.Label chosen ⊕ Unit)

def cleanupLabel (chosen : List K) : MachineDrainMany.Label chosen → Label Λ chosen :=
  fun label => .inr (.inl label)

def resetLabel (chosen : List K) : Label Λ chosen := .inr (.inr ())

def cleanupEntry (chosen : List K) : Option (Label Λ chosen) :=
  MachineDrainMany.entry chosen (cleanupLabel chosen) (some (resetLabel chosen))

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLazyTableRuntime
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

theorem bitLength_half {n : Nat} (h : n ≠ 0) : bitLength n = bitLength (n / 2) + 1 := by
  by_cases hone : n = 1
  · subst n; rfl
  have hn : 2 ≤ n := by omega
  have hh : n / 2 ≠ 0 := by omega
  rw [bitLength_positive h, bitLength_positive hh, Nat.log2_def n, ite_eq_left hn]

theorem increments_half {n : Nat} (h : n ≠ 0) (started : Bool) :
    increments n started = increments (n / 2) true + 1 := by
  rw [increments, ite_eq_right h, increments_true, bitLength_half h]

end DFVSGames.Foundations.Complexity.MachineLogCounter

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RawInitialMachineFinish
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

namespace Program

open PCP.AlphabetTable

def source : Fin 5 → Tape :=
  Fin.cases .vertices (Fin.cases .darts (Fin.cases .tail (Fin.cases .head (fun _ => .rowIndex))))

theorem source_ne_scratch (i : Fin 5) : source i ≠ Tape.scratch := by
  fin_cases i <;> decide

theorem source_ne_accumulator (i : Fin 5) : source i ≠ Tape.accumulator := by
  fin_cases i <;> decide

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

open Turing
open PCP.AlphabetTable

def headerInputTapes (input : List Bool) : Tape → List Bool :=
  headerFrame input [] [] [] [] [] [] []

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Clone100Counting
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

namespace DFVSGames.Outer.Clone100Triples

abbrev Triple := Index × Index × Index

def good (t : Triple) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

instance instDecidablePredTripleGood : DecidablePred good := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

abbrev GoodTriple := {t : Triple // good t}

def toEmbedding (t : GoodTriple) : Fin 3 ↪ Index where
  toFun := ![t.val.1, t.val.2.1, t.val.2.2]
  inj' := by
    have h01 := t.property.1
    have h02 := t.property.2.1
    have h12 := t.property.2.2
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def fromEmbedding (f : Fin 3 ↪ Index) : GoodTriple :=
  ⟨(f 0, f 1, f 2), by
    constructor
    · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (f.injective h)
    constructor
    · exact fun h => (by decide : (0 : Fin 3) ≠ 2) (f.injective h)
    · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (f.injective h)⟩

def embeddingEquiv : GoodTriple ≃ (Fin 3 ↪ Index) where
  toFun := toEmbedding
  invFun := fromEmbedding
  left_inv t := by
    apply Subtype.ext
    rfl
  right_inv f := by
    ext i
    fin_cases i <;> rfl

theorem card_goodTriple : Fintype.card GoodTriple = 970200 := by
  rw [Fintype.card_congr embeddingEquiv, Fintype.card_embedding_eq]
  norm_num [Nat.descFactorial_succ]

end DFVSGames.Outer.Clone100Triples
end

section

namespace DFVSGames.Outer.Clone100

open DFVSGames.Reduction CloneGap ActualSource
open Clone100Triples Clone100Counting
open scoped BigOperators

noncomputable section

def triples : List GoodTriple := Finset.univ.toList

theorem triples_length : triples.length = 970200 := by
  simp [triples, card_goodTriple]

end
end DFVSGames.Outer.Clone100

end

section

namespace DFVSGames.Explicit.MachineClone100Model

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

abbrev State (D : Nat) := (Unit × Context D) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label (D : Nat)
  | headerStart (slot : Fin 2)
  | headerLoop (slot : Fin 2)
  | setup (context : Context D)
  | scan (context : Context D)
  | emit (context control : Context D) (symbol : Bool)
  | restore (context : Context D)
  | clearHeader
  | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | cleanup (slot : Fin 4)
  | finalCounter
  | finalReverse
  deriving DecidableEq, Fintype

def defaultControl (D : Nat) : Context D := .inl 0
def initialState (D : Nat) : State D := (((), defaultControl D), none)

def contextNext {D : Nat} : Context D → Option (Label D)
  | .inl j => if j.val = 0 then some (.setup (.inl 1)) else some .clearHeader
  | .inr (i, j) =>
      if hj : j.val + 1 < 4 then some (.setup (.inr (i, ⟨j.val + 1, hj⟩)))
      else if hi : i.val + 1 < D then some (.setup (.inr (⟨i.val + 1, hi⟩, 0)))
      else some (.cleanup 0)

def cleanupNext {D : Nat} (j : Fin 4) : Label D :=
  if hj : j.val + 1 < 4 then .cleanup ⟨j.val + 1, hj⟩ else .guard

def drain {D : Nat} (tape : Tape) (again next : Label D) :
    TM2.Stmt Alphabet (Label D) (State D) :=
  .pop tape (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

end DFVSGames.Explicit.MachineClone100Model
end

section

namespace DFVSGames.Explicit.MachineClone100Context

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

theorem contextSource_ne_scratch {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.scratch := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

end DFVSGames.Explicit.MachineClone100Context
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_MachineClone100Cleanup
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

namespace DFVSGames.Explicit.MachineClone100Triples

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model MachineClone100Context

def startAt (D i : Nat) : Option (Label D) :=
  if h : i < D then some (.setup (.inr (⟨i, h⟩, 0))) else some (.cleanup 0)

end DFVSGames.Explicit.MachineClone100Triples
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.Explicit.MachineClone100

open Turing DFVSGames.Reduction
open DFVSGames.Foundations.Complexity

noncomputable section

def indices (t : Outer.Clone100Triples.GoodTriple) : Nat × Nat × Nat :=
  (t.val.1.val, t.val.2.1.val, t.val.2.2.val)

def triples : List (Nat × Nat × Nat) := Outer.Clone100.triples.map indices

theorem triples_length : triples.length = 970200 := by
  simp [triples, Outer.Clone100.triples_length]

theorem triples_nonempty : triples ≠ [] := by
  apply List.length_pos_iff.mp
  rw [triples_length]
  decide

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryRenameMachine
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

namespace DFVSGames.Explicit.MachineSingleOrbitProgram

open Turing
open DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad
open DFVSGames.Reduction

inductive Label (q : Nat)
  | start | halfFirst | halfSecond | alphabet | count | guard
  | source | subtract | restore | target
  | table (completed : Fin (q + 1))
  | finishStart
  | finish (localLabel : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def copyField {q : Nat} (loopLabel exitLabel : Label q) :
    TM2.Stmt (fun _ : Tape => Bool) (Label q) State :=
  .pop .input (fun state head => (state.1, head))
    (.push .accumulator (fun state => state.2.getD false)
      (.branch (fun state => state.2.getD false)
        (.goto fun _ => loopLabel)
        (.load (fun _ => initialState) (.goto fun _ => exitLabel))))

end DFVSGames.Explicit.MachineSingleOrbitProgram
end

section

namespace DFVSGames.Explicit.MachineSingleOrbitStreams

open Turing DFVSGames.Foundations.Complexity
open MachineComposition MachineSingleOrbitProgram

def cfg {q : Nat} (label : Label q) (register : Option Bool)
    (i c s r a o : List Bool) : TM2.Cfg (fun _ : Tape => Bool) (Label q) State :=
  ⟨some label, ((), register), tapes i c s r a o⟩

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

namespace DFVSGames.Reduction.SourceEquationLookup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
open SourceClauseLookup (discardFieldsTrace)

def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 4 r, true)
def headerLabel (r : Nat) : Label :=
  if r = 0 then .headerFirst else if r = 1 then .headerSecond else .guard

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

def placedLabel (j : Fin width) : Option SourceEquationLookup.Label → Option (Label width)
  | none => some (.clearWork j)
  | some l => some (.lookup j l)

theorem nextLabel_eq (j : Fin width) : nextLabel j = labelAt (j.val + 1) := rfl

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

namespace DFVSGames.Reduction.MachineAddressHeaders

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition

namespace Prefix

def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 2 r, true)

variable {K Λ σ : Type} [DecidableEq K]

def readTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat)
    (suffix : List Bool) : K → List Bool :=
  SourceFieldArray.sequenceTapes (slots 1) (destination slots) (copied slots base)
    0 [n, m] suffix

end Prefix

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CanonicalAddress
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

namespace DFVSGames.Reduction.CanonicalAddress

open CanonicalEncoding

theorem radix_eq_foldl (B : Nat) (words : List Nat) :
    radix B words = words.foldl (fun acc digit => B * acc + digit) 0 := by
  unfold radix
  rw [Nat.ofDigits_eq_foldr, List.foldr_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

end DFVSGames.Reduction.CanonicalAddress
end

end
end
end
end
end
end
end
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

structure Clean (slots : Tape q width ↪ K) (base : K → List Bool) : Prop where
  reversed : base (slots .reversed) = []
  forward : base (slots .forward) = []
  copyScratch : base (slots .copyScratch) = []
  accA : base (slots .accA) = []
  accB : base (slots .accB) = []
  counter : base (slots .counter) = []
  hornerScratch : base (slots .hornerScratch) = []
  digit : ∀ j, base (slots (.digit j)) = []

def forwardTapes (slots : Tape q width ↪ K) (base : K → List Bool) (values : List Nat) :
    K → List Bool := Function.update base (slots .forward) (encodeWords values)

def parsedTapes (slots : Tape q width ↪ K) (base : K → List Bool) (values : List Nat) :
    K → List Bool :=
  SourceFieldArray.sequenceTapes (slots .forward) (parseDestination slots)
    (forwardTapes slots base values) 0 values []

theorem hornerValue_eq_radix (B : Nat) (values : List Nat) :
    MachineHorner.value B (digits values) values.length = CanonicalAddress.radix B values := by
  rw [MachineHorner.value_eq_foldl, CanonicalAddress.radix_eq_foldl]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, digits,
      List.getElem?_eq_getElem hj, Option.getD_some]

omit [DecidableEq K] in
theorem lengthSum_le_inline_MachineTemplateAddress (selected : List K) (base : K → List Bool) (bound : Nat)
    (bounded : ∀ tape ∈ selected, (base tape).length ≤ bound) :
    MachineDrainMany.lengthSum selected base ≤ selected.length * bound := by
  induction selected with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons tape selected ih =>
    have ht := bounded tape (by simp)
    have hs := ih (fun t ht => bounded t (by simp [ht]))
    simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
      List.length_cons] at *
    nlinarith

noncomputable def timePolynomial (tokenCount width : Nat) : Polynomial Nat :=
  MachineHorner.timePolynomial width +
    Polynomial.C (3 * tokenCount + width + 2) * Polynomial.X +
    Polynomial.C (3 * tokenCount + 3 * width + 3)

omit [DecidableEq K] in
theorem timePolynomial_eval (tokenCount width M : Nat) :
    (timePolynomial tokenCount width).eval M =
      (MachineHorner.timePolynomial width).eval M +
      (3 * tokenCount + width + 2) * M + (3 * tokenCount + 3 * width + 3) := by
  simp [timePolynomial]

end DFVSGames.Reduction.MachineTemplateAddress
end

section

namespace DFVSGames.Reduction.MachineAddressEdge

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def edgeBits (B C : Nat) (leftValues rightValues : List Nat) (permutation : List Bool) :
    List Bool :=
  encodeWords [CanonicalAddress.radix B leftValues, C + CanonicalAddress.radix B rightValues] ++
    permutation

noncomputable def timePolynomial (leftCount rightCount width : Nat) : Polynomial Nat :=
  MachineTemplateAddress.timePolynomial leftCount width +
    MachineTemplateAddress.timePolynomial rightCount width +
    2 * (Polynomial.X + 1) ^ width + 4 * Polynomial.X + 12

omit [DecidableEq K] in
theorem timePolynomial_eval (leftCount rightCount width M : Nat) :
    (timePolynomial leftCount rightCount width).eval M =
      (MachineTemplateAddress.timePolynomial leftCount width).eval M +
      (MachineTemplateAddress.timePolynomial rightCount width).eval M +
      2 * (M + 1) ^ width + 4 * M + 12 := by
  simp [timePolynomial]

omit [DecidableEq K] in
theorem radix_le_magnitude (B : Nat) (values : List Nat) (width M : Nat)
    (hlen : values.length = width) (radixBound : B ≤ M)
    (digitBound : ∀ i, i < width → MachineTemplateAddress.digits values i ≤ M) :
    CanonicalAddress.radix B values ≤ (M + 1) ^ width := by
  have h := MachineHorner.value_le B (MachineTemplateAddress.digits values) values.length M
    radixBound (by simpa only [hlen] using digitBound) values.length (Nat.le_refl _)
  rw [MachineTemplateAddress.hornerValue_eq_radix, hlen] at h
  exact h

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

namespace DFVSGames.Reduction.MachineRhsLoad

open Turing
open DFVSGames.Foundations.Complexity

theorem fill_apply {k : Nat} (values initial : Fin k → Bool) (cells : List (Fin k))
    (i : Fin k) : fill values initial cells i = if i ∈ cells then values i else initial i := by
  induction cells generalizing initial with
  | nil => simp [fill]
  | cons j cells ih =>
    change fill values (Function.update initial j (values j)) cells i = _
    rw [ih]
    by_cases hi : i ∈ cells
    · simp [hi]
    · by_cases hij : i = j
      · subst j; simp [hi]
      · simp [hi, hij]

theorem fill_all {k : Nat} (values initial : Fin k → Bool) :
    fill values initial (List.finRange k) = values := by
  funext i
  rw [fill_apply]
  simp only [List.mem_finRange, ↓reduceIte]

section Program

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

theorem stepAux_peekChain (field : Fin k → K) (exit : Option Λ)
    (cells : List (Fin k)) (state : State k σ) (tapes : K → List Bool) :
    TM2.stepAux (peekChain field exit cells) state tapes =
      ⟨exit, setRhs state (fill (readRhs field tapes) (rhs state) cells), tapes⟩ := by
  induction cells generalizing state with
  | nil => cases exit <;> rfl
  | cons i rest ih =>
    simp only [peekChain, TM2.stepAux]
    rw [ih]
    rfl

theorem stepAux_statement (field : Fin k → K) (exit : Option Λ)
    (state : State k σ) (tapes : K → List Bool) :
    TM2.stepAux (statement field exit) state tapes =
      ⟨exit, setRhs state (readRhs field tapes), tapes⟩ := by
  rw [statement, stepAux_peekChain, fill_all]

end Program

end DFVSGames.Reduction.MachineRhsLoad
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

theorem pairs_associate_inline_FixedOutcomes {α β γ : Type*}
    (xs : List α) (ys : List β) (zs : List γ) :
    pairs (pairs xs ys) zs =
      xs.flatMap (fun x => (pairs ys zs).map (fun p => ((x, p.1), p.2))) := by
  simp only [pairs, List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]

end DFVSGames.Reduction.FixedOutcomes
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.Integration.AddressTupleBudget

open Reduction Foundations.Complexity
open AddressTupleBody

variable {k s d noiseCount : Nat}

@[simp] theorem magnitudePolynomial_eval (k s d L : Nat) :
    (magnitudePolynomial k s d).eval L = magnitude k s d L := by
  simp only [magnitudePolynomial, magnitude, radixBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]

theorem field_length_le_magnitude (k s d L : Nat) : L+1 ≤ magnitude k s d L := by
  unfold magnitude
  omega

theorem eval_sum_constant_inline_AddressTupleBudget {α : Type} (items : List α) (p : Polynomial Nat) (M : Nat) :
    ((items.map (fun _ => p)).sum).eval M = items.length*p.eval M := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [List.map_cons, List.sum_cons, Polynomial.eval_add, List.length_cons,
      Nat.add_mul, Nat.one_mul, ih]
    omega

theorem lengthSum_le_of_mem_inline_AddressTupleBudget {K : Type} [DecidableEq K]
    (chosen : List K) (base : K → List Bool) (M : Nat)
    (bounded : ∀ tape ∈ chosen, (base tape).length ≤ M) :
    MachineDrainMany.lengthSum chosen base ≤ chosen.length*M := by
  induction chosen with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons tape chosen ih =>
    have first := bounded tape (by simp)
    have rest := ih (fun t ht => bounded t (List.mem_cons_of_mem tape ht))
    simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
      List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

end DFVSGames.Integration.AddressTupleBudget
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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


