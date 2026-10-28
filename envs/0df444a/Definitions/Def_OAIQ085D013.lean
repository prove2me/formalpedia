-- Prove2me | Definitions.Def_OAIQ085D013
-- name    : OAIQ085D013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:05:24.280987+00:00
-- url     : https://prove2.me/theorems/137405e2-9e94-4ab5-8c25-c02cd91855cf
-- title:
--   Definitions bundle OAIQ085D013 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 290 declarations of OpenAI's Lean: 102 definitions, 3 inductive types or structures, 1 instance and 184 theorems. The definitions and types are `OAI.DFVSGames.BinaryLiteralMachine.instruction`, `OAI.DFVSGames.BinaryNameCompare.compareStateEquiv`, `OAI.DFVSGames.BinaryNameCompare.instruction`, `OAI.DFVSGames.BinaryNameSearch.instruction`, `OAI.DFVSGames.BinaryRenameLoop.instruction`, `OAI.DFVSGames.BinaryTokenMachine.cfg`, `OAI.DFVSGames.BinaryTokenMachine.machine`, `OAI.DFVSGames.BinaryTokenMachine.program`, `OAI.DFVSGames.BinaryTotalInputMachine.cfg`, `OAI.DFVSGames.BinaryTotalInputMachine.instruction`, `OAI.DFVSGames.BinaryTotalInputMachine.machine`, `OAI.DFVSGames.Decoder.PaddedLaw.ChoiceValue`, `OAI.DFVSGames.Decoder.PaddedLaw.choiceEmbed`, `OAI.DFVSGames.Decoder.PaddedLaw.choiceValuesRawTupleEquiv`, `OAI.DFVSGames.Decoder.PaddedLaw.choiceValuesToRawTuple`, `OAI.DFVSGames.Decoder.PaddedLaw.fullChoiceValue`, `OAI.DFVSGames.Decoder.PaddedLaw.interceptShift`, `OAI.DFVSGames.Decoder.PaddedLaw.paddedMapWeights`, `OAI.DFVSGames.Decoder.PaddedLaw.paddedWeights`, `OAI.DFVSGames.Decoder.PaddedLaw.rawTupleEquiv`, `OAI.DFVSGames.Decoder.PaddedLaw.rawTupleToChoiceValues`, `OAI.DFVSGames.Decoder.PaddedLaw.readChoiceValue`, `OAI.DFVSGames.Decoder.PaddedLaw.singleChoiceValue`, `OAI.DFVSGames.Decoder.PaddedLaw.tupleDraw`, `OAI.DFVSGames.Decoder.PositiveMultiplier.equalityAcceptance`, `OAI.DFVSGames.Decoder.PositiveMultiplier.subspaceLaw`, `OAI.DFVSGames.Decoder.PrivateFourier.frequencyCoset`, `OAI.DFVSGames.Decoder.PrivateFourier.sliceCorrelation`, `OAI.DFVSGames.Decoder.PrivateStrategy.conditionalAgreement`, `OAI.DFVSGames.Decoder.PrivateStrategy.goodCosetMass`, `OAI.DFVSGames.Decoder.VisibleTransfer.fiberMass`, `OAI.DFVSGames.Decoder.VisibleTransfer.visibleWitness`, `OAI.DFVSGames.Explicit.MachineClone100Loop.recordOfEquation`, `OAI.DFVSGames.Explicit.MachineClone100Table.cloneEquationWords`, `OAI.DFVSGames.Explicit.MachineOutputContract.BinaryGapReduction`, `OAI.DFVSGames.Explicit.MachineProductBounds.rowCost`, `OAI.DFVSGames.Explicit.MachineProductField.emitted`, `OAI.DFVSGames.Explicit.MachineProductField.evaluated`, `OAI.DFVSGames.Explicit.MachineProductField.finalTapes`, `OAI.DFVSGames.Explicit.MachineProductField.gathered` and 65 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Analysis_PrivateFourier`, `DirectedFeedback_CookLevin_PolynomialMachine`, `DirectedFeedback_Encoding_CanonicalWordTemplate`, `DirectedFeedback_Encoding_ProductTarget`, `DirectedFeedback_Games_AddressTupleBody`, `DirectedFeedback_Games_Explicit`, `DirectedFeedback_Games_FieldArray`, `DirectedFeedback_Games_PositiveMultiplier`, `DirectedFeedback_Games_Product`, `DirectedFeedback_Games_Target`, `DirectedFeedback_Games_TestEmit`, `DirectedFeedback_Games_VisibleTransfer`, `DirectedFeedback_Machines_MachineAddressHeaders`, `DirectedFeedback_Machines_MachineAffineLookup`, `DirectedFeedback_Machines_MachineBinaryLiteralMachine`, `DirectedFeedback_Machines_MachineBinaryNameMachine`, `DirectedFeedback_Machines_MachineBinaryTokenMachine`, `DirectedFeedback_Machines_MachineBinaryTotalInputMachine`, `DirectedFeedback_Machines_MachineEmbedding`, `DirectedFeedback_Machines_MachineLookupSpec`, `DirectedFeedback_Machines_MachineProductField`, `DirectedFeedback_Machines_MachineProductFinish`, `DirectedFeedback_Machines_MachineProductPower`, `DirectedFeedback_Machines_MachineProductProgram`, `DirectedFeedback_Machines_MachineSingleOrbitCodec`, `DirectedFeedback_Machines_MachineSubdivisionInit`, `DirectedFeedback_Machines_MachineSubdivisionLoop`, `DirectedFeedback_Machines_MachineSubstitution`, `DirectedFeedback_Machines_MachineTemplateAddress`, `DirectedFeedback_Machines_MachineTransducer`, `DirectedFeedback_Machines_MachineUnaryAdd`, `DirectedFeedback_Machines_RuntimeFinish`, `DirectedFeedback_Machines_RuntimeSpace`, `DirectedFeedback_Machines_Tape`, `DirectedFeedback_Machines_TupleOrder`, `DirectedFeedback_RankGraph_Clone100Counting`, `DirectedFeedback_RankGraph_MachineClone100Cleanup`, `DirectedFeedback_RankGraph_MachineClone100Finish`.
--
--   **Imports.** It imports the bundles `OAIQ085D006`, `OAIQ085D007` and `OAIQ085D008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D018`, `OAIQ085D019`, `OAIQ085D020`, `OAIQ085D021`, `OAIQ085D022` and `OAIQ085D023`; the statement `OAI.DFVSGames.theorem11`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ085D006
import Definitions.Def_OAIQ085D007
import Definitions.Def_OAIQ085D008

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Reduction.MachineTransfer

open Turing

variable {α β : Type} [Fintype α] [Fintype β]


variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def transferAtInTime (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩)
      ((base src).length + 1) where
  steps := (base src).length + 1
  evals_in_steps := transferAt_fromTapes src dst distinct f fallback loopLabel exit
    program atLoop base ambient register
  steps_le_m := Nat.le_refl _


end DFVSGames.Reduction.MachineTransfer


namespace DFVSGames.Foundations.Complexity.MachineCopy

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

theorem update_fork_source_inline_MachineCopy (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      source replacement = forkTapes source left right base replacement leftOutput rightOutput := by
  funext k
  by_cases hs : k = source
  · subst k; simp [forkTapes, sourceLeft, sourceRight]
  · by_cases hl : k = left
    · subst k; simp [forkTapes, Ne.symm sourceLeft, leftRight]
    · by_cases hr : k = right
      · subst k; simp [forkTapes, Ne.symm sourceRight]
      · simp [forkTapes, hs, hl, hr]

theorem update_fork_left_inline_MachineCopy (source left right : K) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      left replacement = forkTapes source left right base input replacement rightOutput := by
  funext k
  by_cases hl : k = left
  · subst k; simp [forkTapes, leftRight]
  · by_cases hr : k = right
    · subst k; simp [forkTapes, Ne.symm leftRight]
    · simp [forkTapes, hl, hr]

theorem update_fork_right_inline_MachineCopy (source left right : K)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      right replacement = forkTapes source left right base input leftOutput replacement := by
  simp [forkTapes]

theorem forkStep_empty (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (leftOutput rightOutput : List β) (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), forkTapes source left right base [] leftOutput rightOutput⟩ =
        some ⟨exit, (ambient, none), forkTapes source left right base [] leftOutput rightOutput⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base [] leftOutput rightOutput)) = _
  rw [atLoop]
  cases exit <;>
    simp [forkLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, sourceLeft, sourceRight,
      leftRight, update_fork_source_inline_MachineCopy]

theorem forkStep_cons (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (head : β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩ =
      some ⟨some loopLabel, (ambient, some head),
        forkTapes source left right base input (head :: leftOutput) (head :: rightOutput)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base (head :: input) leftOutput rightOutput)) = _
  rw [atLoop]
  simp [forkLoop, TM2.stepAux, sourceLeft, sourceRight, leftRight,
    update_fork_source_inline_MachineCopy, update_fork_left_inline_MachineCopy, update_fork_right_inline_MachineCopy]

theorem forkTrace (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register),
        forkTapes source left right base input leftOutput rightOutput⟩) =
      some ⟨exit, (ambient, none), forkTapes source left right base []
        (input.reverse ++ leftOutput) (input.reverse ++ rightOutput)⟩ := by
  induction input generalizing leftOutput rightOutput register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, List.reverse_nil, List.nil_append] using
        forkStep_empty source left right sourceLeft sourceRight leftRight fallback loopLabel exit
          program atLoop base leftOutput rightOutput ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩) = _
    rw [forkStep_cons source left right sourceLeft sourceRight leftRight fallback loopLabel exit
      program atLoop base head input leftOutput rightOutput ambient register, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem restoredTapes (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    forkTapes scratch source destination (drainedTapes source scratch base) []
      (base source) (base source ++ base destination) =
        Function.update base destination (base source ++ base destination) := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [forkTapes, sourceDestination]
  · by_cases hd : k = destination
    · subst k; simp [forkTapes]
    · by_cases ht : k = scratch
      · subst k
        simp [forkTapes, Ne.symm sourceScratch, Ne.symm destinationScratch, scratchEmpty]
      · simp [forkTapes, drainedTapes, Reduction.MachineTransfer.tapesAt, hs, hd, ht]

theorem copyTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = forkLoop scratch source destination fallback secondLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[2 * ((base source).length + 1)]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (base source ++ base destination)⟩ := by
  have first := Reduction.MachineTransfer.transferAt_fromTapes source scratch sourceScratch
    id fallback firstLabel (some secondLabel) program atFirst base ambient register
  change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  have second := forkTrace scratch source destination (Ne.symm sourceScratch)
    (Ne.symm destinationScratch) sourceDestination fallback secondLabel exit program atSecond
    (drainedTapes source scratch base)
    (drainedTapes source scratch base scratch) (drainedTapes source scratch base source)
    (drainedTapes source scratch base destination) ambient none
  simp only [forkTapes_self] at second
  have scratchWord : drainedTapes source scratch base scratch = (base source).reverse := by
    simp [drainedTapes]
  have sourceWord : drainedTapes source scratch base source = [] := by
    simp [drainedTapes, sourceScratch]
  have destinationWord : drainedTapes source scratch base destination = base destination := by
    simp [drainedTapes, Reduction.MachineTransfer.tapesAt, Ne.symm sourceDestination,
      destinationScratch]
  rw [scratchWord, sourceWord, destinationWord] at second
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at second
  rw [restoredTapes source destination scratch sourceDestination sourceScratch destinationScratch
    base scratchEmpty] at second
  rw [show 2 * ((base source).length + 1) =
    ((base source).length + 1) + ((base source).length + 1) by omega,
    Function.iterate_add_apply, first]
  exact second

def copyInTime (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = forkLoop scratch source destination fallback secondLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) where
  steps := 2 * ((base source).length + 1)
  evals_in_steps := copyTrace source destination scratch sourceDestination sourceScratch
    destinationScratch fallback firstLabel secondLabel exit program atFirst atSecond base
    scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineCopy

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceMachine

open Turing
open DFVSGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

theorem fieldStep_delimiter (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), fieldTapes source destination base (false :: suffix) output⟩ =
      some ⟨exit, (ambient, none), fieldTapes source destination base suffix output⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (fieldTapes source destination base (false :: suffix) output)) = _
  rw [atLoop]
  cases exit <;>
    simp [fieldLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, hne, update_field_source_inline_SourceMachine]

theorem fieldStep_true (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), fieldTapes source destination base (true :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some true),
        fieldTapes source destination base input (true :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (fieldTapes source destination base (true :: input) output)) = _
  rw [atLoop]
  simp [fieldLoop, TM2.stepAux, hne, update_field_source_inline_SourceMachine, update_field_destination_inline_SourceMachine]

theorem fieldLoopTrace (source destination : K) (hne : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        fieldTapes source destination base suffix (List.replicate n true ++ output)⟩ := by
  induction n generalizing output register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
      fieldStep_delimiter source destination hne loopLabel exit program atLoop
        base suffix output ambient register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        fieldTapes source destination base (true :: (encodeWord n ++ suffix)) output⟩) = _
    rw [fieldStep_true source destination hne loopLabel exit program atLoop, ih]
    have hrotate : List.replicate n true ++ true :: output =
        true :: (List.replicate n true ++ output) := by
      calc
        _ = (List.replicate n true ++ [true]) ++ output := by simp
        _ = List.replicate (n + 1) true ++ output := by rw [List.replicate_succ']
        _ = _ := by rw [List.replicate_succ, List.cons_append]
    rw [hrotate]

def fieldInTime (source destination : K) (hne : source ≠ destination)
    (startLabel loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = fieldStart destination loopLabel)
    (atLoop : program loopLabel = fieldLoop source destination loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (hinput : base source = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some startLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        fieldTapes source destination base suffix (encodeWord n ++ base destination)⟩)
      (n + 2) where
  steps := n + 2
  evals_in_steps := by
    have hbase : fieldTapes source destination base (encodeWord n ++ suffix)
        (base destination) = base := by rw [← hinput, fieldTapes_self]
    conv_lhs => rw [← hbase]
    change (MachineComposition.advance (TM2.step program))^[(n + 1) + 1]
      (some ⟨some startLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) (base destination)⟩) = _
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some startLabel, (ambient, register),
        fieldTapes source destination base (encodeWord n ++ suffix) (base destination)⟩) = _
    rw [fieldStartStep source destination startLabel loopLabel program atStart,
      fieldLoopTrace source destination hne loopLabel exit program atLoop]
    simp [encodeWord, List.append_assoc]
  steps_le_m := Nat.le_refl _

def fourFieldsInTime (source : K) (destination : Fin 4 → K)
    (hsep : ∀ j, source ≠ destination j)
    (start loopLabel : Fin 4 → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : ∀ j, program (start j) = fieldStart (destination j) (loopLabel j))
    (atLoop : ∀ j, program (loopLabel j) =
      fieldLoop source (destination j) (loopLabel j) (fieldNext start exit j))
    (base : K → List Bool) (a b c d : Nat) (suffix : List Bool)
    (hinput : base source = encodeWords [a, b, c, d] ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (start 0), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), fourTapes source destination base a b c d suffix⟩)
      (a + b + c + d + 8) := by
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  have h₀ : base source = encodeWord a ++ (encodeWords [b, c, d] ++ suffix) := by
    simpa only [encodeWords, List.append_assoc] using hinput
  have h₁ : t₀ source = encodeWord b ++ (encodeWords [c, d] ++ suffix) := by
    simp [t₀, afterField, hsep, encodeWords, List.append_assoc]
  have h₂ : t₁ source = encodeWord c ++ (encodeWords [d] ++ suffix) := by
    simp [t₁, afterField, hsep, encodeWords, List.append_assoc]
  have h₃ : t₂ source = encodeWord d ++ suffix := by
    simp [t₂, afterField, hsep, encodeWords]
  have p₀ := fieldInTime source (destination 0) (hsep 0) (start 0) (loopLabel 0)
    (some (start 1)) program (atStart 0) (atLoop 0) base a
    (encodeWords [b, c, d] ++ suffix) h₀ ambient register
  have p₁ := fieldInTime source (destination 1) (hsep 1) (start 1) (loopLabel 1)
    (some (start 2)) program (atStart 1) (atLoop 1) t₀ b
    (encodeWords [c, d] ++ suffix) h₁ ambient none
  have p₂ := fieldInTime source (destination 2) (hsep 2) (start 2) (loopLabel 2)
    (some (start 3)) program (atStart 2) (atLoop 2) t₁ c
    (encodeWords [d] ++ suffix) h₂ ambient none
  have p₃ := fieldInTime source (destination 3) (hsep 3) (start 3) (loopLabel 3)
    exit program (atStart 3) (atLoop 3) t₂ d suffix h₃ ambient none
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by have h := p.steps_le_m; omega
  }

end DFVSGames.Foundations.Hastad.SourceMachine


namespace DFVSGames.Foundations.Complexity.MachineDrain

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem drainTrace (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : program again = drain source again exit)
    (base : K → List Bool) (word : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[word.length + 1]
      (some ⟨some again, (ambient, register), Function.update base source word⟩) =
      some ⟨exit, (ambient, none), Function.update base source []⟩ := by
  induction word generalizing register with
  | nil =>
      change some (TM2.stepAux (program again) (ambient, register)
        (Function.update base source [])) = _
      rw [atDrain]
      cases exit <;> simp [drain, TM2.stepAux, Reduction.MachineTransfer.exitAt]
  | cons symbol word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[word.length + 1]
        (some (TM2.stepAux (program again) (ambient, register)
          (Function.update base source (symbol :: word)))) = _
      rw [atDrain]
      simpa [drain, TM2.stepAux] using ih (some symbol)

def drainInTime (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : program again = drain source again exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some again, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), Function.update base source []⟩)
      ((base source).length + 1) where
  steps := (base source).length + 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some again, (ambient, register), base⟩) = _
    simpa only [Function.update_eq_self] using
      drainTrace source again exit program atDrain base (base source) ambient register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Complexity.MachineDrain


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubstitution
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineSequential

open Turing

def program (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) :
    Label first second → TM2.Stmt (Symbols first second) (Label first second)
      (State first second)
  | .inl label => firstStatement first second (first.m label)
  | .inr (.inr label) => secondStatement first second (second.m label)
  | .inr (.inl false) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inl first.k₁) (.inr (.inr ())) relabel fallback
        (bridgeLabel first second false) (some (bridgeLabel first second true))
  | .inr (.inl true) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inr (.inr ())) (.inr (.inl second.k₀)) id fallback
        (bridgeLabel first second true) (some (.inr (.inr second.main)))

def machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) : FinTM2 where
  K := Tape first second
  kFin := by
    letI := first.kFin
    letI := second.kFin
    exact inferInstanceAs (Fintype (first.K ⊕ (second.K ⊕ Unit)))
  k₀ := .inl first.k₀
  k₁ := .inr (.inl second.k₁)
  Γ := Symbols first second
  Λ := Label first second
  ΛFin := by
    letI := first.ΛFin
    letI := second.ΛFin
    exact inferInstanceAs (Fintype (first.Λ ⊕ (Bool ⊕ second.Λ)))
  main := .inl first.main
  σ := State first second
  σFin := by
    letI := first.σFin
    letI := second.σFin
    letI := second.Γk₀Fin
    exact inferInstanceAs (Fintype ((first.σ × second.σ) × Option (second.Γ second.k₀)))
  initialState := ((first.initialState, second.initialState), none)
  Γk₀Fin := first.Γk₀Fin
  m := program first second relabel fallback

theorem firstStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : first.Cfg)
    (transition : first.step a = some b) :
    (machine first second relabel fallback).step (firstConfiguration first second a) =
      some (firstConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement id (firstStates first second)
          (MachineEmbedding.statement (some (bridgeLabel first second false)) (first.m label)))
        ((firstStates first second) (state, (second.initialState, none)))
        (MachineEmbedding.tapes tapes (fun _ => []))) = _
      have controlled := MachineControl.stepAux_simulation id (firstStates first second)
        (MachineEmbedding.statement
          (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
          (some (bridgeLabel first second false)) (first.m label))
        (state, (second.initialState, none)) (MachineEmbedding.tapes tapes (fun _ => []))
      have embedded := MachineEmbedding.stepAux_simulation
        (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
        (some (bridgeLabel first second false)) (second.initialState, (none : Register second))
        (fun _ => []) (first.m label) state tapes
      exact congrArg some (controlled.trans
        (congrArg (MachineControl.configuration id (firstStates first second)) embedded))

theorem secondStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : second.Cfg)
    (transition : second.step a = some b) :
    (machine first second relabel fallback).step (secondConfiguration first second a) =
      some (secondConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement (secondLabels first second) (secondStates first second)
          (MachineStackSwap.statement
            (MachineEmbedding.statement
              (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
              (Λextra := Bool ⊕ first.Λ) none (second.m label))))
        ((secondStates first second) (state, (first.initialState, none)))
        (MachineStackSwap.tapes (MachineEmbedding.tapes tapes (fun _ => [])))) = _
      rw [MachineControl.stepAux_simulation, MachineStackSwap.stepAux_simulation,
        MachineEmbedding.stepAux_simulation]
      rfl

theorem firstConfiguration_init (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (input : List (first.Γ first.k₀)) :
    firstConfiguration first second (initList first input) =
      initList (machine first second relabel fallback) input := by
  unfold firstConfiguration MachineControl.configuration MachineEmbedding.configuration initList
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₀
    · subst k
      simp [machine, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineEmbedding.tapes, h]
  · simp [machine, MachineEmbedding.tapes]
  · simp [machine, MachineEmbedding.tapes]

theorem secondConfiguration_halt (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (output : List (second.Γ second.k₁)) :
    secondConfiguration first second (haltList second output) =
      haltList (machine first second relabel fallback) output := by
  unfold secondConfiguration MachineControl.configuration MachineStackSwap.configuration
    MachineEmbedding.configuration haltList
  congr 1
  funext k
  rcases k with k | k | k
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
  · by_cases h : k = second.k₁
    · subst k
      simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes, h]
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]

def firstTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (first.Γ first.k₁)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (firstConfiguration first second (haltList first word))
      (some (temporaryConfiguration first second (word.reverse.map relabel)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inl first.k₁ : Tape first second) (.inr (.inr ())) (by intro h; cases h)
    relabel fallback (bridgeLabel first second false)
    (some (bridgeLabel first second true)) (program first second relabel fallback) rfl
    (firstConfiguration first second (haltList first word)).stk
    (first.initialState, second.initialState) none
  have inputTape : (firstConfiguration first second (haltList first word)).stk (.inl first.k₁) =
      word := by simp [firstConfiguration, MachineControl.configuration,
        MachineEmbedding.configuration, MachineEmbedding.tapes, haltList]
  have outputTape :
      (firstConfiguration first second (haltList first word)).stk (.inr (.inr ())) = [] := rfl
  rw [inputTape, outputTape, List.append_nil, firstTransfer_tapes] at run
  exact run

def secondTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (second.Γ second.k₀)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (temporaryConfiguration first second word)
      (some (secondConfiguration first second (initList second word.reverse)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inr (.inr ()) : Tape first second) (.inr (.inl second.k₀)) (by intro h; cases h)
    id fallback (bridgeLabel first second true) (some (.inr (.inr second.main)))
    (program first second relabel fallback) rfl (temporaryTapes first second word)
    (first.initialState, second.initialState) none
  simp only [temporaryTapes, List.map_id, List.append_nil] at run
  rw [secondTransfer_tapes] at run
  exact run

def execute (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (input : List (first.Γ first.k₀)) (middle : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₁)) (firstBudget secondBudget : Nat)
    (runFirst : TM2OutputsInTime first input (some middle) firstBudget)
    (runSecond : TM2OutputsInTime second (middle.map relabel) (some output) secondBudget) :
    TM2OutputsInTime (machine first second relabel fallback) input (some output)
      (firstBudget + 2 * (middle.length + 1) + secondBudget) := by
  let start := MachineComposition.liftExecutionInTime first.step
    (machine first second relabel fallback).step (firstConfiguration first second)
    (firstStep first second relabel fallback) runFirst
  let bridge₁ := firstTransfer first second relabel fallback middle
  have bridge₂ := secondTransfer first second relabel fallback (middle.reverse.map relabel)
  have reversal : (middle.reverse.map relabel).reverse = middle.map relabel := by
    simp only [List.map_reverse, List.reverse_reverse]
  rw [reversal] at bridge₂
  simp only [List.length_map, List.length_reverse] at bridge₂
  let finish := MachineComposition.liftExecutionInTime second.step
    (machine first second relabel fallback).step (secondConfiguration first second)
    (secondStep first second relabel fallback) runSecond
  let phase₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start bridge₁
  let phase₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂ bridge₂
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂₃ finish
  rw [firstConfiguration_init, secondConfiguration_halt] at full
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by have h := full.steps_le_m; omega
  }

noncomputable def compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) := by
  let relabel : first.tm.Γ first.tm.k₁ → second.tm.Γ second.tm.k₀ :=
    fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol)
  let defaultSymbol := second.inputAlphabet.symm fallback
  let intermediate : Polynomial Nat := Polynomial.X +
    Polynomial.C (Runtime.programPushBound first.tm) * first.time
  refine {
    tm := machine first.tm second.tm relabel defaultSymbol
    inputAlphabet := first.inputAlphabet
    outputAlphabet := second.outputAlphabet
    time := MachineComposition.compositionPolynomial first.time second.time intermediate
    outputsFun := ?_
  }
  intro a
  let input := (ea a).map first.inputAlphabet.invFun
  let middle := (eb (f a)).map first.outputAlphabet.invFun
  let output := (ec (g (f a))).map second.outputAlphabet.invFun
  have handoff : middle.map relabel = (eb (f a)).map second.inputAlphabet.invFun := by
    dsimp only [middle, relabel]
    simp only [List.map_map]
    apply List.map_congr_left
    intro symbol _
    exact congrArg second.inputAlphabet.symm (first.outputAlphabet.apply_symm_apply symbol)
  have runSecond : TM2OutputsInTime second.tm (middle.map relabel) (some output)
      (second.time.eval (eb (f a)).length) := by
    rw [handoff]
    exact second.outputsFun (f a)
  have full := execute first.tm second.tm relabel defaultSymbol input middle output
    (first.time.eval (ea a).length) (second.time.eval (eb (f a)).length)
    (first.outputsFun a) runSecond
  have intermediateBound : (eb (f a)).length ≤ intermediate.eval (ea a).length :=
    Runtime.encodedOutputLength first a
  have totalBound := MachineComposition.compositionBudget_le first.time second.time
    intermediate (ea a).length (eb (f a)).length intermediateBound
  have middleLength : middle.length = (eb (f a)).length := by simp only [middle, List.length_map]
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans full.steps_le_m
      simpa only [middleLength] using totalBound
  }

noncomputable def composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) :=
  compose first second false

end DFVSGames.Foundations.Complexity.MachineSequential

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTransducer
attribute [-instance] _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineTransducerCopy

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ Q : Type} [DecidableEq K]

abbrev tapes (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input scratchWord outputWord

theorem update_source_inline_MachineTransducerCopy (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      source replacement = tapes source scratch destination base replacement scratchWord outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, sourceScratch, sourceDestination]
  · by_cases ht : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceScratch, scratchDestination]
    · by_cases hd : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm sourceDestination]
      · simp [tapes, MachineCopy.forkTapes, hs, ht, hd]

theorem update_scratch_inline_MachineTransducerCopy (source scratch destination : K)
    (scratchDestination : scratch ≠ destination) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      scratch replacement = tapes source scratch destination base input replacement outputWord := by
  funext k
  by_cases ht : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, scratchDestination]
  · by_cases hd : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, Ne.symm scratchDestination]
    · simp [tapes, MachineCopy.forkTapes, ht, hd]

theorem update_output_inline_MachineTransducerCopy (source scratch destination : K) (base : K → List Bool)
    (input scratchWord outputWord replacement : List Bool) :
    Function.update (tapes source scratch destination base input scratchWord outputWord)
      destination replacement = tapes source scratch destination base input scratchWord replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem scanStep_empty (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base [] scratchWord outputWord⟩ =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] scratchWord outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base [] scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source_inline_MachineTransducerCopy]

theorem scanStep_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, control), register),
      tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩ =
      some ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord) outputWord⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, control), register)
    (tapes source scratch destination base (symbol :: input) scratchWord outputWord)) = _
  rw [atScan]
  simp [scanLoop, TM2.stepAux, sourceScratch, sourceDestination, scratchDestination,
    update_source_inline_MachineTransducerCopy, update_scratch_inline_MachineTransducerCopy]

theorem emitterStep (source scratch destination : K)
    (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (symbol : Bool) :
    TM2.step program ⟨some (emitterLabel control symbol), ((ambient, control), some symbol),
      tapes source scratch destination base input scratchWord outputWord⟩ =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input scratchWord
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change some (TM2.stepAux (program (emitterLabel control symbol)) ((ambient, control), some symbol)
    (tapes source scratch destination base input scratchWord outputWord)) = _
  rw [atEmitter]
  simp only [emitter, TM2.stepAux]
  rw [stepAux_pushWord]
  simp only [TM2.stepAux, MachineCopy.forkTapes_right]
  rw [update_output_inline_MachineTransducerCopy]

theorem twoSteps_cons (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (symbol : Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩) =
      some ⟨some scanLabel, ((ambient, transition control symbol), some symbol),
        tapes source scratch destination base input (symbol :: scratchWord)
          ((emit control symbol).reverse ++ outputWord)⟩ := by
  change (TM2.step program ⟨some scanLabel, ((ambient, control), register),
    tapes source scratch destination base (symbol :: input) scratchWord outputWord⟩).bind
      (TM2.step program) = _
  rw [scanStep_cons source scratch destination sourceScratch sourceDestination scratchDestination
    initial scanLabel restoreLabel emitterLabel program atScan base symbol input scratchWord
    outputWord ambient control register]
  exact emitterStep source scratch destination transition emit scanLabel emitterLabel program
    atEmitter base input (symbol :: scratchWord) outputWord ambient control symbol

theorem scanTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (base : K → List Bool) (input scratchWord outputWord : List Bool)
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * input.length + 1]
      (some ⟨some scanLabel, ((ambient, control), register),
        tapes source scratch destination base input scratchWord outputWord⟩) =
      some ⟨some restoreLabel, ((ambient, initial), none),
        tapes source scratch destination base [] (input.reverse ++ scratchWord)
          ((Reduction.MachineTransducer.output transition emit control input).reverse ++ outputWord)⟩ := by
  induction input generalizing control scratchWord outputWord register with
  | nil =>
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, Reduction.MachineTransducer.output, List.reverse_nil,
      List.nil_append] using
      scanStep_empty source scratch destination sourceScratch sourceDestination scratchDestination
        initial scanLabel restoreLabel emitterLabel program atScan base scratchWord outputWord
        ambient control register
  | cons symbol input ih =>
    rw [List.length_cons, show 2 * (input.length + 1) + 1 = (2 * input.length + 1) + 2 by omega,
      Function.iterate_add_apply]
    rw [twoSteps_cons source scratch destination sourceScratch sourceDestination scratchDestination
      initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
      symbol input scratchWord outputWord ambient control register, ih]
    simp only [Reduction.MachineTransducer.output, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.singleton_append]

theorem restoreTapes (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (outputWord : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base [] (base source).reverse outputWord)
      [] (base source) = Function.update base destination outputWord := by
  funext k
  by_cases hs : k = source
  · subst k; simp [Reduction.MachineTransfer.tapesAt, sourceDestination]
  · by_cases ht : k = scratch
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, Ne.symm sourceScratch, scratchDestination, scratchEmpty]
    · by_cases hd : k = destination
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes,
          Ne.symm sourceDestination, Ne.symm scratchDestination]
      · simp [Reduction.MachineTransfer.tapesAt, tapes, MachineCopy.forkTapes, hs, ht, hd]

theorem transduceCopyTrace (source scratch destination : K)
    (sourceScratch : source ≠ scratch) (sourceDestination : source ≠ destination)
    (scratchDestination : scratch ≠ destination)
    (initial : Q) (transition : Q → Bool → Q) (emit : Q → Bool → List Bool)
    (scanLabel restoreLabel : Λ) (emitterLabel : Q → Bool → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ Q))
    (atScan : program scanLabel = scanLoop source scratch initial emitterLabel restoreLabel)
    (atEmitter : ∀ control symbol, program (emitterLabel control symbol) =
      emitter destination transition emit scanLabel control symbol)
    (atRestore : program restoreLabel =
      Reduction.MachineTransfer.loopAt scratch source id false restoreLabel exit)
    (base : K → List Bool) (scratchEmpty : base scratch = [])
    (ambient : σ) (control : Q) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * (base source).length + 2]
      (some ⟨some scanLabel, ((ambient, control), register), base⟩) =
      some ⟨exit, ((ambient, initial), none),
        Function.update base destination
          ((Reduction.MachineTransducer.output transition emit control (base source)).reverse ++
            base destination)⟩ := by
  have scan := scanTrace source scratch destination sourceScratch sourceDestination scratchDestination
    initial transition emit scanLabel restoreLabel emitterLabel program atScan atEmitter base
    (base source) (base scratch) (base destination) ambient control register
  have tapesSelf : tapes source scratch destination base (base source) (base scratch)
      (base destination) = base := MachineCopy.forkTapes_self source scratch destination base
  rw [tapesSelf] at scan
  simp only [scratchEmpty, List.append_nil] at scan
  let outputWord :=
    (Reduction.MachineTransducer.output transition emit control (base source)).reverse ++ base destination
  let scanned := tapes source scratch destination base [] (base source).reverse outputWord
  have restore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm sourceScratch)
    id false restoreLabel exit program atRestore scanned (ambient, initial) none
  change (MachineComposition.advance (TM2.step program))^[(scanned scratch).length + 1]
    (some ⟨some restoreLabel, ((ambient, initial), none), scanned⟩) = _ at restore
  have scratchWord : scanned scratch = (base source).reverse := by
    simp [scanned, scratchDestination]
  have sourceWord : scanned source = [] := by
    simp [scanned, sourceScratch, sourceDestination]
  rw [scratchWord, sourceWord] at restore
  simp only [List.map_id, List.reverse_reverse, List.append_nil, List.length_reverse] at restore
  rw [restoreTapes source scratch destination sourceScratch sourceDestination scratchDestination
    base scratchEmpty outputWord] at restore
  rw [show 3 * (base source).length + 2 =
    ((base source).length + 1) + (2 * (base source).length + 1) by omega,
    Function.iterate_add_apply, scan]
  exact restore

end DFVSGames.Foundations.Complexity.MachineTransducerCopy


namespace DFVSGames.Reduction.MachineFieldTemplate

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q : Nat} {K Λ σ : Type}

def tokenSteps (fields : Fin q → List Bool) : Token q → Nat
  | .literal _ => 1
  | .copy j => 3 * (fields j).length + 3

def workSteps (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  (tokens.map (tokenSteps fields)).sum

def templateSteps (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  workSteps tokens fields + 1

def copiedLength (tokens : List (Token q)) (fields : Fin q → List Bool) : Nat :=
  (tokens.map (fun t => match t with | .literal _ => 0 | .copy j => (fields j).length)).sum

def instruction (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (place : Label tokens.length → Λ) (exit : Option Λ) :
    Label tokens.length → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .entry i => match tokens.get i with
      | .literal bits => .load reset
          (pushWord output bits (.goto fun _ => place (startAt tokens.length (i.val + 1))))
      | .copy _ => .load reset (.goto fun _ => place (.scan i))
  | .scan i => match tokens.get i with
      | .literal _ => .halt
      | .copy j => MachineTransducerCopy.scanLoop (field j) scratch ()
          (fun _ b => place (.emit i b)) (place (.restore i))
  | .emit i b => MachineTransducerCopy.emitter output (fun _ _ => ()) identityEmit
      (place (.scan i)) () b
  | .restore i => match tokens.get i with
      | .literal _ => .halt
      | .copy j => MachineTransfer.loopAt scratch (field j) id false
          (place (.restore i)) (some (place (startAt tokens.length (i.val + 1))))
  | .done => .load reset (jump exit)

variable [DecidableEq K]

section Execution

variable (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
variable (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
variable (scratchOutput : scratch ≠ output)
variable (place : Label tokens.length → Λ) (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ label,
  P (place label) = instruction tokens field scratch output place exit label)

include atInstruction

theorem doneStep (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place .done), state, base⟩ =
      some ⟨exit, reset state, base⟩ := by
  change some (TM2.stepAux (P (place .done)) state base) = _
  rw [atInstruction .done]
  cases exit <;> rfl

theorem literalStep (i : Fin tokens.length) (bits : List Bool)
    (token : tokens.get i = .literal bits) (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (.entry i)), state, base⟩ =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output bits⟩ := by
  change some (TM2.stepAux (P (place (.entry i))) state base) = _
  rw [atInstruction (.entry i)]
  simp only [instruction, token, TM2.stepAux]
  rw [stepAux_pushWord]
  rfl

theorem copySetupStep (i : Fin tokens.length) (j : Fin q)
    (token : tokens.get i = .copy j) (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (.entry i)), state, base⟩ =
      some ⟨some (place (.scan i)), reset state, base⟩ := by
  change some (TM2.stepAux (P (place (.entry i))) state base) = _
  rw [atInstruction (.entry i)]
  simp only [instruction, token, TM2.stepAux]

include fieldScratch fieldOutput scratchOutput

theorem copyTrace (i : Fin tokens.length) (j : Fin q)
    (token : tokens.get i = .copy j) (base : K → List Bool)
    (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[3 * (base (field j)).length + 3]
      (some ⟨some (place (.entry i)), state, base⟩) =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output (base (field j))⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (field j) scratch output (fieldScratch j) (fieldOutput j) scratchOutput
    () (fun _ _ => ()) identityEmit (place (.scan i)) (place (.restore i))
    (fun _ b => place (.emit i b)) (some (place (startAt tokens.length (i.val + 1)))) P
    (by rw [atInstruction (.scan i)]; simp only [instruction, token])
    (by intro control b; cases control; exact atInstruction (.emit i b))
    (by rw [atInstruction (.restore i)]; simp only [instruction, token])
    base scratchEmpty state.1.1 () none
  rw [show 3 * (base (field j)).length + 3 =
      (3 * (base (field j)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[3 * (base (field j)).length + 2]
    (TM2.step P ⟨some (place (.entry i)), state, base⟩) = _
  rw [copySetupStep tokens field scratch output place exit P atInstruction i j token]
  simpa only [identity_output, reset, outputTapes] using copied

theorem tokenTrace (i : Fin tokens.length) (base : K → List Bool)
    (scratchEmpty : base scratch = []) (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[
      tokenSteps (fun j => base (field j)) (tokens.get i)]
      (some ⟨some (place (.entry i)), state, base⟩) =
      some ⟨some (place (startAt tokens.length (i.val + 1))), reset state,
        outputTapes base output (tokenOutput (fun j => base (field j)) (tokens.get i))⟩ := by
  cases token : tokens.get i with
  | literal bits =>
      simpa only [token, tokenSteps, tokenOutput, Function.iterate_one,
        MachineComposition.advance_some] using
        literalStep tokens field scratch output place exit P atInstruction i bits token base state
  | copy j =>
      simpa only [token, tokenSteps, tokenOutput] using
        copyTrace tokens field scratch output fieldScratch fieldOutput scratchOutput place exit P
          atInstruction i j token base scratchEmpty state

theorem suffixTrace_inline_MachineFieldTemplate (remaining : Nat) :
    ∀ (i : Nat), i + remaining = tokens.length →
      ∀ (base : K → List Bool) (_scratchEmpty : base scratch = []) (state : State σ),
        (MachineComposition.advance (TM2.step P))^[
          workSteps (tokens.drop i) (fun j => base (field j)) + 1]
          (some ⟨some (place (startAt tokens.length i)), state, base⟩) =
          some ⟨exit, reset state, outputTapes base output
            (templateOutput (tokens.drop i) (fun j => base (field j)))⟩ := by
  induction remaining with
  | zero =>
      intro i hi base _scratchEmpty state
      have heq : i = tokens.length := by omega
      subst i
      simpa [startAt, workSteps, templateOutput, MachineComposition.advance_some] using
        doneStep tokens field scratch output place exit P atInstruction base state
  | succ remaining ih =>
      intro i hi base scratchEmpty state
      have hiLt : i < tokens.length := by omega
      let index : Fin tokens.length := ⟨i, hiLt⟩
      let bits := tokenOutput (fun j => base (field j)) (tokens.get index)
      let after := outputTapes base output bits
      have first := tokenTrace tokens field scratch output fieldScratch fieldOutput scratchOutput
        place exit P atInstruction index base scratchEmpty state
      have second := ih (i + 1) (by omega) after
        (by simpa [after, outputTapes, scratchOutput] using scratchEmpty) (reset state)
      have fieldsAfter : (fun j => after (field j)) = (fun j => base (field j)) :=
        fieldValues_outputTapes field output fieldOutput base bits
      rw [fieldsAfter] at second
      have combined := chain_inline_MachineFieldTemplate first second
      simp only [reset_reset, after, outputTapes_append] at combined
      have dropHead : tokens.drop i = tokens.get index :: tokens.drop (i + 1) :=
        List.drop_eq_getElem_cons hiLt
      have hstart : startAt tokens.length i = .entry index := by
        simp [startAt, hiLt, index]
      rw [hstart, dropHead]
      simp only [templateOutput, List.flatMap_cons]
      change _ = some (⟨exit, reset state, outputTapes base output
        (bits ++ templateOutput (tokens.drop (i + 1)) (fun j => base (field j)))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ))
      convert combined using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      simp only [workSteps, List.map_cons, List.sum_cons]
      omega

theorem phaseTrace (base : K → List Bool) (scratchEmpty : base scratch = [])
    (state : State σ) :
    (MachineComposition.advance (TM2.step P))^[templateSteps tokens (fun j => base (field j))]
      (some ⟨some (place (startAt tokens.length 0)), state, base⟩) =
      some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩ := by
  simpa only [Nat.zero_add, List.drop_zero, templateSteps] using
    suffixTrace_inline_MachineFieldTemplate tokens field scratch output fieldScratch fieldOutput scratchOutput place exit P
      atInstruction tokens.length 0 (by omega) base scratchEmpty state

end Execution

theorem templateSteps_le (tokens : List (Token q)) (fields : Fin q → List Bool) :
    templateSteps tokens fields ≤ 3 * copiedLength tokens fields + 3 * tokens.length + 1 := by
  have workBound : workSteps tokens fields ≤
      3 * copiedLength tokens fields + 3 * tokens.length := by
    induction tokens with
    | nil => simp [workSteps, copiedLength]
    | cons token tokens ih =>
        cases token <;>
          simp only [workSteps, copiedLength, List.map_cons, List.sum_cons,
            tokenSteps, List.length_cons] at * <;> omega
  unfold templateSteps
  omega

def phaseInTime (tokens : List (Token q)) (field : Fin q → K) (scratch output : K)
    (fieldScratch : ∀ j, field j ≠ scratch) (fieldOutput : ∀ j, field j ≠ output)
    (scratchOutput : scratch ≠ output) (place : Label tokens.length → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction tokens field scratch output place exit label)
    (base : K → List Bool) (scratchEmpty : base scratch = []) (state : State σ) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (startAt tokens.length 0)), state, base⟩
      (some ⟨exit, reset state,
        outputTapes base output (templateOutput tokens (fun j => base (field j)))⟩)
      (3 * copiedLength tokens (fun j => base (field j)) + 3 * tokens.length + 1) where
  steps := templateSteps tokens (fun j => base (field j))
  evals_in_steps := phaseTrace tokens field scratch output fieldScratch fieldOutput scratchOutput
    place exit P atInstruction base scratchEmpty state
  steps_le_m := templateSteps_le tokens _

end DFVSGames.Reduction.MachineFieldTemplate

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeFinish
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def tapes (source scratch destination : K) (base : K → List Bool)
    (input saved output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input saved output

@[simp] theorem tapes_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output source = input :=
  MachineCopy.forkTapes_source source scratch destination hs hd base input saved output

@[simp] theorem tapes_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output scratch = saved :=
  MachineCopy.forkTapes_left source scratch destination hsd base input saved output

@[simp] theorem tapes_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output destination = output :=
  MachineCopy.forkTapes_right source scratch destination base input saved output

theorem update_source_inline_MachineUnaryAffineAt (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) source replacement =
      tapes source scratch destination base replacement saved output := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, h₀, hsd]
    · by_cases h₂ : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, h₀]
      · simp [tapes, MachineCopy.forkTapes, h₀, h₁, h₂]

theorem update_scratch_inline_MachineUnaryAffineAt (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) scratch replacement =
      tapes source scratch destination base input replacement output := by
  funext k
  by_cases h : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, hsd]
  · by_cases h' : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, h]
    · simp [tapes, MachineCopy.forkTapes, h, h']

theorem update_destination_inline_MachineUnaryAffineAt (source scratch destination : K)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) destination replacement =
      tapes source scratch destination base input saved replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem scan_step_succ (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord (a + 1) ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some scanLabel, (ambient,some true), tapes source scratch destination base
        (encodeWord a ++ suffix) (true :: saved) (encodeWord (coefficient + b) ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord (a + 1) ++ suffix = true :: (encodeWord a ++ suffix) by
    simp [encodeWord, List.replicate_succ]]
  simp [scan, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source_inline_MachineUnaryAffineAt source scratch destination hs hd hsd, tapes_scratch _ _ _ hsd,
    update_scratch_inline_MachineUnaryAffineAt _ _ _ hsd, stepAux_pushWord, tapes_destination,
    prepend_replicate_word, update_destination_inline_MachineUnaryAffineAt]

theorem scan_step_zero (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord 0 ++ suffix = false :: suffix from rfl]
  simp [scan, finish, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source_inline_MachineUnaryAffineAt source scratch destination hs hd hsd]

theorem scanTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[a + 1]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) saved (encodeWord b ++ output)⟩) =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) (List.replicate a true ++ saved)
        (encodeWord (coefficient * a + b) ++ output)⟩ := by
  induction a generalizing b saved register with
  | zero =>
      simpa using scan_step_zero source scratch destination hs hd hsd coefficient scanLabel
        restoreLabel program atScan base b suffix saved output ambient register
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ source scratch destination hs hd hsd coefficient scanLabel restoreLabel
        program atScan]
      rw [ih]
      have hval : coefficient * a + (coefficient + b) = coefficient * (a + 1) + b := by
        rw [Nat.mul_succ]; omega
      rw [hval]
      have hsave : List.replicate a true ++ true :: saved = List.replicate (a + 1) true ++ saved := by
        simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
      rw [hsave]

theorem restoreTapes (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (a value : Nat) (suffix output : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base (encodeWord 0 ++ suffix)
        (List.replicate a true) (encodeWord value ++ output))
      [] (encodeWord a ++ suffix) =
      tapes source scratch destination base (encodeWord a ++ suffix) [] (encodeWord value ++ output) := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k
      simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hs, hsd]
    · by_cases h₂ : k = destination
      · subst k
        simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hd, Ne.symm hsd]
      · simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, h₀, h₁, h₂]

theorem affineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1)]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩) =
      some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩ := by
  have hscan := scanTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    program atScan base a b suffix [] output ambient register
  simp only [List.append_nil] at hscan
  let mid := tapes source scratch destination base (encodeWord 0 ++ suffix)
    (List.replicate a true) (encodeWord (coefficient * a + b) ++ output)
  have hrestore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm hs)
    id false restoreLabel exit program atRestore mid ambient none
  change (advance (TM2.step program))^[(mid scratch).length + 1]
    (some ⟨some restoreLabel,(ambient,none),mid⟩) = _ at hrestore
  have hsaved : mid scratch = List.replicate a true := by
    simp [mid, tapes, hsd]
  have hsource : mid source = encodeWord 0 ++ suffix := by
    simp [mid, tapes, hs, hd]
  rw [hsaved, hsource] at hrestore
  simp only [List.length_replicate, List.reverse_replicate, List.map_id] at hrestore
  have hword : List.replicate a true ++ (encodeWord 0 ++ suffix) = encodeWord a ++ suffix := by
    simp [encodeWord, List.append_assoc]
  rw [hword] at hrestore
  simp only [mid, restoreTapes source scratch destination hs hd hsd] at hrestore
  rw [show 2 * (a + 1) = (a + 1) + (a + 1) by omega, Function.iterate_add_apply, hscan]
  exact hrestore

theorem seededAffineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient offset : Nat) (seedLabel scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program seedLabel = seed destination offset scanLabel)
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord a ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1) + 1]
      (some ⟨some seedLabel, (ambient,register), base⟩) =
      some ⟨exit, (ambient,none),
        Function.update base destination (encodeWord (coefficient * a + offset) ++ base destination)⟩ := by
  have hseed : TM2.step program ⟨some seedLabel,(ambient,register),base⟩ =
      some ⟨some scanLabel,(ambient,register),
        Function.update base destination (encodeWord offset ++ base destination)⟩ := by
    change some (TM2.stepAux (program seedLabel) _ _) = _
    rw [atSeed, seed, stepAux_pushWord]
    simp only [List.reverse_reverse, TM2.stepAux]
  have hrun := affineTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    exit program atScan atRestore base a offset suffix (base destination) ambient register
  have hframe (word : List Bool) :
      tapes source scratch destination base (encodeWord a ++ suffix) [] word =
        Function.update base destination word := by
    rw [← sourceWord, ← scratchEmpty]
    simp only [tapes, MachineCopy.forkTapes, Function.update_eq_self]
  rw [hframe, hframe] at hrun
  rw [Function.iterate_succ_apply]
  simp only [advance_some]
  rw [hseed]
  exact hrun

end DFVSGames.Foundations.Complexity.MachineUnaryAffineAt


namespace DFVSGames.Integration.GapSemantics

open DFVSGames.Foundations.Target

theorem countSatisfied_ofFn {m n q : Nat} (labeling : Fin n → Fin q)
    (constraints : Fin m → Constraint n q) :
    countSatisfied labeling (List.ofFn constraints) =
      ∑ i, if (constraints i).satisfied labeling then (1 : Nat) else 0 := by
  rw [countSatisfied_eq_sum, List.map_ofFn, List.sum_ofFn]
  rfl

end DFVSGames.Integration.GapSemantics

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionInit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionEmission

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction
open MachineSubdivisionProgram

theorem header_template (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      headerBits n q Q := by
  simp [MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput,
    headerTokens, newHeaderField, MachineSubdivisionInit.resultTapes,
    headerBits, encodeWords]

theorem header_copiedLength (n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (headerTokens q)
      (fun j => MachineSubdivisionInit.resultTapes n q Q body (newHeaderField j)) =
      n + 7 * Q + 2 := by
  simp [MachineFieldTemplate.copiedLength, headerTokens, newHeaderField,
    MachineSubdivisionInit.resultTapes]
  omega

end DFVSGames.Explicit.MachineSubdivisionEmission


namespace DFVSGames.Explicit.MachineSubdivisionBody

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction
open MachineSubdivisionProgram

def rowPayload {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : List Bool :=
  MachineFieldTemplate.templateOutput (rowTokens q)
    (fun j => afterTable base u v table suffix (rowField j))

def afterRows {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterTable base u v table suffix) .accumulator
    (rowPayload base u v table suffix)

def afterDrainU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterRows base u v table suffix) .u []

def afterDrainV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainU base u v table suffix) .v []

def afterDrainTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainV base u v table suffix) .permutation []

def bodyResult {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  incrementTapes (afterDrainTable base u v table suffix)

def bodyBudget {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Nat :=
  (u + 2) + (v + 2) + (2 * (q * (q + 1)) + 2) +
    (3 * MachineFieldTemplate.copiedLength (rowTokens q)
      (fun j => afterTable base u v table suffix (rowField j)) + 37) +
    ((afterRows base u v table suffix .u).length + 1) +
    ((afterDrainU base u v table suffix .v).length + 1) +
    ((afterDrainV base u v table suffix .permutation).length + 1) + 1

end DFVSGames.Explicit.MachineSubdivisionBody


namespace DFVSGames.Explicit.MachineSubdivisionBodySpec

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open DFVSGames.Reduction
open MachineSubdivisionProgram MachineSubdivisionBody

def resultTapes {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .u | .v | .permutation | .permutationReverse => []
  | .middle => true :: base .middle
  | .first => true :: true :: base .first
  | .last => true :: true :: base .last
  | .accumulator => (rowPayload base u v table suffix).reverse ++ base .accumulator
  | k => base k

theorem bodyResult_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (_ready : Ready base u v table suffix) :
    bodyResult base u v table suffix = resultTapes base u v table suffix := by
  funext k
  cases k <;> simp [bodyResult, incrementTapes, afterDrainTable, afterDrainV,
    afterDrainU, afterRows, MachineFieldTemplate.outputTapes, afterTable,
    MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, resultTapes]

theorem result_input {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .input = suffix := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem result_accumulator {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .accumulator =
      (rowPayload base u v table suffix).reverse ++ base .accumulator := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem result_indices {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyResult base u v table suffix .middle = encodeWord (n + (e + 1)) ∧
    bodyResult base u v table suffix .first = encodeWord (n + Q + 2 * (e + 1)) ∧
    bodyResult base u v table suffix .last = encodeWord (n + Q + 2 * (e + 1) + 1) := by
  rw [bodyResult_eq base u v table suffix ready]
  have hm : n + (e + 1) = (n + e) + 1 := by omega
  have hf : n + Q + 2 * (e + 1) = (n + Q + 2 * e) + 1 + 1 := by omega
  have hl : n + Q + 2 * (e + 1) + 1 = (n + Q + 2 * e + 1) + 1 + 1 := by omega
  simp [resultTapes, middle, first, last, hm, hf, encodeWord_succ]

theorem rowPayload_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (middle first last : Nat)
    (hm : base .middle = encodeWord middle) (hf : base .first = encodeWord first)
    (hl : base .last = encodeWord last) :
    rowPayload base u v table suffix = rowBits u middle first last v table := by
  simp [rowPayload, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput, rowField,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, hm, hf, hl,
    rowBits, tableBits, encodeWords, List.append_assoc]

theorem bodyBudget_le {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (hu : u < n) (hv : v < n) (he : e ≤ Q)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyBudget base u v table suffix ≤ 100 * (n + 3 * Q + q * (q + 1) + 1) := by
  have ht : (tableBits table).length ≤ q * (q + 1) :=
    GameEncodingSize.tableBits_length_le table
  simp [bodyBudget, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.copiedLength, rowField,
    afterDrainV, afterDrainU, afterRows, MachineFieldTemplate.outputTapes,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, middle, first, last] at *
  omega

end DFVSGames.Explicit.MachineSubdivisionBodySpec

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RuntimeSpace
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceRuntimeSpace

open Turing Complexity
open scoped BigOperators

attribute [local instance] FinTM2.kFin

theorem step_configurationLength (tm : FinTM2) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    configurationLength tm b ≤ configurationLength tm a +
      Fintype.card tm.K * Runtime.programPushBound tm := by
  calc
    _ ≤ ∑ k : tm.K, ((a.stk k).length + Runtime.programPushBound tm) :=
      Finset.sum_le_sum (fun k _ => Runtime.stepStackLength tm k a b transition)
    _ = _ := by simp [configurationLength, Finset.sum_add_distrib]

theorem execution_configurationLength (tm : FinTM2) {start finish : tm.Cfg}
    {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    configurationLength tm finish ≤ configurationLength tm start +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) :=
  Runtime.executionSizeBound tm.step (configurationLength tm)
    (Fintype.card tm.K * Runtime.programPushBound tm) (step_configurationLength tm) run

theorem prefix_configurationLength (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    {finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish) budget) :
    configurationLength tm finish ≤ input.length +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) := by
  simpa only [initial_configurationLength] using execution_configurationLength tm run

theorem finishCost_le_of_prefix (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    {finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step (initList tm input) (some finish) budget)
    (clearKeys : List tm.K) (accumulator output : tm.K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : tm.K → List Bool) (outputEmpty : base output = [])
    (sameLengths : ∀ k, (base k).length = (finish.stk k).length) :
    SourceRuntimeFinish.finishCost clearKeys accumulator base ≤ input.length +
      budget * (Fintype.card tm.K * Runtime.programPushBound tm) + clearKeys.length + 2 := by
  rw [SourceRuntimeFinish.finishCost_eq_totalLength clearKeys accumulator output
    keepAccumulator keepOutput covers base outputEmpty,
    totalLength_eq_configurationLength tm finish base sameLengths]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (prefix_configurationLength tm input run) clearKeys.length) 2

def prefixAndFinishInTime (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (time : Polynomial Nat) {middle finish : tm.Cfg}
    (prefixRun : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some middle) (time.eval input.length))
    (clearKeys : List tm.K) (accumulator output : tm.K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : tm.K → List Bool) (outputEmpty : base output = [])
    (sameLengths : ∀ k, (base k).length = (middle.stk k).length)
    (finishRun : StateTransition.EvalsToInTime tm.step middle (some finish)
      (SourceRuntimeFinish.finishCost clearKeys accumulator base)) :
    StateTransition.EvalsToInTime tm.step (initList tm input) (some finish)
      ((completedTime tm clearKeys.length time).eval input.length) := by
  have joined := StateTransition.EvalsToInTime.trans tm.step _ _ _ _ _ prefixRun finishRun
  have hc := finishCost_le_of_prefix tm input prefixRun clearKeys accumulator output
    keepAccumulator keepOutput covers base outputEmpty sameLengths
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  rw [completedTime_eval]
  omega

end DFVSGames.Foundations.Hastad.SourceRuntimeSpace


namespace DFVSGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

theorem sequential_machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (hfirst : FiniteAlphabet first) (hsecond : FiniteAlphabet second) :
    FiniteAlphabet (MachineSequential.machine first second relabel fallback) := by
  intro tape
  rcases tape with tape | tape | tape
  · exact hfirst tape
  · exact hsecond tape
  · exact input_finite second

theorem compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.compose first second fallback).tm := by
  exact sequential_machine first.tm second.tm
    (fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol))
    (second.inputAlphabet.symm fallback) hfirst hsecond

theorem composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.composeBits first second).tm :=
  compose first second false hfirst hsecond

end DFVSGames.Foundations.Complexity.MachineFiniteAlphabet


namespace DFVSGames.Explicit.MachineUniformRun

open Turing DFVSGames.Reduction
open DFVSGames.Foundations Target
open DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad
open MachineUniformProgram

theorem repeated_template (C : Nat) (fields : Fin 4 → List Bool) :
    MachineFieldTemplate.templateOutput (List.replicate C (.copy 3)) fields =
      MachineUniformCopyOrder.copyMajor C (fields 3) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simp only [List.replicate_succ, MachineFieldTemplate.templateOutput,
      List.flatMap_cons, MachineFieldTemplate.tokenOutput,
      MachineUniformCopyOrder.copyMajor, List.flatten_cons] at *
    rw [ih]

theorem template_output (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.templateOutput (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) = outputBits C n q Q body := by
  simp only [tokens, MachineFieldTemplate.templateOutput, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, MachineFieldTemplate.tokenOutput]
  rw [show (List.replicate C (MachineFieldTemplate.Token.copy (3 : Fin 4))).flatMap
      (MachineFieldTemplate.tokenOutput (fun i => afterScale C n q Q body (emitField i))) =
        MachineUniformCopyOrder.copyMajor C (afterScale C n q Q body (emitField 3)) from
      repeated_template C _]
  simp [afterScale, MachineUniformHeaders.resultTapes, emitField, outputBits,
    encodeWords, List.append_assoc]

theorem template_copiedLength (C n q Q : Nat) (body : List Bool) :
    MachineFieldTemplate.copiedLength (tokens C)
      (fun i => afterScale C n q Q body (emitField i)) =
        n + q + C * Q + 3 + C * body.length := by
  simp [MachineFieldTemplate.copiedLength, tokens, afterScale,
    MachineUniformHeaders.resultTapes, emitField, Nat.add_assoc] ; omega

end DFVSGames.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionLoop

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame

theorem rowPayload_eq {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.rowPayload (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) = rowBits Q e edge := by
  rw [MachineSubdivisionBodySpec.rowPayload_eq _ _ _ _ _ (ready Q e edge edges emitted)
    (n + e) (n + Q + 2 * e) (n + Q + 2 * e + 1) rfl rfl rfl]
  simp only [MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem bodyResult_eq_frame {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.bodyResult (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) =
      frame Q (e + 1) edges (emitted ++ rowBits Q e edge) := by
  have indices := MachineSubdivisionBodySpec.result_indices
    (afterGuard Q e edge edges emitted) edge.source.val edge.target.val edge.permutation
    (bodyBits edges) (ready Q e edge edges emitted) n Q e rfl rfl rfl
  funext tape
  cases tape with
  | middle => exact indices.1
  | first => exact indices.2.1
  | last => exact indices.2.2
  | input => exact MachineSubdivisionBodySpec.result_input _ _ _ _ _ (ready Q e edge edges emitted)
  | accumulator =>
    rw [MachineSubdivisionBodySpec.result_accumulator _ _ _ _ _ (ready Q e edge edges emitted),
      rowPayload_eq]
    simp [afterGuard, frame, List.reverse_append]
  | _ =>
    rw [MachineSubdivisionBodySpec.bodyResult_eq _ _ _ _ _ (ready Q e edge edges emitted)]
    simp [MachineSubdivisionBodySpec.resultTapes, afterGuard, frame,
      MachineSubdivisionInit.resultTapes]

end DFVSGames.Explicit.MachineSubdivisionLoop


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineBinaryNameMachine
attribute [-instance] _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineOutputContract

open DFVSGames.Foundations
open Target
open scoped BigOperators

namespace SimpleBipartite

variable {q : Nat} {game : Instance q} (presentation : SimpleBipartite game)

theorem toBipartiteGame_count (labeling : Fin game.vertices → Fin q) :
    presentation.toBipartiteGame.satisfiedCount
      (fun v => labeling v.val) (fun v => labeling v.val) =
      countSatisfied labeling game.constraints := by
  have count := Integration.GapSemantics.countSatisfied_ofFn labeling
    (fun i : Fin game.constraints.length => game.constraints[i])
  simp only [Fin.getElem_fin, List.ofFn_getElem] at count
  rw [count]
  unfold BipartiteGame.satisfiedCount
  apply Finset.sum_congr rfl
  intro e _
  simp [toBipartiteGame, permutationEquiv, Constraint.satisfied]
  rfl

theorem toBipartiteGame_count_merge
    (left : {v : Fin game.vertices // presentation.side v = false} → Fin q)
    (right : {v : Fin game.vertices // presentation.side v = true} → Fin q) :
    presentation.toBipartiteGame.satisfiedCount left right =
      countSatisfied (presentation.mergeLabelings left right) game.constraints := by
  simpa only [mergeLabelings_left, mergeLabelings_right] using
    presentation.toBipartiteGame_count (presentation.mergeLabelings left right)

theorem toBipartiteGame_maxSatisfied :
    presentation.toBipartiteGame.maxSatisfied =
      Integration.InstanceValue.maxSatisfied game := by
  classical
  apply Nat.le_antisymm
  · unfold BipartiteGame.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [presentation.toBipartiteGame_count_merge labeling.1 labeling.2]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied _ _
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    rw [← presentation.toBipartiteGame_count labeling]
    exact BipartiteGame.satisfiedCount_le_maxSatisfied _ _ _

theorem toBipartiteGame_value :
    presentation.toBipartiteGame.value = Integration.InstanceValue.value game := by
  unfold BipartiteGame.value Integration.InstanceValue.value
  rw [presentation.toBipartiteGame_maxSatisfied]
  simp

end SimpleBipartite

structure BinaryGapReduction (ε δ : ℝ) where
  alphabet : Nat
  alphabetAtLeastTwo : 2 ≤ alphabet
  dimension : Nat
  dimensionPositive : 1 ≤ dimension
  coordinates : Fin alphabet ≃ Integration.BinaryLinear.Vector dimension
  construct : List Bool → Instance alphabet
  simpleBipartite : ∀ input, SimpleBipartite (construct input)
  translations : ∀ input,
    Integration.TranslationTarget.IsTranslationInstance coordinates (construct input)
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    Complexity.gameBits construct
  finiteAlphabet : Complexity.MachineFiniteAlphabet.FiniteAlphabet computation.tm
  completeness : ∀ input, BinaryLanguage.language input →
    ∃ labeling, 1 - ε ≤
      (countSatisfied labeling (construct input).constraints : ℝ) /
        (construct input).constraints.length
  soundness : ∀ input, ¬BinaryLanguage.language input →
    ∀ labeling, (countSatisfied labeling (construct input).constraints : ℝ) /
      (construct input).constraints.length ≤ δ

namespace BinaryGapReduction

variable {ε δ : ℝ} (reduction : BinaryGapReduction ε δ)

theorem occurrence_count_positive (input : List Bool) :
    0 < (reduction.construct input).constraints.length :=
  (reduction.construct input).constraintCount_positive

end BinaryGapReduction
end DFVSGames.Explicit.MachineOutputContract

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ProductTarget
attribute [-instance] _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceModule _root_.OAI.DFVSGames.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionCorrespondence

open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open MachineSubdivisionLoopFrame

theorem translations_involutive {q s : Nat}
    (coordinates : Fin q ≃ Integration.BinaryLinear.Vector s) (H : Instance q)
    (translations : Integration.TranslationTarget.IsTranslationInstance coordinates H) :
    Involutive H := by
  intro e
  apply inverseTable_eq
  apply Vector.ext
  intro i hi
  apply coordinates.injective
  obtain ⟨shift, law⟩ := translations H.constraints[e] (List.getElem_mem e.isLt)
  have h := law (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)])
  rw [H.constraints[e].permutation.rightInverse] at h
  have cancel : shift + shift = 0 := by
    ext j
    simp [CharTwo.add_self_eq_zero]
  have doubled := congrArg (fun x => x + shift) h
  have inverseLaw : coordinates (H.constraints[e].permutation.inverseImages[(⟨i, hi⟩ : Fin q)]) =
      coordinates ⟨i, hi⟩ + shift := by
    simpa only [add_assoc, cancel, add_zero] using doubled.symm
  exact inverseLaw.trans (law ⟨i, hi⟩).symm

end DFVSGames.Explicit.MachineSubdivisionCorrespondence


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Product
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Explicit.ProductPaddedOutput

open DFVSGames.Foundations
open Target
open MachineOutputContract
open ProductTarget
open scoped BigOperators

namespace Embedded

variable {L R E : Type*} {q N M : ℕ}


variable [Fintype L] [Fintype R] [Fintype E]

omit [Fintype L] [Fintype R] in
theorem count (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M)
    (labeling : Fin N → Fin q) :
    countSatisfied labeling (render G vertices edges hM).constraints =
      G.satisfiedCount (fun x => labeling (vertices (Sum.inl x)))
        (fun y => labeling (vertices (Sum.inr y))) := by
  classical
  change countSatisfied labeling (List.ofFn (row G vertices edges)) = _
  rw [Integration.GapSemantics.countSatisfied_ofFn]
  unfold BipartiteGame.satisfiedCount
  apply Fintype.sum_equiv edges
  intro i
  simp [row, Constraint.satisfied, fullTable]

theorem maxSatisfied [Nonempty (Fin q)] (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    Integration.InstanceValue.maxSatisfied (render G vertices edges hM) = G.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · unfold Integration.InstanceValue.maxSatisfied
    apply Finset.sup_le
    intro labeling _
    change Fin N → Fin q at labeling
    exact (count G vertices edges hM labeling).le.trans
      (G.satisfiedCount_le_maxSatisfied _ _)
  · obtain ⟨left, right, hmax⟩ := G.maxSatisfied_attained
    have hcount := count G vertices edges hM (extendLabelings vertices left right)
    simp only [extendLabelings_left, extendLabelings_right, hmax] at hcount
    rw [← hcount]
    exact Integration.InstanceValue.countSatisfied_le_maxSatisfied
      (render G vertices edges hM) (extendLabelings vertices left right)

theorem value [Nonempty (Fin q)] (G : BipartiteGame L R E (Fin q))
    (vertices : (L ⊕ R) ↪ Fin N) (edges : Fin M ≃ E) (hM : 0 < M) :
    Integration.InstanceValue.value (render G vertices edges hM) = G.value := by
  unfold Integration.InstanceValue.value BipartiteGame.value
  rw [maxSatisfied, render_length]
  have hc : M = Fintype.card E := by simpa using Fintype.card_congr edges
  rw [hc]

end Embedded

end DFVSGames.Explicit.ProductPaddedOutput


namespace DFVSGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

theorem tapes_other (index source destination p : K)
    (hi : p ≠ index) (hs : p ≠ source) (hd : p ≠ destination)
    (base : K → List Bool) (counter input output : List Bool) :
    tapes index source destination base counter input output p = base p := by
  simp [tapes, hi, hs, hd]

theorem update_index (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) index replacement =
      tapes index source destination base replacement input output := by
  funext p
  by_cases hi : p = index
  · subst p; simp [tapes, his, hid]
  · by_cases hs : p = source
    · subst p; by_cases hs : source = destination <;> simp [tapes, hi, hs, Ne.symm hid]
    · by_cases hd : p = destination
      · subst p; simp [tapes, hi]
      · simp [tapes, hi, hs, hd]

theorem update_source (index source destination : K) (hsd : source ≠ destination)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output) source replacement =
      tapes index source destination base counter replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [tapes, hsd]
  · by_cases hd : p = destination
    · subst p; simp [tapes, hs]
    · simp [tapes, hs, hd]

theorem update_destination (index source destination : K)
    (base : K → List Bool) (counter input output replacement : List Bool) :
    Function.update (tapes index source destination base counter input output)
      destination replacement = tapes index source destination base counter input replacement := by
  simp [tapes]

end DFVSGames.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLookupSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat)
    (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord 0 ++ indexSuffix)
    (encodeWords (values.drop (index + 1)) ++ workSuffix) (encodeWord value ++ output)

end DFVSGames.Foundations.Complexity.MachinePreservingLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAffineLookup
attribute [-instance] _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) : K → List Bool :=
  MachinePreservingLookup.finalTapes tape base values index value
    (base (tape 1)) (base (tape 2)) (base (tape 3))

theorem initialTapes_eq_update (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (i : Nat) :
    MachinePreservingLookup.initialTapes tape base i
      (base (tape 1)) (base (tape 2)) (base (tape 3)) =
      Function.update base (tape 1) (encodeWord i ++ base (tape 1)) := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  funext k
  by_cases h₁ : k = tape 1
  · subst k
    simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
      hd 1 2 (by decide), hd 1 3 (by decide)]
  · by_cases h₂ : k = tape 2
    · subst k
      simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁,
        hd 2 3 (by decide)]
    · by_cases h₃ : k = tape 3
      · subst k
        simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁]
      · simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁, h₂, h₃]

theorem finalTapes_other (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) (k : K)
    (h₁ : k ≠ tape 1) (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) :
    finalTapes tape base values index value k = base k :=
  MachineLookup.tapes_other _ _ _ _ h₁ h₂ h₃ _ _ _ _

theorem finalTapes_output (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) :
    finalTapes tape base values index value (tape 3) = encodeWord value ++ base (tape 3) :=
  MachineLookup.tapes_destination _ _ _ _ _ _ _

end DFVSGames.Foundations.Complexity.MachineAffineLookup


namespace DFVSGames.Explicit.MachineProductGather

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def finalTapes (values : List Nat) (coefficient : Nat) :
    (width : Nat) → (Tape width → K) → (Fin width → Nat) →
      (Fin width → Nat) → (Fin width → Nat) → (K → List Bool) → K → List Bool
  | 0, _, _, _, _, base => base
  | width + 1, placement, indices, offsets, fields, base =>
    finalTapes values coefficient width (placement ∘ shift width)
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
        (coefficient * indices 0 + offsets 0) (fields 0))

theorem finalTapes_other (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (indices offsets fields : Fin width → Nat)
    (base : K → List Bool) (k : K)
    (query : k ≠ placement (.inl 1)) (scan : k ≠ placement (.inl 2))
    (outputs : ∀ i, k ≠ placement (.inr (.inr i))) :
    finalTapes values coefficient width placement indices offsets fields base k = base k := by
  induction width generalizing base with
  | zero => rfl
  | succ width ih =>
    rw [finalTapes]
    rw [ih (placement ∘ shift width) (fun i => indices i.succ)
      (fun i => offsets i.succ) (fun i => fields i.succ) _ query scan
      (fun i => outputs i.succ)]
    exact MachineAffineLookup.finalTapes_other _ _ _ _ _ k query scan (outputs 0)

theorem finalTapes_field (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (i : Fin width) :
    finalTapes values coefficient width placement indices offsets fields base
      (placement (.inr (.inr i))) =
      encodeWord (fields i) ++ base (placement (.inr (.inr i))) := by
  induction width generalizing base with
  | zero => exact Fin.elim0 i
  | succ width ih =>
    have hd (a b : Tape (width + 1)) (hne : a ≠ b) : placement a ≠ placement b :=
      fun h => hne (distinct h)
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    refine Fin.cases ?_ (fun j => ?_) i
    · change finalTapes values coefficient width (placement ∘ shift width)
        (fun j => indices j.succ) (fun j => offsets j.succ) (fun j => fields j.succ)
        mid (placement (.inr (.inr 0))) = _
      rw [finalTapes_other values coefficient width _ _ _ _ mid _
        (hd _ _ (by simp [shift])) (hd _ _ (by simp [shift]))
        (fun j => hd _ _ (by simp [shift, Fin.ext_iff]))]
      exact MachineAffineLookup.finalTapes_output _ _ _ _ _
    · change finalTapes values coefficient width (placement ∘ shift width)
        (fun j => indices j.succ) (fun j => offsets j.succ) (fun j => fields j.succ)
        mid ((placement ∘ shift width) (.inr (.inr j))) = _
      rw [ih (placement ∘ shift width) (distinct.comp (shift_injective width))
        (fun j => indices j.succ) (fun j => offsets j.succ) (fun j => fields j.succ) mid j]
      congr 1
      exact MachineAffineLookup.finalTapes_other (placement ∘ lookupRole width) base values
        (coefficient * indices 0 + offsets 0) (fields 0)
        (placement (.inr (.inr j.succ)))
        (hd _ _ (by simp [lookupRole])) (hd _ _ (by simp [lookupRole]))
        (hd _ _ (by simp [lookupRole, Fin.ext_iff]))

end DFVSGames.Explicit.MachineProductGather


namespace DFVSGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .copyDrain => Reduction.MachineTransfer.loopAt (slots 1) (slots 4) id false
      (labels .copyDrain) (some (labels .copyFork))
  | .copyFork => MachineCopy.forkLoop (slots 4) (slots 1) (slots 3) false
      (labels .copyFork) (some (labels .seed))
  | .seed => .push (slots 2) (fun _ => false) (.goto fun _ => labels .guard)
  | .guard => MachineUnaryCounter.guard (slots 3) (labels .scan) (labels .finish)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore)
  | .emitFalse => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () false
  | .emitTrue => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () true
  | .restore => Reduction.MachineTransfer.loopAt (slots 4) (slots 0) id false
      (labels .restore) (some (labels .guard))
  | .finish => .pop (slots 3) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 2) exit)

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

end DFVSGames.Foundations.Complexity.MachineUnaryMultiply

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineUnaryAdd
attribute [-instance] _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineRadixStep

open Turing

variable {K Λ σ : Type}

variable [DecidableEq K]

def statement (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .multiply label => MachineUnaryMultiply.statement (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) label
  | .digitDrain => Reduction.MachineTransfer.loopAt (slots 2) (slots 5) id false
      (labels .digitDrain) (some (labels .digitFork))
  | .digitFork => MachineCopy.forkLoop (slots 5) (slots 2) (slots 4) false
      (labels .digitFork) (some (labels .add))
  | .add => MachineUnaryAddAt.loop (slots 4) (slots 3) (labels .add) (some (labels .finish))
  | .finish => .pop (slots 4) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 3) exit)

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

end DFVSGames.Foundations.Complexity.MachineRadixStep


namespace DFVSGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

def statement (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ) :
    Label width → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => .push (slots (.inl 1)) (fun _ => false)
      (.load (fun state => (state.1, none)) (.goto fun _ => labels (entryLabel width 0)))
  | .radix i inner => MachineRadixStep.statement (radixSlots slots i)
      (fun l => labels (.radix i l)) (some (labels (.clear i))) inner
  | .clear i => drainLoop (slots (.inl (accumulator (parity i.val))))
      (labels (.clear i)) (some (labels (entryLabel width (i.val + 1))))
  | .finishDrain => Reduction.MachineTransfer.loopAt
      (slots (.inl (accumulator (parity width)))) (slots (.inl 5)) id false
      (labels .finishDrain) (some (labels .finishRestore))
  | .finishRestore => Reduction.MachineTransfer.loopAt (slots (.inl 5)) (slots (.inl 3)) id false
      (labels .finishRestore) exit

theorem drainTrace (tape : K) (loopLabel : Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLoop : p loopLabel = drainLoop tape loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[n + 1]
      (some ⟨some loopLabel, ((ambient, ()), register),
        Function.update base tape (encodeWord n ++ suffix)⟩) =
      some ⟨exit, ((ambient, ()), none), Function.update base tape suffix⟩ := by
  induction n generalizing register with
  | zero =>
    change some (TM2.stepAux (p loopLabel) _ _) = _
    rw [atLoop]
    cases exit <;> simp [drainLoop, TM2.stepAux, encodeWord, Reduction.MachineTransfer.exitAt]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step p))^[n + 1]
      (some (TM2.stepAux (p loopLabel) _ _)) = _
    rw [atLoop]
    simp only [drainLoop, TM2.stepAux, Function.update_self, encodeWord,
      List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
      Option.getD_some, Function.update_idem]
    exact ih (some true)

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

end DFVSGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductField
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

def gathered (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) : K → List Bool :=
  MachineProductGather.finalTapes values coefficient width (gatherSlots slots)
    indices offsets fields base

def evaluated (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  MachineHorner.resultTapes (hornerSlots slots)
    (gathered slots values coefficient indices offsets fields base) value

def emitted (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  tapesAt (slots (.inr 5)) (slots (.inr 6))
    (evaluated slots values coefficient indices offsets fields base value) []
    ((encodeWord value).reverse ++ base (slots (.inr 6)))

def finalTapes (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  MachineDrainMany.finalTapes (clearTapes slots)
    (emitted slots values coefficient indices offsets fields base value)

def steps (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (radix : Nat) (digits : Nat → Nat) : Nat :=
  MachineProductGather.steps values coefficient width indices offsets +
    MachineHorner.steps radix digits width + (MachineHorner.value radix digits width + 2) +
    MachineDrainMany.steps (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base
        (MachineHorner.value radix digits width))

theorem gathered_extra (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (i : Fin 7) :
    gathered slots values coefficient indices offsets fields base (slots (.inr i)) =
      base (slots (.inr i)) := by
  apply MachineProductGather.finalTapes_other
  · apply slots.injective.ne; simp []
  · apply slots.injective.ne; simp []
  · intro j; apply slots.injective.ne; simp []

end DFVSGames.Explicit.MachineProductField


namespace DFVSGames.Explicit.MachineProductGather

open DFVSGames.Foundations.Complexity

variable {K : Type} [DecidableEq K]

theorem affine_final_length (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (values : List Nat) (index value : Nat) (selected : values[index]? = some value)
    (base : K → List Bool) (k : K) :
    (MachineAffineLookup.finalTapes tape base values index value k).length ≤
      (base k).length + (encodeWords values).length + 1 := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  have hov := MachineLookupSpec.output_length_le values index value selected
  have hdrop : (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
    have split : encodeWords (values.take (index + 1)) ++
        encodeWords (values.drop (index + 1)) = encodeWords values := by
      rw [← encodeWords_append, List.take_append_drop]
    have h := congrArg List.length split
    simp only [List.length_append] at h
    omega
  by_cases h1 : k = tape 1
  · subst k
    simp only [MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes_index _ _ _ (hd 1 2 (by decide)) (hd 1 3 (by decide)),
      List.length_append, encodeWord_length]
    omega
  · by_cases h2 : k = tape 2
    · subst k
      simp only [MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
        MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide)), List.length_append]
      omega
    · by_cases h3 : k = tape 3
      · subst k
        rw [MachineAffineLookup.finalTapes_output, List.length_append]
        omega
      · rw [MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h1 h2 h3]
        omega

theorem finalTapes_length (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (k : K) :
    (finalTapes values coefficient width placement indices offsets fields base k).length ≤
      (base k).length + width * ((encodeWords values).length + 1) := by
  induction width generalizing base with
  | zero => simp [finalTapes]
  | succ width ih =>
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    have first := affine_final_length (placement ∘ lookupRole width)
      (distinct.comp (lookupRole_injective width)) values
      (coefficient * indices 0 + offsets 0) (fields 0) (selected 0) base k
    have rest := ih (placement ∘ shift width) (distinct.comp (shift_injective width))
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (fun i => selected i.succ) mid
    change (finalTapes values coefficient width (placement ∘ shift width)
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ) mid k).length ≤ _
    rw [Nat.add_mul, Nat.one_mul]
    dsimp only [mid] at rest
    dsimp only [mid]
    omega

end DFVSGames.Explicit.MachineProductGather


namespace DFVSGames.Explicit.MachineProductField

open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction.MachineTransfer

variable {K : Type} [DecidableEq K] {width : Nat}

theorem gathered_frame (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (k : K) (outside : k ∉ clearTapes slots) :
    gathered slots values coefficient indices offsets fields base k = base k := by
  rw [mem_clearTapes] at outside
  apply MachineProductGather.finalTapes_other
  · exact fun h => outside (Or.inl h)
  · exact fun h => outside (Or.inr (Or.inl h))
  · intro i h; exact outside (Or.inr (Or.inr ⟨i, h⟩))

theorem finalTapes_eq (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (ready : Ready slots base) (value : Nat) :
    finalTapes slots values coefficient indices offsets fields base value =
      Function.update base (slots (.inr 6))
        ((encodeWord value).reverse ++ base (slots (.inr 6))) := by
  funext k
  rw [finalTapes, MachineDrainMany.finalTapes_apply]
  by_cases member : k ∈ clearTapes slots
  · have notOutput : k ≠ slots (.inr 6) := by
      intro h; subst k; exact extra_not_mem_clearTapes slots 6 member
    simp [member, Function.update_of_ne notOutput, ready.empty_clearTapes slots base k member]
  · rw [ite_eq_right member]
    by_cases output : k = slots (.inr 6)
    · subst k
      simp [emitted, tapesAt]
    · by_cases field : k = slots (.inr 5)
      · subst k
        simp [emitted, tapesAt, output, ready.output]
      · have frame := gathered_frame slots values coefficient indices offsets fields base k member
        simp only [emitted, tapesAt, Function.update_of_ne output, Function.update_of_ne field,
          evaluated, MachineHorner.resultTapes]
        change Function.update (gathered slots values coefficient indices offsets fields base)
          (slots (.inr 5)) _ k = base k
        rw [Function.update_of_ne field, frame]

theorem emitted_clear_length (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : Ready slots base) (value : Nat)
    (k : K) (member : k ∈ clearTapes slots) :
    (emitted slots values coefficient indices offsets fields base value k).length ≤
      width * ((encodeWords values).length + 1) := by
  have notExtra (i : Fin 7) : k ≠ slots (.inr i) := by
    intro h; subst k; exact extra_not_mem_clearTapes slots i member
  have h := MachineProductGather.finalTapes_length values coefficient width (gatherSlots slots)
    (gatherSlots slots).injective indices offsets fields selected base k
  rw [ready.empty_clearTapes slots base k member, List.length_nil, Nat.zero_add] at h
  simpa only [emitted, tapesAt, Function.update_of_ne (notExtra 6),
    Function.update_of_ne (notExtra 5), evaluated, MachineHorner.resultTapes,
    show hornerSlots slots (.inl 3) = slots (.inr 5) from rfl,
    Function.update_of_ne (notExtra 5), gathered] using h

theorem cleanup_steps_le (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : Ready slots base) (value : Nat) :
    MachineDrainMany.steps (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base value) ≤
      (width + 2) * (width * ((encodeWords values).length + 1) + 1) := by
  have sumBound : MachineDrainMany.lengthSum (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base value) ≤
      (clearTapes slots).length * (width * ((encodeWords values).length + 1)) := by
    have hs := List.sum_le_card_nsmul
      ((clearTapes slots).map (fun k => (emitted slots values coefficient indices offsets fields base value k).length))
      (width * ((encodeWords values).length + 1)) (by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
        exact emitted_clear_length slots values coefficient indices offsets fields selected base ready value k hk)
    simpa [MachineDrainMany.lengthSum, nsmul_eq_mul] using hs
  have h := MachineDrainMany.steps_le (clearTapes slots)
    (emitted slots values coefficient indices offsets fields base value)
  rw [clearTapes_length] at sumBound h
  rw [Nat.mul_add, Nat.mul_one]
  omega

end DFVSGames.Explicit.MachineProductField


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

def instruction (slots : MachineHorner.Layout (exponent + 1) ↪ K) (output : K)
    (labels : Label exponent → Λ) (exit : Option Λ) :
    Label exponent → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl l => MachineHorner.statement slots (fun x => labels (.inl x))
      (some (labels (.inr ()))) l
  | .inr _ => loopAt (slots (.inl 3)) output id false (labels (.inr ())) exit

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

end DFVSGames.Explicit.MachineProductPower


namespace DFVSGames.Foundations.Complexity.MachineOdometerInit
open Turing

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def statement (tape : Tape k → K) (labels : Label k → Λ) (exit : Option Λ) :
    Label k → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .seed j => .push (tape (.current j)) (fun _ => false)
      (.goto (fun _ => labels (.copyOut j)))
  | .copyOut j => Reduction.MachineTransfer.loopAt (tape .radix) (tape .scratch)
      id false (labels (.copyOut j)) (some (labels (.copyBack j)))
  | .copyBack j => MachineCopy.forkLoop (tape .scratch) (tape .radix) (tape (.remaining j))
      false (labels (.copyBack j)) (some (labels (.trim j)))
  | .trim j => .pop (tape (.remaining j)) (fun state _ => state)
      (.goto (fun _ => labelAt labels (j.val+1)))
  | .done => .load (fun state => (state.1,none))
      (Reduction.MachineTransfer.exitAt (tape .radix) exit)

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

end DFVSGames.Foundations.Complexity.MachineOdometerInit

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

theorem finishStep (source : K) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFinish : program label = finish source exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some label, (ambient, register), base⟩ =
      some ⟨exit, (ambient, none), base⟩ := by
  change some (TM2.stepAux (program label) (ambient, register) base) = _
  rw [atFinish]
  cases exit <;> simp [finish, Reduction.MachineTransfer.exitAt, TM2.stepAux]

theorem sequenceTrace (source : K) (destination : Nat → K)
    (start loopLabel : Nat → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (atStart : ∀ r, r < values.length →
      program (start (offset + r)) = fieldStart (destination (offset + r)) (loopLabel (offset + r)))
    (atLoop : ∀ r, r < values.length → program (loopLabel (offset + r)) =
      fieldLoop source (destination (offset + r)) (loopLabel (offset + r))
        (some (start (offset + r + 1))))
    (atDone : program (start (offset + values.length)) = finish source exit)
    (hinput : base source = encodeWords values ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[values.sum + 2 * values.length + 1]
      (some ⟨some (start offset), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), sequenceTapes source destination base offset values suffix⟩ := by
  induction values generalizing offset base register with
  | nil =>
    simpa only [List.sum_nil, List.length_nil, Nat.mul_zero, Nat.zero_add,
      Nat.add_zero, Function.iterate_one, MachineComposition.advance_some, sequenceTapes]
      using finishStep source (start offset) exit program atDone base ambient register
  | cons n rest ih =>
    have hr0 : 0 < (n :: rest).length := by simp
    have hsep0 : source ≠ destination offset := by simpa using hsep 0 hr0
    have hs0 : program (start offset) = fieldStart (destination offset) (loopLabel offset) := by
      simpa using atStart 0 hr0
    have hl0 : program (loopLabel offset) = fieldLoop source (destination offset)
        (loopLabel offset) (some (start (offset + 1))) := by simpa using atLoop 0 hr0
    have hin : base source = encodeWord n ++ (encodeWords rest ++ suffix) := by
      simpa only [encodeWords, List.append_assoc] using hinput
    let nextBase := afterField source (destination offset) base n (encodeWords rest ++ suffix)
    have hfirst := (fieldInTime source (destination offset) hsep0 (start offset)
      (loopLabel offset) (some (start (offset + 1))) program hs0 hl0 base n
      (encodeWords rest ++ suffix) hin ambient register).evals_in_steps
    change (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some (start offset), (ambient, register), base⟩) =
      some ⟨some (start (offset + 1)), (ambient, none), nextBase⟩ at hfirst
    have hsep' : ∀ r, r < rest.length → source ≠ destination (offset + 1 + r) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsep (r + 1) (by simp; omega)
    have hs' : ∀ r, r < rest.length → program (start (offset + 1 + r)) =
        fieldStart (destination (offset + 1 + r)) (loopLabel (offset + 1 + r)) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atStart (r + 1) (by simp; omega)
    have hl' : ∀ r, r < rest.length → program (loopLabel (offset + 1 + r)) =
        fieldLoop source (destination (offset + 1 + r)) (loopLabel (offset + 1 + r))
          (some (start (offset + 1 + r + 1))) := by
      intro r hr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atLoop (r + 1) (by simp; omega)
    have hd' : program (start (offset + 1 + rest.length)) = finish source exit := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atDone
    have hin' : nextBase source = encodeWords rest ++ suffix := by
      simp [nextBase, afterField, hsep0]
    rw [show (n :: rest).sum + 2 * (n :: rest).length + 1 =
      (rest.sum + 2 * rest.length + 1) + (n + 2) by simp; omega]
    rw [Function.iterate_add_apply, hfirst,
      ih nextBase (offset + 1) hsep' hs' hl' hd' hin' none]
    rfl

def sequenceInTime (source : K) (destination : Nat → K)
    (start loopLabel : Nat → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (offset : Nat) (values : List Nat) (suffix : List Bool)
    (hsep : ∀ r, r < values.length → source ≠ destination (offset + r))
    (atStart : ∀ r, r < values.length →
      program (start (offset + r)) = fieldStart (destination (offset + r)) (loopLabel (offset + r)))
    (atLoop : ∀ r, r < values.length → program (loopLabel (offset + r)) =
      fieldLoop source (destination (offset + r)) (loopLabel (offset + r))
        (some (start (offset + r + 1))))
    (atDone : program (start (offset + values.length)) = finish source exit)
    (hinput : base source = encodeWords values ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (start offset), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), sequenceTapes source destination base offset values suffix⟩)
      (values.sum + 2 * values.length + 1) where
  steps := values.sum + 2 * values.length + 1
  evals_in_steps := sequenceTrace source destination start loopLabel exit program base offset
    values suffix hsep atStart atLoop atDone hinput ambient register
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.Hastad.SourceFieldArray


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

theorem inputBits_length (input : Input) :
    (inputBits input).length = input.«variables» + input.equations.length + 2 +
      (encodeWords (input.equations.flatMap equationWords)).length := by
  simp only [inputBits, inputWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

theorem inputBits_length_le (input : Input) :
    (inputBits input).length ≤ input.«variables» + input.equations.length + 2 +
      input.equations.length * (3 * input.«variables» + 2) := by
  rw [inputBits_length]
  exact Nat.add_le_add_left (equationsBits_length_le input.equations) _

theorem inputBits_length_ge_variables (input : Input) :
    input.«variables» ≤ (inputBits input).length := by rw [inputBits_length]; omega

theorem inputBits_length_ge_equations (input : Input) :
    input.equations.length ≤ (inputBits input).length := by rw [inputBits_length]; omega

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

theorem stepAux_increment_succ (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d r : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix) =
      ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord, List.replicate_succ, update_current_inline_MachineTupleOdometer, update_remaining_inline_MachineTupleOdometer]

theorem stepAux_increment_zero (current remaining : K) (distinct : current ≠ remaining)
    (doneLabel resetLabel : Λ) (base : K → List Bool) (d : ℕ)
    (currentSuffix remainingSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (increment current remaining doneLabel resetLabel) (ambient, register)
      (digitTapes current remaining base d 0 currentSuffix remainingSuffix) =
      ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  simp [increment, TM2.stepAux, digitTapes, MachineUnaryAddAt.unaryTapes,
    distinct, encodeWord]

theorem incrementStep_succ (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d (r + 1) currentSuffix remainingSuffix⟩ =
      some ⟨some doneLabel, (ambient, none),
        digitTapes current remaining base (d + 1) r currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_succ current remaining distinct]

theorem incrementStep_zero (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ =
      some ⟨some resetLabel, (ambient, none),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩ := by
  change some (TM2.stepAux (program checkLabel) (ambient, register) _) = _
  rw [atCheck, stepAux_increment_zero current remaining distinct]

theorem resetTrace (current remaining : K) (distinct : current ≠ remaining)
    (resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d r : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 1]
      (some ⟨some resetLabel, (ambient, register),
        digitTapes current remaining base d r currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 (d + r) currentSuffix remainingSuffix⟩ :=
  MachineUnaryAddAt.addTrace current remaining distinct resetLabel (some carryLabel)
    program atReset base d r currentSuffix remainingSuffix ambient register

theorem carryTrace (current remaining : K) (distinct : current ≠ remaining)
    (checkLabel doneLabel resetLabel carryLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining doneLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel carryLabel)
    (base : K → List Bool) (d : ℕ) (currentSuffix remainingSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[d + 2]
      (some ⟨some checkLabel, (ambient, register),
        digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) =
      some ⟨some carryLabel, (ambient, none),
        digitTapes current remaining base 0 d currentSuffix remainingSuffix⟩ := by
  rw [show d + 2 = (d + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[d + 1]
    (TM2.step program ⟨some checkLabel, (ambient, register),
      digitTapes current remaining base d 0 currentSuffix remainingSuffix⟩) = _
  rw [incrementStep_zero current remaining distinct checkLabel doneLabel resetLabel
    program atCheck]
  simpa only [Nat.add_zero] using resetTrace current remaining distinct resetLabel carryLabel
    program atReset base d 0 currentSuffix remainingSuffix ambient none

section AscendingCycle

open scoped BigOperators

theorem cycleTrace (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (maximum count : ℕ) (hcount : count ≤ maximum)
    (currentSuffix remainingSuffix : List Bool) (ambient : ℕ → σ)
    (register : ℕ → Option Bool) (base : ℕ → K → List Bool) (cost : ℕ → ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program maximum count
      currentSuffix remainingSuffix ambient register base cost) :
    (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (some (bodyConfiguration current remaining bodyLabel maximum count
        currentSuffix remainingSuffix ambient base)) =
      some (cycleExit current remaining exitLabel maximum
        currentSuffix remainingSuffix ambient base) := by
  induction count with
  | zero =>
    rw [cycleSteps_zero_inline_MachineTupleOdometer, Function.iterate_add_apply, visits 0 (Nat.le_refl 0)]
    simpa only [checkConfiguration, cycleExit, Nat.sub_zero] using
      carryTrace current remaining distinct checkLabel bodyLabel resetLabel exitLabel
        program atCheck atReset (base 0) maximum currentSuffix remainingSuffix
        (ambient 0) (register 0)
  | succ count ih =>
    rw [cycleSteps_succ_inline_MachineTupleOdometer, Function.iterate_add_apply, visits (count + 1) (Nat.le_refl _),
      Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[cycleSteps cost maximum count]
      (TM2.step program ⟨some checkLabel, (ambient (count + 1), register (count + 1)),
        digitTapes current remaining (base (count + 1)) (maximum - (count + 1))
          (count + 1) currentSuffix remainingSuffix⟩) = _
    rw [incrementStep_succ current remaining distinct checkLabel bodyLabel resetLabel
      program atCheck]
    have hnext : maximum - (count + 1) + 1 = maximum - count := by omega
    rw [hnext]
    exact ih (by omega) (fun r hr => visits r (by omega))

def ascendingCycleInTime (current remaining : K) (distinct : current ≠ remaining)
    (bodyLabel checkLabel resetLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atCheck : program checkLabel = increment current remaining bodyLabel resetLabel)
    (atReset : program resetLabel = reset current remaining resetLabel exitLabel)
    (n : ℕ) (hn : 0 < n) (currentSuffix remainingSuffix : List Bool)
    (ambient : ℕ → σ) (register : ℕ → Option Bool) (base : ℕ → K → List Bool)
    (cost : ℕ → ℕ) (B : ℕ)
    (visits : VisitTraces current remaining bodyLabel checkLabel program (n - 1) (n - 1)
      currentSuffix remainingSuffix ambient register base cost)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    StateTransition.EvalsToInTime (TM2.step program)
      (bodyConfiguration current remaining bodyLabel (n - 1) (n - 1)
        currentSuffix remainingSuffix ambient base)
      (some (cycleExit current remaining exitLabel (n - 1)
        currentSuffix remainingSuffix ambient base)) (n * (B + 2)) where
  steps := cycleSteps cost (n - 1) (n - 1)
  evals_in_steps := cycleTrace current remaining distinct bodyLabel checkLabel resetLabel exitLabel
    program atCheck atReset (n - 1) (n - 1) (Nat.le_refl _) currentSuffix remainingSuffix
    ambient register base cost visits
  steps_le_m := by
    have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
      calc
        _ ≤ ∑ _r ∈ Finset.range n, B :=
          Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
        _ = _ := by simp
    have hn' : n - 1 + 1 = n := by omega
    simp only [cycleSteps, hn', Nat.mul_add] at *
    omega

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

namespace DFVSGames.Foundations.Complexity.MachineTupleOdometer
open Turing
open Reduction.MachineTransfer
variable {K Λ σ : Type} [DecidableEq K]

section Nested

open scoped BigOperators

inductive NestedCycle (n : ℕ) (current remaining : ℕ → K) (bodyLabel : Λ)
    (checkLabel resetLabel : ℕ → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) :
    ℕ → Λ → Configuration K Λ σ → Configuration K Λ σ → Type where
  | leaf (exitLabel : Λ) (start finish : Configuration K Λ σ) (count : ℕ)
      (atBody : start.l = some bodyLabel) (atExit : finish.l = some exitLabel)
      (run : (MachineComposition.advance (TM2.step program))^[count] (some start) = some finish) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        0 exitLabel start finish
  | node (depth : ℕ) (exitLabel : Λ) (positive : 0 < n)
      (distinct : current depth ≠ remaining depth)
      (atCheck : program (checkLabel depth) =
        increment (current depth) (remaining depth) bodyLabel (resetLabel depth))
      (atReset : program (resetLabel depth) =
        reset (current depth) (remaining depth) (resetLabel depth) exitLabel)
      (s : CycleSchedule K σ)
      (children : ∀ r : Fin n,
        NestedCycle n current remaining bodyLabel checkLabel resetLabel program
          depth (checkLabel depth)
          (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.base)
          (checkConfiguration (current depth) (remaining depth) (checkLabel depth) (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.register s.base)) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        (depth + 1) exitLabel
        (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (current depth) (remaining depth) exitLabel (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

def steps {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : ℕ :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count
  | .node _ _ _ _ _ _ _ children =>
    cycleSteps (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) (n - 1) (n - 1)
termination_by depth

def LeafBound (B : ℕ) {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : Prop :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count ≤ B
  | .node _ _ _ _ _ _ _ children => ∀ r, LeafBound B (children r)
termination_by depth

theorem trace {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) :
    (MachineComposition.advance (TM2.step program))^[tree.steps] (some start) = some finish := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run => simpa only [steps] using run
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [steps]
    apply cycleTrace (current depth) (remaining depth) distinct bodyLabel (checkLabel depth)
      (resetLabel depth) exitLabel program atCheck atReset (n - 1) (n - 1)
      (Nat.le_refl _) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
    intro r hr
    have hlt : r < n := by omega
    simpa only [dite_eq_left hlt] using ih ⟨r, hlt⟩

theorem steps_le {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ n ^ depth * B + counterOverhead n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simpa only [steps, LeafBound, counterOverhead, pow_zero, Nat.one_mul, Nat.add_zero] using bounded
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [LeafBound] at bounded
    have visits : VisitTraces (current depth) (remaining depth) bodyLabel (checkLabel depth)
        program (n - 1) (n - 1) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
        (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) := by
      intro r hr
      have hlt : r < n := by omega
      simpa only [dite_eq_left hlt] using (children ⟨r, hlt⟩).trace
    have bodyBound : ∀ r, r < n →
        (if hr : r < n then steps (children ⟨r, hr⟩) else 0) ≤
          n ^ depth * B + counterOverhead n depth := by
      intro r hr
      simpa only [dite_eq_left hr] using ih ⟨r, hr⟩ (bounded ⟨r, hr⟩)
    have h := (ascendingCycleInTime (current depth) (remaining depth) distinct bodyLabel
      (checkLabel depth) (resetLabel depth) exitLabel program atCheck atReset n positive
      s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
      (n ^ depth * B + counterOverhead n depth) visits bodyBound).steps_le_m
    change cycleSteps _ (n - 1) (n - 1) ≤ _ at h
    simpa only [steps, counterOverhead, pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc] using h

end NestedCycle

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

theorem steps_le_power {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (hn : 0 < n) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ (B + 2 * depth) * n ^ depth := by
  have h := (tree.steps_le B bounded).trans
    (Nat.add_le_add_left (counterOverhead_le n depth hn) (n ^ depth * B))
  simpa only [Nat.add_mul, Nat.mul_add, Nat.mul_comm] using h

end NestedCycle

end Nested


end DFVSGames.Foundations.Complexity.MachineTupleOdometer


namespace DFVSGames.Foundations.Hastad.SourceOdometerSchedule

open Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

theorem blockPrefix_all {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) :
    blockPrefix (blocks bits) m = allBits bits := by
  rw [blockPrefix_eq_ofFn]
  simp only [blocks, Fin.isLt, ↓reduceDIte, allBits, tupleOrder_snoc]
  simp only [List.flatMap_assoc, List.flatMap_map]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ u)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical accumulator base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (.extra accumulator))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical accumulator base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt accumulator)
      (remaining := remainingAt accumulator) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical accumulator base bits) count rfl rfl hrun
    refine ⟨tree, ?_⟩
    unfold NestedCycle.LeafBound
    exact hcount
  | succ q ih =>
    have hqu : q < u := by omega
    let s : CycleSchedule (Tape u Extra) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (.extra accumulator))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base)
            (checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
              s.ambient s.register s.base), tree.LeafBound B := by
      let d : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c d)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (.extra accumulator)))
        d.val (m - 1 - d.val)
      have hrem : m - 1 - d.val = r.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = d.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = d.val + 1 := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, d.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical accumulator
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c d) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical accumulator childBase childBits =
          checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
            s.ambient s.register s.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_extra, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) s children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
        bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, s,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt accumulator q) (remainingAt accumulator q)
        (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        finalConfiguration (next (q + 1)) canonical accumulator base bits := by
      simp only [cycleExit, finalConfiguration, configuration, s, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt accumulator) (remainingAt accumulator)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
          bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (currentAt accumulator q) (remainingAt accumulator q)
          (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B : ℕ) (base : Tape u Extra → List Bool)
    (bits : (Fin u → Fin m) → List Bool)
    (atCheck : ∀ i, i < u → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < u → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) u bodyLabel canonical base)
      (some (finalConfiguration (next u) canonical accumulator base bits))
      ((B + 2 * u) * m ^ u)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical accumulator
    positive B u (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

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


namespace DFVSGames.Explicit.MachineProductHeaders

open Turing
open DFVSGames.Foundations Target Complexity Hastad
open MachineProductProgram

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

end DFVSGames.Explicit.MachineProductHeaders


namespace DFVSGames.Explicit.MachineProductBounds

open DFVSGames.Foundations.Complexity

variable {K : Type} [DecidableEq K] {width : Nat}

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

def rowCost (slots : MachineProductRow.Layout width ↪ K) (table : List Nat) (coefficient : Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat)
    (fields : MachineProductRow.Command width → Fin width → Nat)
    (digits : MachineProductRow.Command width → Nat → Nat)
    (c : MachineProductRow.Command width) (base : K → List Bool) : Nat :=
  MachineProductField.steps (MachineProductRow.fieldSlots slots c.1) table coefficient indices c.2
    (fields c) base (radices c.1) (digits c)

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

end DFVSGames.Explicit.MachineProductBounds


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineProductFinish
attribute [-instance] _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

def pairEnergy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) : ℝ :=
  ν.expectation fun e => ∑ ω,
    if R e (a (left e) ω) (a (right e) ω)
      then f (left e) ω * f (right e) ω else 0

end
end DFVSGames.Repetition


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Analysis_PrivateFourier
attribute [-instance] _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace DFVSGames.Decoder.PrivateFourier

open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixFourier
open scoped BigOperators Classical

section AffineSlice

variable {E H V : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup H] [Module F2 H]
variable [AddCommGroup V] [Module F2 V]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 H] [FiniteDimensional F2 V]
variable [Fintype (E →ₗ[F2] H)] [Fintype (H →ₗ[F2] E)]
variable [Fintype (V →ₗ[F2] H)]

def frequencyCoset (q : E →ₗ[F2] V) (θ : H →ₗ[F2] E) :
    Finset (H →ₗ[F2] E) := Finset.univ.filter fun Φ => q.comp (Φ + θ) = 0

def sliceCorrelation (q : E →ₗ[F2] V) (N₀ : E →ₗ[F2] H)
    (f : (E →ₗ[F2] H) → ℝ) (θ : H →ₗ[F2] E) : ℝ :=
  𝔼 A : V →ₗ[F2] H,
    f (N₀ + A.comp q) * (linearTraceCharacter θ (N₀ + A.comp q)).re

end AffineSlice


end DFVSGames.Decoder.PrivateFourier
end


noncomputable section

namespace DFVSGames.Decoder.PrivateStrategy

attribute [local instance] Classical.propDecidable

open PrivateFourier
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Foundations.Games
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

def conditionalAgreement (Z : Submodule F2 U) (z : U)
    (τU : U →ₗ[F2] F2) (hz : τU z = 1) (π : U →ₗ[F2] E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K)
    (τ : E →ₗ[F2] F2) (fallback : ActualAnswer τ) : ℝ :=
  ((candidateLaw Z z τU hz).product (privateLaw F ι τ fallback)).probability
    (fun a => decide (π a.1.1 = a.2.1))

def goodCosetMass (Q : Submodule F2 E) (z' : E)
    (F : (E →ₗ[F2] H) → K) (ι : H →ₗ[F2] K) : ℝ :=
  𝔼 σ : K →ₗ[F2] F2, if σ.comp ι ≠ 0 then
    ∑ Φ ∈ frequencyCoset Q.mkQ ((σ.comp ι).smulRight z'),
      frequencyWeight (tableSign F σ) Φ else 0

end ConditionalAgreement


end DFVSGames.Decoder.PrivateStrategy
end

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

noncomputable section

def timePolynomial (p : Polynomial Nat) : Polynomial Nat :=
  prefixCostPolynomial (digit p) (width p) +
    Polynomial.C 2 * prefixValuePolynomial (digit p) (width p) + Polynomial.X + Polynomial.C 8

theorem timePolynomial_eval (p : Polynomial Nat) (n : Nat) :
    (timePolynomial p).eval n = MachineHorner.steps n (digit p) (width p) + n + 3 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval,
    prefixCostPolynomial_eval, MachineHorner.steps]
  omega

theorem hornerValue_eq_eval (p : Polynomial Nat) (n : Nat) :
    MachineHorner.value n (digit p) (width p) = p.eval n := by
  rw [MachineHorner.value_eq_foldl, range_map_digit]
  have hh := highCoefficients_foldl p n
  simpa only [Nat.mul_comm] using hh

end

end DFVSGames.Foundations.Complexity.CookLevin.PolynomialMachine


namespace DFVSGames.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

noncomputable section

namespace Eval

open CookLevin.PolynomialMachine

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (p : Polynomial Nat) := Unit ⊕ (MachineHorner.Label (width p) ⊕ Unit)

def start (p : Polynomial Nat) : Label p := .inl ()
def inner (p : Polynomial Nat) (l : MachineHorner.Label (width p)) : Label p := .inr (.inl l)
def finish (p : Polynomial Nat) : Label p := .inr (.inr ())

theorem clear_result (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (base : K → List Bool) (result : Nat)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = []) :
    clearFieldsTapes (fun k => (word p slots k).length) (indices p slots)
      (MachineHorner.resultTapes slots (prepared p slots base) result) =
      MachineHorner.resultTapes slots base result := by
  funext k
  rw [clearFieldsTapes_apply _ _ (indices_nodup p slots)]
  by_cases h : k ∈ indices p slots
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp [MachineHorner.resultTapes, slots.injective.eq_iff, prepared_digit,
      fieldWord, hcoeff]
  · by_cases hd : k = slots (.inl 3)
    · subst k
      simp [MachineHorner.resultTapes]
    · simp [h, MachineHorner.resultTapes, hd, prepared,
        prependFieldsTapes_apply _ _ (indices_nodup p slots)]

def statement (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ) :
    Label p → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl _ => prependFields (word p slots) (indices p slots)
      (.goto fun _ => labels (inner p .start))
  | .inr (.inl l) => MachineHorner.statement slots (fun l => labels (inner p l))
      (some (labels (finish p))) l
  | .inr (.inr _) => clearFields (fun k => (word p slots k).length) (indices p slots)
      (Reduction.MachineTransfer.exitAt (slots (.inl 3)) exit)

def steps (p : Polynomial Nat) (n : Nat) : Nat :=
  MachineHorner.steps n (digit p) (width p) + 2

theorem trace (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement p slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl 0)) = encodeWord n)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps p n]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
  have hp : (advance (TM2.step program))^[1]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (inner p .start)), ((ambient, ()), register), prepared p slots base⟩ := by
    change some (TM2.stepAux (program (labels (start p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (prependFields _ _ _) _ _) = _
    rw [stepAux_prependFields]
    rfl
  have hh := MachineHorner.hornerTrace slots (fun l => labels (inner p l))
    (some (labels (finish p))) program (fun l => atLabels (inner p l))
    (prepared p slots base) n (digit p) (by simpa using hinput)
    (fun i => prepared_digit p slots base i (hcoeff i))
    (by
      constructor
      · simpa using clean.accA
      · simpa using clean.accB
      · simpa using clean.counter
      · simpa using clean.scratch) ambient register
  rw [hornerValue_eq_eval] at hh
  have hc : (advance (TM2.step program))^[1]
      (some ⟨some (labels (finish p)), ((ambient, ()), none),
        MachineHorner.resultTapes slots (prepared p slots base) (p.eval n)⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
    change some (TM2.stepAux (program (labels (finish p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (clearFields _ _ _) _ _) = _
    rw [stepAux_clearFields, clear_result p slots base _ hcoeff]
    cases exit <;> rfl
  rw [show steps p n = 1 + (MachineHorner.steps n (digit p) (width p) + 1) by
    unfold steps; omega, Function.iterate_add_apply, Function.iterate_add_apply, hp, hh, hc]

end Eval

end

end DFVSGames.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Explicit
attribute [-instance] _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype
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
open ConditionalIncidences PartnerProjection RawPartnerTarget RawMapLaw
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

def interceptShift (rhs : Fin k → Bool) (d : Fin k → BlockDraw V) : V :=
  ∑ j, ofBit (rhs j) • blockThird (d j)

def rawTupleEquiv (J : Finset (Fin k)) : RawTuple J V ≃ RawCoefficients J V where
  toFun a
    | none => a.1
    | some (.inl (j, i)) => if i = 0 then (a.2.1 j).1 else (a.2.1 j).2
    | some (.inr j) => a.2.2 j
  invFun gamma := ⟨gamma none,
    ⟨(fun j => (gamma (some (.inl (j, 0))), gamma (some (.inl (j, 1))))),
      (fun j => gamma (some (.inr j)))⟩⟩
  left_inv a := by
    apply Prod.ext rfl
    apply Prod.ext
    · funext j
      rfl
    · rfl
  right_inv gamma := by
    funext s
    rcases s with _ | (⟨j, i⟩ | j)
    · rfl
    · fin_cases i <;> rfl
    · rfl

def tupleDraw (J : Finset (Fin k)) (slot : Fin k → Slot) (a : RawTuple J V)
    (j : Fin k) : BlockDraw V :=
  if hj : j ∈ J then .inr (ConcreteExtraction.slotIndex (slot j), a.2.2 ⟨j, hj⟩)
  else .inl (a.2.1 ⟨j, hj⟩)


variable [Fintype V]

def paddedWeights (rhs : Fin k → Bool) (β : ℝ) : ActualEnumeration.Coefficients k V → ℝ :=
  pushforwardWeight (drawWeights β k)
    (fun dz => ActualEnumeration.toCoefficients k V (paddedMap rhs dz.1 dz.2))

def ChoiceValue (V : Type) : ProjectionChoice → Type
  | none => V × V
  | some _ => V

instance choiceValueFintype (c : ProjectionChoice) : Fintype (ChoiceValue V c) := by
  cases c <;> dsimp [ChoiceValue] <;> infer_instance

def choiceEmbed : (c : ProjectionChoice) → ChoiceValue V c → BlockDraw V
  | none, ab => .inl ab
  | some i, a => .inr (i, a)

def fullChoiceValue : (c : ProjectionChoice) → ChoiceValue V c → V × V
  | none, x => x
  | some _, _ => (0, 0)

def singleChoiceValue : (c : ProjectionChoice) → ChoiceValue V c → V
  | none, _ => 0
  | some _, x => x

def readChoiceValue (q : ProjectionChoice) (full : q = none → V × V)
    (single : q.isSome = true → V) : ChoiceValue V q := by
  cases q with
  | none => exact full rfl
  | some i => exact single rfl

omit [Module F2 V] [Fintype V] in
theorem readChoiceValue_roundtrip (q : ProjectionChoice) (v : ChoiceValue V q) :
    readChoiceValue q (fun _ => fullChoiceValue q v)
      (fun _ => singleChoiceValue q v) = v := by
  cases q <;> rfl

omit [Module F2 V] [Fintype V] in
theorem readChoiceValue_full (q : ProjectionChoice) (full : q = none → V × V)
    (single : q.isSome = true → V) (h : q = none) :
    fullChoiceValue q (readChoiceValue q full single) = full h := by
  subst q
  rfl

omit [Module F2 V] [Fintype V] in
theorem readChoiceValue_single (q : ProjectionChoice) (full : q = none → V × V)
    (single : q.isSome = true → V) (h : q.isSome = true) :
    singleChoiceValue q (readChoiceValue q full single) = single h := by
  cases q with
  | none => simp at h
  | some i => rfl

def choiceValuesToRawTuple (c : Fin k → ProjectionChoice)
    (fz : (∀ j, ChoiceValue V (c j)) × V) : RawTuple (choiceMask c) V :=
  (fz.2,
    (fun j => fullChoiceValue (c j.val) (fz.1 j.val)),
      fun j => singleChoiceValue (c j.val) (fz.1 j.val))

def rawTupleToChoiceValues (c : Fin k → ProjectionChoice)
    (a : RawTuple (choiceMask c) V) (j : Fin k) : ChoiceValue V (c j) :=
  readChoiceValue (c j)
    (fun h => a.2.1 ⟨j, (not_mem_choiceMask c j).mpr h⟩)
    (fun h => a.2.2 ⟨j, by simpa [choiceMask] using h⟩)

def choiceValuesRawTupleEquiv (c : Fin k → ProjectionChoice) :
    ((∀ j, ChoiceValue V (c j)) × V) ≃ RawTuple (choiceMask c) V where
  toFun := choiceValuesToRawTuple c
  invFun a := (rawTupleToChoiceValues c a, a.1)
  left_inv fz := by
    apply Prod.ext
    · funext j
      exact readChoiceValue_roundtrip (c j) (fz.1 j)
    · rfl
  right_inv a := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        have hc : c j.val = none := (not_mem_choiceMask c j.val).mp j.property
        exact readChoiceValue_full (c j.val) _ _ hc
      · funext j
        have hc : (c j.val).isSome = true := by
          simpa [choiceMask] using j.property
        exact readChoiceValue_single (c j.val) _ _ hc


variable [Fintype (ActualHomogeneous.E k →ₗ[F2] V)]

def paddedMapWeights (rhs : Fin k → Bool) (β : ℝ) :
    (ActualHomogeneous.E k →ₗ[F2] V) → ℝ :=
  pushforwardWeight (drawWeights β k) (fun dz => paddedMap rhs dz.1 dz.2)


end
end DFVSGames.Decoder.PaddedLaw

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

namespace DFVSGames.Outer.Clone100

open DFVSGames.Reduction CloneGap ActualSource
open Clone100Triples Clone100Counting
open scoped BigOperators

noncomputable section

def equation {n : Nat} (e : Equation (Fin n)) (t : GoodTriple) :
    Equation (Fin (n * 100)) :=
  ⟨nameEquiv n (e.first, t.val.1), nameEquiv n (e.second, t.val.2.1),
    nameEquiv n (e.third, t.val.2.2), e.rhs⟩

def equations {n : Nat} (es : List (Equation (Fin n))) :
    List (Equation (Fin (n * 100))) :=
  es.flatMap (fun e => triples.map (equation e))

theorem equations_length {n : Nat} (es : List (Equation (Fin n))) :
    (equations es).length = es.length * 970200 := by
  induction es with
  | nil => simp [equations]
  | cons e es ih =>
    simp only [equations, List.flatMap_cons, List.length_append, List.length_map,
      triples_length, List.length_cons] at *
    omega

theorem equations_nonempty {n : Nat} (es : List (Equation (Fin n))) (hne : es ≠ []) :
    equations es ≠ [] := by
  apply List.length_pos_iff.mp
  rw [equations_length]
  exact Nat.mul_pos (List.length_pos_iff.mpr hne) (by decide)

def clonedInput (input : SourceEncoding.Input) : SourceEncoding.Input where
  «variables» := input.«variables» * 100
  equations := equations input.equations
  nonempty := equations_nonempty input.equations input.nonempty

end
end DFVSGames.Outer.Clone100

end

section

namespace DFVSGames.Explicit.MachineClone100Table

open DFVSGames.Reduction

def cloneEquationWords {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * e.first.val, t.2.1 + 100 * e.second.val,
    t.2.2 + 100 * e.third.val, if e.rhs then 1 else 0]

end DFVSGames.Explicit.MachineClone100Table
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.Explicit.MachineClone100Loop

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineClone100Model

def recordOfEquation {n : Nat} (e : CloneGap.Equation (Fin n)) : Record :=
  ⟨e.first.val, e.second.val, e.third.val, if e.rhs then 1 else 0⟩

end DFVSGames.Explicit.MachineClone100Loop

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

theorem equation_words {n : Nat} (e : CloneGap.Equation (Fin n))
    (t : Outer.Clone100Triples.GoodTriple) :
    SourceEncoding.equationWords (Outer.Clone100.equation e t) =
      MachineClone100Table.cloneEquationWords e (indices t) := by
  simp [SourceEncoding.equationWords, Outer.Clone100.equation,
    Outer.Clone100.nameEquiv, finProdFinEquiv,
    MachineClone100Table.cloneEquationWords, indices, Nat.mul_comm]

theorem body_words {n : Nat} (es : List (CloneGap.Equation (Fin n))) :
    (Outer.Clone100.equations es).flatMap SourceEncoding.equationWords =
      es.flatMap (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [Outer.Clone100.equations, List.flatMap_assoc, List.flatMap_map,
    equation_words, triples]

theorem input_words_eq (input : SourceEncoding.Input) :
    SourceEncoding.inputWords (Outer.Clone100.clonedInput input) =
      [100 * input.«variables», triples.length * input.equations.length] ++
        input.equations.flatMap
          (fun e => triples.flatMap (MachineClone100Table.cloneEquationWords e)) := by
  simp only [SourceEncoding.inputWords, Outer.Clone100.clonedInput,
    Outer.Clone100.equations_length, body_words, triples_length]
  simp [Nat.mul_comm]

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

def instruction : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push 2 (fun state => state.2.getD false)
            (.load (fun state => (nextMode state.1 (state.2.getD false), none))
              (.goto fun _ => .scan)))
          (.branch (fun state => decide (state.1 = .done))
            (.load (fun _ => (.clause, none)) (.goto fun _ => .restore))
            (.load (fun _ => (.clause, none)) (.goto fun _ => .drain))))
  | .restore => loopAt 2 1 id false .restore none
  | .drain => MachineDrain.drain 2 .drain (some .rejectOutput)
  | .rejectOutput => pushWord 1 rejectedWord.reverse .halt

abbrev machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (.clause, none)
  m := instruction

def cfg (label : Option Label) (input output saved : List Bool) (mode : Mode := .clause)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input output saved⟩

theorem step_scan_empty (output saved : List Bool) (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) [] output saved mode register) =
      some (cfg (some (afterScan mode)) [] output saved) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  by_cases accepted : mode = .done <;>
    simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryTotalInputMachine, afterScan, accepted]
  all_goals rfl

theorem step_scan_cons (bit : Bool) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) (bit :: input) output saved mode register) =
      some (cfg (some .scan) input output (bit :: saved) (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryTotalInputMachine, update_saved_inline_MachineBinaryTotalInputMachine]
  rfl

theorem scanTrace (input output saved : List Bool) (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .scan) input output saved mode register)) =
      some (cfg (some (afterScan (run mode input))) [] output (input.reverse ++ saved)) := by
  induction input generalizing saved mode register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run, List.reverse_nil, List.nil_append] using
          step_scan_empty output saved mode register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_scan_cons]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (bit :: saved) (nextMode mode bit) none

theorem drainTrace (saved output : List Bool) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .drain) [] output saved .clause register)) =
      some (cfg (some .rejectOutput) [] output []) := by
  change (advance (TM2.step instruction))^[saved.length + 1]
    (some ⟨some .drain, (Mode.clause, register), tapes [] output saved⟩) =
    some ⟨some .rejectOutput, (Mode.clause, none), tapes [] output []⟩
  have trace := MachineDrain.drainTrace (2 : Fin 3) .drain (some .rejectOutput)
    instruction rfl (tapes [] output []) saved Mode.clause register
  simpa only [update_saved_inline_MachineBinaryTotalInputMachine] using trace

theorem step_rejectOutput (output : List Bool) :
    machine.step (cfg (some .rejectOutput) [] output []) =
      some (cfg none [] (rejectedWord ++ output) []) := by
  change some (TM2.stepAux
    (pushWord (Γ := Alphabet) (Λ := Label) (σ := State)
      (1 : Fin 3) rejectedWord.reverse .halt) _ _) = _
  rw [stepAux_pushWord]
  simp only [cfg, List.reverse_reverse, tapes_output, update_output_inline_MachineBinaryTotalInputMachine, TM2.stepAux]
  rfl

theorem rejectedTrace (input : List Bool) (rejected : run .clause input ≠ .done) :
    (advance machine.step)^[2 * input.length + 3]
      (some (cfg (some .scan) input [] [])) = some (cfg none [] rejectedWord []) := by
  have first := scanTrace input [] [] .clause none
  simp only [afterScan, rejected, ↓reduceIte, List.append_nil] at first
  have second := drainTrace input.reverse [] none
  simp only [List.length_reverse] at second
  have third : (advance machine.step)^[1]
      (some (cfg (some .rejectOutput) [] [] [])) = some (cfg none [] rejectedWord []) := by
    simpa only [Function.iterate_one, advance_some, List.append_nil] using
      step_rejectOutput []
  have time : 2 * input.length + 3 = (input.length + 1) + (input.length + 1) + 1 := by omega
  rw [time]
  exact joinTrace_inline_MachineBinaryTotalInputMachine (joinTrace_inline_MachineBinaryTotalInputMachine first second) third

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .scan) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] output [] := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end DFVSGames.BinaryTotalInputMachine

end

section

namespace DFVSGames.BinaryNameCompare

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

def compareStateEquiv (A : Type) : MachineCompare.State A ≃ State A where
  toFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  invFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

def instruction (tape : Fin 5 → K) (labels : Label → Λ)
    (equalExit differentExit malformedExit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan => MachineStateEquiv.statement (scanStateEquiv A)
      (BinaryNameMachine.scan (tape 0) (tape 2) (labels .scan)
        (some (labels .copyOut)) malformedExit)
  | .copyOut => DFVSGames.Reduction.MachineTransfer.loopAt (tape 1) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4) (tape 1) (tape 3) false
      (labels .copyBack) (some (labels .compare))
  | .compare => MachineStateEquiv.statement (compareStateEquiv A)
      (MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit)

end DFVSGames.BinaryNameCompare

end

section

namespace DFVSGames.BinaryNameSearch

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

section Program

variable {K Λ A : Type} [DecidableEq K]

def instruction (tape : Fin 6 → K) (labels : Label → Λ)
    (foundExit missingExit malformedExit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .sign =>
      .pop (tape 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (finish (some (labels (.comparison .scan)))) (finish missingExit))
  | .comparison l => BinaryNameCompare.instruction (compareTapes tape)
      (fun l => labels (.comparison l)) foundExit (some (labels .increment)) malformedExit l
  | .increment => .push (tape 5) (fun _ => true) (.goto fun _ => labels .sign)

end Program

end DFVSGames.BinaryNameSearch

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.BinaryLiteralMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

def instruction (tape : Fin 9 → K) (labels : Label → Λ)
    (exit malformed : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .readSign => readSign tape (labels .scanKey) malformed
  | .scanKey => MachineStateEquiv.statement (BinaryNameCompare.scanStateEquiv (A × Bool))
      (BinaryNameMachine.scan (tape 0) (tape 2) (labels .scanKey)
        (some (labels .copyOut)) malformed)
  | .copyOut => loopAt (tape 1) (tape 6) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 6) (tape 1) (tape 3) false
      (labels .copyBack) (some (labels (.search .sign)))
  | .search l => BinaryNameSearch.instruction (searchTapes tape)
      (fun l => labels (.search l)) (some (labels .drainSearch)) malformed malformed l
  | .drainSearch => MachineDrain.drain (tape 3) (labels .drainSearch)
      (some (labels .drainKey))
  | .drainKey => MachineDrain.drain (tape 2) (labels .drainKey)
      (some (labels .emitIndex))
  | .emitIndex => loopAt (tape 7) (tape 8) id false
      (labels .emitIndex) (some (labels .emitSign))
  | .emitSign => emitSign (tape 8) exit

end DFVSGames.BinaryLiteralMachine

end

section

namespace DFVSGames.BinaryRenameLoop

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

section Program

variable {K Λ A : Type} [DecidableEq K]

def instruction (tape : Fin 11 → K) (labels : Label → Λ)
    (done malformed : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .entry =>
      .pop (tape 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push (tape 0) (fun state => state.2.getD false)
            (finish (some (labels (.literal .readSign)))))
          (finish done))
  | .literal l => BinaryLiteralMachine.instruction (literalTapes tape)
      (fun l => labels (.literal l)) (some (labels .tally)) malformed l
  | .tally =>
      .push (tape 9) (fun _ => true)
        (.branch (fun state => state.1.1.1.2 == (2 : Fin 3))
          (.push (tape 10) (fun _ => true) (next (labels .entry)))
          (next (labels .entry)))

end Program

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

namespace DFVSGames.BinaryTokenMachine

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer
open BinaryFormula BinaryEncoding

def program : Label → TM2.Stmt Alphabet Label State
  | .clause => clauseInstruction
  | .sign slot => signInstruction slot
  | .name slot => nameInstruction slot
  | .restore => loopAt 1 2 id false .restore (some .accept)
  | .accept => .halt
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := Label
  main := .clause
  σ := State
  initialState := ((), none)
  m := program

def cfg (label : Option Label) (input reversed output : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input reversed output⟩

theorem clauseStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (true :: input) reversed output register) =
      some (cfg (some (.sign 0)) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero_inline_MachineBinaryTokenMachine]
  rfl

theorem finalStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (false :: input) reversed output register) =
      some (cfg (some .restore) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero_inline_MachineBinaryTokenMachine]
  rfl

theorem signStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.sign slot)) (bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: reversed) output) := by
  change some (TM2.stepAux (program (.sign slot)) _ _) = _
  simp [program, signInstruction, jump, cfg, TM2.stepAux, update_zero_inline_MachineBinaryTokenMachine, update_one_inline_MachineBinaryTokenMachine]
  rfl

theorem nameEndStep (slot : Fin 3) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.name slot)) (false :: input) reversed output register) =
      some (cfg (some (afterName slot)) input (false :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero_inline_MachineBinaryTokenMachine, update_one_inline_MachineBinaryTokenMachine]
  rfl

theorem nameDigitStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step
      (cfg (some (.name slot)) (true :: bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: true :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero_inline_MachineBinaryTokenMachine, update_one_inline_MachineBinaryTokenMachine]
  rfl

theorem nameTrace (slot : Fin 3) (bits suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[bits.length + 1]
      (some (cfg (some (.name slot)) (frame bits ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix ((frame bits).reverse ++ reversed) output) := by
  induction bits generalizing reversed register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        frame, List.singleton_append, List.reverse_singleton] using
        nameEndStep slot suffix reversed output register
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [frame, List.cons_append, advance_some]
      rw [nameDigitStep, ih]
      simp only [List.reverse_cons, List.append_assoc,
        List.cons_append, List.nil_append]

theorem literalTrace (slot : Fin 3) (literal : Literal)
    (suffix reversed output : List Bool) (register : Option Bool) :
    (advance machine.step)^[literal.name.size + 2]
      (some (cfg (some (.sign slot)) (literalBits literal ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix
        ((literalBits literal).reverse ++ reversed) output) := by
  rw [show literal.name.size + 2 = (literal.name.bits.length + 1) + 1 by
    rw [Nat.size_eq_bits_len]]
  rw [Function.iterate_succ_apply]
  simp only [literalBits, List.cons_append, advance_some]
  rw [signStep]
  change (advance machine.step)^[literal.name.bits.length + 1]
    (some (cfg (some (.name slot)) (frame literal.name.bits ++ suffix)
      (literal.positive :: reversed) output)) = _
  rw [nameTrace]
  simp only [nameBits, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem clauseTrace (clause : Clause) (suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[clauseNameSize clause + 6]
      (some (cfg (some (.sign 0)) (clauseBits clause ++ suffix) reversed output register)) =
      some (cfg (some .clause) suffix ((clauseBits clause).reverse ++ reversed) output) := by
  have first := literalTrace 0 clause[0]
    (literalBits clause[1] ++ literalBits clause[2] ++ suffix) reversed output register
  have second := literalTrace 1 clause[1] (literalBits clause[2] ++ suffix)
    ((literalBits clause[0]).reverse ++ reversed) output none
  have third := literalTrace 2 clause[2] suffix
    ((literalBits clause[1]).reverse ++ ((literalBits clause[0]).reverse ++ reversed)) output none
  simp only [afterName_zero, afterName_one, afterName_two, List.append_assoc]
    at first second third
  have full := joinTrace_inline_MachineBinaryTokenMachine (joinTrace_inline_MachineBinaryTokenMachine first second) third
  have htime : (clause[0].name.size + 2 + (clause[1].name.size + 2)) +
      (clause[2].name.size + 2) = clauseNameSize clause + 6 := by
    simp [clauseNameSize, clauseNames]
    omega
  rw [htime] at full
  simpa only [clauseBits, List.append_assoc, List.reverse_append] using full

theorem stripTrace (clauses : List Clause) (suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[7 * clauses.length + namesBitSize clauses + 1]
      (some (cfg (some .clause) (clausesBits clauses ++ suffix) reversed output register)) =
      some (cfg (some .restore) suffix ((tokens clauses).reverse ++ reversed) output) := by
  induction clauses generalizing reversed register with
  | nil =>
      simpa only [List.length_nil, Nat.mul_zero, namesBitSize_nil, Nat.add_zero,
        Nat.zero_add, Function.iterate_one, advance_some, clausesBits,
        List.singleton_append, tokens_nil, List.reverse_nil, List.nil_append] using
        finalStep suffix reversed output register
  | cons clause clauses ih =>
      have first : (advance machine.step)^[1]
          (some (cfg (some .clause)
            (true :: (clauseBits clause ++ (clausesBits clauses ++ suffix)))
            reversed output register)) =
          some (cfg (some (.sign 0))
            (clauseBits clause ++ (clausesBits clauses ++ suffix)) reversed output) := by
        simpa only [Function.iterate_one, advance_some] using
          clauseStep (clauseBits clause ++ (clausesBits clauses ++ suffix)) reversed output register
      have second := clauseTrace clause (clausesBits clauses ++ suffix) reversed output none
      have third := ih ((clauseBits clause).reverse ++ reversed) none
      have full := joinTrace_inline_MachineBinaryTokenMachine (joinTrace_inline_MachineBinaryTokenMachine first second) third
      have htime : (1 + (clauseNameSize clause + 6)) +
          (7 * clauses.length + namesBitSize clauses + 1) =
          7 * (clause :: clauses).length + namesBitSize (clause :: clauses) + 1 := by
        simp only [List.length_cons, namesBitSize_cons]
        omega
      rw [htime] at full
      simpa only [clausesBits, List.cons_append, List.append_assoc,
        tokens_cons, List.reverse_append] using full

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .clause) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] [] output := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltStep (output : List Bool) :
    machine.step (cfg (some .accept) [] [] output) = some (cfg none [] [] output) := by
  change some (TM2.stepAux (program .accept) _ _) = _
  rfl

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end DFVSGames.BinaryTokenMachine

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.Explicit.MachineSingleOrbitCodec

open DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity

def doubleInstance {q : Nat} (I : Instance q) : Instance q where
  vertices := 2 * I.vertices
  constraints := I.constraints.map doubleConstraint
  nonempty h := I.nonempty (List.map_eq_nil_iff.mp h)

end DFVSGames.Explicit.MachineSingleOrbitCodec
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .copyOut => MachineTransfer.loopAt (slots 0) (slots 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (slots 4) (slots 0) (slots 1) false
      (labels .copyBack) (some (labels (readStart 0)))
  | .read slot => if slot.1.val < 2 then
      if slot.2 then SourceMachine.fieldLoop (slots 1) (destination slots slot.1.val)
        (labels (.read (slot.1, true))) (some (labels (readStart (slot.1.val + 1))))
      else SourceMachine.fieldStart (destination slots slot.1.val) (labels (.read (slot.1, true)))
    else SourceFieldArray.finish (slots 1) (some (labels .clear))
  | .clear => MachineDrain.drain (slots 1) (labels .clear) exit

omit [DecidableEq K] in
theorem atReadStart (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (r : Nat) (hr : r < 2) :
    statement (σ := σ) slots labels exit (readStart r) =
      SourceMachine.fieldStart (destination slots r) (labels (readLoop r)) := by
  simp [statement, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem atReadLoop (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (r : Nat) (hr : r < 2) :
    statement (σ := σ) slots labels exit (readLoop r) =
      SourceMachine.fieldLoop (slots 1) (destination slots r) (labels (readLoop r))
        (some (labels (readStart (r + 1)))) := by
  simp [statement, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem atReadDone (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    statement (σ := σ) slots labels exit (readStart 2) =
      SourceFieldArray.finish (slots 1) (some (labels .clear)) := by
  simp [statement, readStart]

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

def afterHorner (slots : Tape q width ↪ K) (base : K → List Bool) (B : Nat) (values : List Nat) :
    K → List Bool :=
  MachineHorner.resultTapes (hornerSlots slots) (parsedTapes slots base values)
    (MachineHorner.value B (digits values) width)

def phaseSteps (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
    (base : K → List Bool) (B : Nat) (values : List Nat) : Nat :=
  MachineFieldTemplate.templateSteps tokens (fun j => base (slots (.field j))) +
    ((encodeWords values).length + 1) + (values.sum + 2 * values.length + 1) +
    MachineHorner.steps B (digits values) width +
    MachineDrainMany.steps (chosen slots) (afterHorner slots base B values)

theorem resultTapes_other (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat)
    (tape : K) (hne : tape ≠ slots .output) : resultTapes slots base value tape = base tape := by
  simp [resultTapes, hne]

theorem parsedTapes_other (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) (tape : K)
    (notForward : tape ≠ slots .forward) (notDigit : ∀ i, tape ≠ slots (.digit i)) :
    parsedTapes slots base values tape = base tape := by
  rw [parsedTapes, SourceFieldArray.sequenceTapes_other]
  · exact Function.update_of_ne notForward _ _
  · exact notForward
  · intro r hr
    simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
    exact notDigit _

theorem parsedTapes_source (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) :
    parsedTapes slots base values (slots .forward) = [] := by
  apply SourceFieldArray.sequenceTapes_source
  · intro r hr
    simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
    exact slots.injective.ne (by simp)
  · simp [forwardTapes]

theorem parsedTapes_digit (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) (clean : Clean slots base) (i : Fin width) :
    parsedTapes slots base values (slots (.digit i)) = encodeWord (digits values i.val) := by
  have hi : i.val < values.length := by omega
  have h := SourceFieldArray.sequenceTapes_selected (slots .forward) (parseDestination slots)
    (forwardTapes slots base values) 0 values [] i.val hi
    (by
      intro r hr
      simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
      exact slots.injective.ne (by simp))
    (by
      intro r s hr hs h
      simp only [Nat.zero_add, parseDestination_below slots r (by omega),
        parseDestination_below slots s (by omega)] at h
      exact congrArg Fin.val (Tape.digit.inj (slots.injective h)))
  simpa [parsedTapes, parseDestination, i.isLt, forwardTapes, clean.digit,
    slots.injective.ne (show Tape.digit i ≠ Tape.forward by simp), digits,
    List.getElem?_eq_getElem hi] using h

theorem parsedTapes_clean (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) (clean : Clean slots base) :
    MachineHorner.Clean (hornerSlots slots) (parsedTapes slots base values) := by
  constructor
  · rw [show hornerSlots slots (.inl 1) = slots .accA from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.accA
  · rw [show hornerSlots slots (.inl 2) = slots .accB from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.accB
  · rw [show hornerSlots slots (.inl 4) = slots .counter from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.counter
  · rw [show hornerSlots slots (.inl 5) = slots .hornerScratch from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.hornerScratch

theorem cleanup_result (slots : Tape q width ↪ K) (base : K → List Bool)
    (B : Nat) (values : List Nat) (hlen : values.length = width) (clean : Clean slots base) :
    MachineDrainMany.finalTapes (chosen slots) (afterHorner slots base B values) =
      resultTapes slots base (CanonicalAddress.radix B values) := by
  have hv : MachineHorner.value B (digits values) width = CanonicalAddress.radix B values := by
    rw [← hlen, hornerValue_eq_radix]
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  by_cases hd : tape ∈ chosen slots
  · rw [ite_eq_left hd]
    obtain ⟨i, rfl⟩ := (mem_chosen slots tape).mp hd
    simp [resultTapes, slots.injective.ne (show Tape.digit i ≠ Tape.output by simp), clean.digit]
  · rw [ite_eq_right hd]
    have notDigit : ∀ i, tape ≠ slots (.digit i) := by
      intro i hi
      exact hd ((mem_chosen slots tape).mpr ⟨i, hi.symm⟩)
    by_cases ho : tape = slots .output
    · subst tape
      simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        Function.update_self, resultTapes_output, hv]
      rw [parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp)) notDigit]
    · simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        resultTapes, Function.update_of_ne ho]
      by_cases hf : tape = slots .forward
      · subst tape
        rw [parsedTapes_source slots base values hlen, clean.forward]
      · exact parsedTapes_other slots base values hlen tape hf notDigit

omit [DecidableEq K] in
theorem copiedLength_le_inline_MachineTemplateAddress (tokens : List (MachineFieldTemplate.Token q))
    (fields : Fin q → List Bool) (M : Nat) (bounded : ∀ j, (fields j).length ≤ M) :
    MachineFieldTemplate.copiedLength tokens fields ≤ tokens.length * M := by
  induction tokens with
  | nil => simp [MachineFieldTemplate.copiedLength]
  | cons token tokens ih =>
    cases token with
    | literal bits =>
      simp only [MachineFieldTemplate.copiedLength, List.map_cons, List.sum_cons,
        List.length_cons, Nat.zero_add] at *
      nlinarith
    | copy j =>
      simp only [MachineFieldTemplate.copiedLength, List.map_cons, List.sum_cons,
        List.length_cons] at *
      have h := bounded j
      nlinarith

theorem phaseSteps_le_timePolynomial (tokens : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool) (B : Nat) (values : List Nat)
    (hlen : values.length = width) (clean : Clean slots base) (M : Nat)
    (fieldsBound : ∀ j, (base (slots (.field j))).length ≤ M)
    (wordsBound : (encodeWords values).length ≤ M) (radixBound : B ≤ M)
    (digitBound : ∀ i, i < width → digits values i ≤ M) :
    phaseSteps tokens slots base B values ≤ (timePolynomial tokens.length width).eval M := by
  have hcopied := copiedLength_le_inline_MachineTemplateAddress tokens (fun j => base (slots (.field j))) M fieldsBound
  have htemplate := MachineFieldTemplate.templateSteps_le tokens (fun j => base (slots (.field j)))
  have hhorner := MachineHorner.steps_le_timePolynomial B (digits values) width M radixBound digitBound
  have hselected : ∀ tape ∈ chosen slots, (afterHorner slots base B values tape).length ≤ M + 1 := by
    intro tape ht
    obtain ⟨i, rfl⟩ := (mem_chosen slots tape).mp ht
    have heq : afterHorner slots base B values (slots (.digit i)) =
        encodeWord (digits values i.val) := by
      simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        Function.update_of_ne (slots.injective.ne (show Tape.digit i ≠ Tape.output by simp))]
      exact parsedTapes_digit slots base values hlen clean i
    rw [heq]
    simpa only [encodeWord, List.length_append, List.length_replicate, List.length_singleton] using
      Nat.add_le_add_right (digitBound i.val i.isLt) 1
  have hsum := lengthSum_le_inline_MachineTemplateAddress (chosen slots) (afterHorner slots base B values) (M + 1) hselected
  have hcleanup := MachineDrainMany.steps_le (chosen slots) (afterHorner slots base B values)
  have hchosen : (chosen slots).length = width := by simp [chosen]
  rw [hchosen] at hsum hcleanup
  have hparse := SourceFieldArray.sequence_time_eq_length values
  rw [hlen] at hparse
  rw [timePolynomial_eval]
  unfold phaseSteps
  rw [hlen]
  nlinarith

end DFVSGames.Reduction.MachineTemplateAddress
end

section

namespace DFVSGames.Reduction.MachineAddressEdge

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem work_ne_output (slots : Tape q width ↪ K) :
    workTape slots ≠ outputTape slots := address_ne_output slots _

omit [DecidableEq K] in
theorem temp_ne_work (slots : Tape q width ↪ K) :
    tempTape slots ≠ workTape slots := slots.injective.ne (by simp)

structure Clean (slots : Tape q width ↪ K) (base : K → List Bool) : Prop where
  address : MachineTemplateAddress.Clean (addressSlots slots) base
  work : base (workTape slots) = []

theorem appended_other (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) (tape : K) (hne : tape ≠ outputTape slots) :
    appended slots base bits tape = base tape :=
  MachineFieldTemplate.outputTapes_other _ _ _ _ hne

theorem appended_append (slots : Tape q width ↪ K) (base : K → List Bool)
    (first second : List Bool) :
    appended slots (appended slots base first) second = appended slots base (first ++ second) :=
  MachineFieldTemplate.outputTapes_append _ _ _ _

theorem Clean.appended (slots : Tape q width ↪ K) (base : K → List Bool)
    (clean : Clean slots base) (bits : List Bool) : Clean slots (appended slots base bits) := by
  constructor
  · constructor
    · simpa only [appended_address] using clean.address.reversed
    · simpa only [appended_address] using clean.address.forward
    · simpa only [appended_address] using clean.address.copyScratch
    · simpa only [appended_address] using clean.address.accA
    · simpa only [appended_address] using clean.address.accB
    · simpa only [appended_address] using clean.address.counter
    · simpa only [appended_address] using clean.address.hornerScratch
    · intro j; simpa only [appended_address] using clean.address.digit j
  · simpa only [workTape, appended_address] using clean.work

def phaseSteps (left right : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool)
    (B C : Nat) (leftValues rightValues : List Nat) : Nat :=
  MachineTemplateAddress.phaseSteps left (addressSlots slots) base B leftValues +
    MachineTemplateAddress.phaseSteps right (addressSlots slots)
      (appended slots base (encodeWord (CanonicalAddress.radix B leftValues))) B rightValues +
    CanonicalAddress.radix B leftValues + CanonicalAddress.radix B rightValues + 4 * C + 12

theorem addressResult_eq (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    MachineTemplateAddress.resultTapes (addressSlots slots) base value =
      Function.update base (workTape slots) (encodeWord value ++ base (workTape slots)) := rfl

theorem transfer_result (slots : Tape q width ↪ K) (base : K → List Bool)
    (value : Nat) (empty : base (workTape slots) = []) :
    MachineTransfer.tapesAt (workTape slots) (outputTape slots)
      (MachineTemplateAddress.resultTapes (addressSlots slots) base value) []
      (((MachineTemplateAddress.resultTapes (addressSlots slots) base value) (workTape slots)).reverse.map id ++
        (MachineTemplateAddress.resultTapes (addressSlots slots) base value) (outputTape slots)) =
      appended slots base (encodeWord value) := by
  funext tape
  by_cases hw : tape = workTape slots
  · subst tape
    simp [MachineTransfer.tapesAt, addressResult_eq, appended,
      MachineFieldTemplate.outputTapes, work_ne_output, empty]
  · by_cases ho : tape = outputTape slots
    · subst tape
      simp [MachineTransfer.tapesAt, addressResult_eq, appended,
        MachineFieldTemplate.outputTapes, Ne.symm (work_ne_output slots), empty]
    · simp [MachineTransfer.tapesAt, addressResult_eq, appended,
        MachineFieldTemplate.outputTapes, hw, ho]

theorem phaseSteps_le_timePolynomial (left right : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool) (B C : Nat)
    (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base) (M : Nat)
    (fieldsBound : ∀ j, (base (addressSlots slots (.field j))).length ≤ M)
    (leftWordsBound : (encodeWords leftValues).length ≤ M)
    (rightWordsBound : (encodeWords rightValues).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (leftDigitBound : ∀ i, i < width → MachineTemplateAddress.digits leftValues i ≤ M)
    (rightDigitBound : ∀ i, i < width → MachineTemplateAddress.digits rightValues i ≤ M) :
    phaseSteps left right slots base B C leftValues rightValues ≤
      (timePolynomial left.length right.length width).eval M := by
  have hleft := MachineTemplateAddress.phaseSteps_le_timePolynomial left (addressSlots slots)
    base B leftValues leftLength clean.address M fieldsBound leftWordsBound radixBound leftDigitBound
  have hright := MachineTemplateAddress.phaseSteps_le_timePolynomial right (addressSlots slots)
    (appended slots base (encodeWord (CanonicalAddress.radix B leftValues))) B rightValues
    rightLength (Clean.appended slots base clean _).address M
    (by simpa only [appended_address] using fieldsBound) rightWordsBound radixBound rightDigitBound
  have hlrank := radix_le_magnitude B leftValues width M leftLength radixBound leftDigitBound
  have hrrank := radix_le_magnitude B rightValues width M rightLength radixBound rightDigitBound
  rw [timePolynomial_eval]
  unfold phaseSteps
  omega

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_CanonicalWordTemplate
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

namespace DFVSGames.Reduction.CanonicalWordTemplate

open Foundations.Complexity CanonicalEncoding

theorem eval_template {n m s d : Nat} (names : Fin m → Fin 3 → Fin n)
    (occurrence : Fin m) (a : Fin 3 → Ambient s d) :
    evalTemplate (fun j => (names occurrence j).val) occurrence.val (template a) =
      recordWords (ActualCanonical.record names occurrence a) := by
  unfold template ActualCanonical.record
  split_ifs <;> rfl

end DFVSGames.Reduction.CanonicalWordTemplate
end

section

namespace DFVSGames.Reduction.CanonicalBodyTemplate

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding
open scoped BigOperators

variable {k : Nat}

@[simp] theorem recordFields_occurrence (names : Fin 3 → Nat) (occurrence : Nat) :
    recordFields names occurrence 3 = occurrence := by simp [recordFields]

def sourceFields {n m k : Nat} (occ : Fin k → Fin m) (names : Fin m → Fin 3 → Fin n)
    (j : Fin k) : Fin 4 → Nat :=
  recordFields (fun i => (names (occ j) i).val) (occ j).val

theorem eval_liftToken {n m k : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (j : Fin k) (token : CanonicalWordTemplate.Token) :
    evalToken (sourceFields occ names) (liftToken j token) =
      CanonicalWordTemplate.evalToken (fun i => (names (occ j) i).val) (occ j).val token := by
  cases token <;> simp [evalToken, sourceFields, liftToken, CanonicalWordTemplate.evalToken]

theorem eval_liftRecord {n m k : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (j : Fin k)
    (tokens : List CanonicalWordTemplate.Token) :
    evalTemplate (sourceFields occ names) (liftRecord j tokens) =
      CanonicalWordTemplate.evalTemplate (fun i => (names (occ j) i).val) (occ j).val tokens := by
  simp only [evalTemplate, liftRecord, List.map_map, Function.comp_def, eval_liftToken,
    CanonicalWordTemplate.evalTemplate]

theorem eval_recordsList {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (a : Fin k → Fin 3 → Ambient s d)
    (positions : List (Fin k)) :
    evalTemplate (sourceFields occ names) (recordsList a positions) =
      (positions.map (fun j => ActualCanonical.record names (occ j) (a j))).flatMap recordWords := by
  induction positions with
  | nil => rfl
  | cons j positions ih =>
    change
      evalTemplate (sourceFields occ names)
          (liftRecord j (CanonicalWordTemplate.template (a j)) ++ recordsList a positions) =
        recordWords (ActualCanonical.record names (occ j) (a j)) ++
          (positions.map (fun i => ActualCanonical.record names (occ i) (a i))).flatMap recordWords
    rw [show ∀ xs ys, evalTemplate (sourceFields occ names) (xs ++ ys) =
      evalTemplate (sourceFields occ names) xs ++ evalTemplate (sourceFields occ names) ys by
      intro xs ys; exact List.map_append]
    rw [eval_liftRecord, CanonicalWordTemplate.eval_template, ih]

theorem eval_data {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (z : Ambient s d) (a : Fin k → Fin 3 → Ambient s d) :
    evalTemplate (sourceFields occ names) (template z a (fun j => rhs (occ j))) =
      bodyWords ((ActualCanonical.data occ names rhs z a).1.2,
        (ActualCanonical.data occ names rhs z a).2) := by
  change
    vectorWord (ambientShift z a (fun j => rhs (occ j))).2 ::
        evalTemplate (sourceFields occ names) (recordsList a (List.ofFn id)) =
      vectorWord (ambientShift z a (fun j => rhs (occ j))).2 ::
        (List.ofFn (fun j => ActualCanonical.record names (occ j) (a j))).flatMap recordWords
  rw [eval_recordsList, List.map_ofFn]
  rfl

theorem eval_canonical {n m k s d : Nat} (occ : Fin k → Fin m)
    (names : Fin m → Fin 3 → Fin n) (rhs : Fin m → F2)
    (X : ActualHomogeneous.E k →ₗ[F2] Ambient s d) :
    evalTemplate (sourceFields occ names)
        (template (X (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple X)
          (fun j => rhs (occ j))) =
      bodyWords ((ActualCanonical.canonical occ names rhs X).1.2,
        (ActualCanonical.canonical occ names rhs X).2) :=
  eval_data occ names rhs _ _

theorem eval_actualQuery (S : ActualSource.Source) {k s d : Nat}
    (q : ActualGame.Query S k s d) :
    evalTemplate (sourceFields q.1 (ActualGame.names S))
        (template (q.2 (ActualHomogeneous.hBasis k)) (ActualCanonical.standardTriple q.2)
          (fun j => ActualGame.rhs S (q.1 j))) =
      bodyWords (ActualOrbit.body (ActualGame.canonical S k s d) q) :=
  eval_canonical q.1 (ActualGame.names S) (ActualGame.rhs S) q.2

end DFVSGames.Reduction.CanonicalBodyTemplate
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
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

namespace DFVSGames.Reduction.AddressOdometerSchedule

open Turing
open DFVSGames.Foundations.Complexity MachineTupleOdometer
open DFVSGames.Foundations.Hastad
open MachineTransfer

noncomputable section

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def blocks {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) (d : ℕ) : List Bool :=
  if h : d < m then allBits (fun c => bits (Fin.snoc c ⟨d, h⟩)) else []

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
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PositiveMultiplier
attribute [-instance] _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier
open MatrixCharacters MatrixFourier MatrixNoise MatrixEnergy

namespace DFVSGames.Decoder.PositiveMultiplier

section ActualMatrixTest

variable {Q C E V : Type*} [Fintype Q] [Fintype C]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
  [Fintype V] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] V)] [Fintype (V →ₗ[F2] E)]

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

def subspaceLaw (ι : K →ₗ[F2] V) (v : V) : ℝ := by
  classical
  exact ∑ k, if ι k = v then (Fintype.card K : ℝ)⁻¹ else 0

end UniformSubspace

end DFVSGames.Decoder.PositiveMultiplier
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_VisibleTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.VisibleTransfer

open DFVSGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Ω D : Type*} [Fintype Ω] [Fintype D]

def fiberMass (μ : FiniteDistribution Ω) (observe : Ω → D)
    (d : D) (event : Ω → Bool) : ℝ :=
  μ.probability (fiberEvent observe d event)

def visibleWitness (μ : FiniteDistribution Ω) (observe : Ω → D)
    (slice targetHit : Ω → Bool) (threshold : ℝ) (d : D) : Bool := by
  classical
  exact decide (0 < fiberMass μ observe d slice ∧
    threshold * fiberMass μ observe d slice ≤
      fiberMass μ observe d (fun x => slice x && targetHit x))

end
end DFVSGames.Decoder.VisibleTransfer

end OAI
end


