-- Prove2me | Definitions.Def_OAIQ085D015
-- name    : OAIQ085D015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:08:47.187224+00:00
-- url     : https://prove2.me/theorems/6613f76b-c96b-43dd-9086-bfef73e0c46e
-- title:
--   Definitions bundle OAIQ085D015 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 412 declarations of OpenAI's Lean: 118 definitions, 2 inductive types or structures, 1 instance and 291 theorems. The definitions and types are `OAI.DFVSGames.Foundations.Hastad.ConditionedOracle.fallback`, `OAI.DFVSGames.Foundations.Hastad.SourceAddressDescriptors.baseValue`, `OAI.DFVSGames.Foundations.Hastad.SourceBasePhase.operandLength`, `OAI.DFVSGames.Foundations.Hastad.SourceBasePhase.steps`, `OAI.DFVSGames.Foundations.Hastad.SourceBasePhase.timePolynomial`, `OAI.DFVSGames.Foundations.Hastad.SourceClauseLookup.outputTapes`, `OAI.DFVSGames.Foundations.Hastad.SourceClauseLookup.program`, `OAI.DFVSGames.Foundations.Hastad.SourceContextLoad.lookupOutput`, `OAI.DFVSGames.Foundations.Hastad.SourceContextLoad.program`, `OAI.DFVSGames.Foundations.Hastad.SourceEquationEmit.statement`, `OAI.DFVSGames.Foundations.Hastad.SourceGame.repeatedVisible`, `OAI.DFVSGames.Foundations.Hastad.SourceGame.sourceProjectionGame`, `OAI.DFVSGames.Foundations.Hastad.SourceGeneratorModel.allTapes`, `OAI.DFVSGames.Foundations.Hastad.SourceGeneratorModel.clearKeys`, `OAI.DFVSGames.Foundations.Hastad.SourceGeneratorModel.coefficientKeys`, `OAI.DFVSGames.Foundations.Hastad.SourceGeneratorModel.headerControl`, `OAI.DFVSGames.Foundations.Hastad.SourceGeneratorModel.headerSlots`, `OAI.DFVSGames.Foundations.Hastad.SourceGeneratorModel.outputTape`, `OAI.DFVSGames.Foundations.Hastad.SourceGeneratorModel.workKeys`, `OAI.DFVSGames.Foundations.Hastad.SourceGeneratorProgram.Tape`, `OAI.DFVSGames.Foundations.Hastad.SourceHeaderCounts.Clean`, `OAI.DFVSGames.Foundations.Hastad.SourceHeaderCounts.WorkClean`, `OAI.DFVSGames.Foundations.Hastad.SourceLocalEquation.signatureEncoding`, `OAI.DFVSGames.Foundations.Hastad.SourceLocalSignature.signatureCanonicalSlot`, `OAI.DFVSGames.Foundations.Hastad.SourceLocalSignature.signatureEquiv`, `OAI.DFVSGames.Foundations.Hastad.SourceLocalSignature.signatureProjection`, `OAI.DFVSGames.Foundations.Hastad.SourceLocalSignature.signatureValid`, `OAI.DFVSGames.Foundations.Hastad.SourceLoopInit.copiedInput`, `OAI.DFVSGames.Foundations.Hastad.SourceLoopInit.headerDestination`, `OAI.DFVSGames.Foundations.Hastad.SourceLoopInit.program`, `OAI.DFVSGames.Foundations.Hastad.SourceLoopInit.readOutput`, `OAI.DFVSGames.Foundations.Hastad.SourceQueryOrder.occurrenceBits`, `OAI.DFVSGames.Foundations.Hastad.SourceQueryOrder.slotBits`, `OAI.DFVSGames.Foundations.Hastad.SourceQueryOrder.tupleBits`, `OAI.DFVSGames.Foundations.Hastad.SourceRuntimeModel.baseSlots`, `OAI.DFVSGames.Foundations.Hastad.SourceRuntimeModel.clauseRankSlots`, `OAI.DFVSGames.Foundations.Hastad.SourceRuntimeModel.queryLayout`, `OAI.DFVSGames.Foundations.Hastad.SourceRuntimeModel.querySources`, `OAI.DFVSGames.Foundations.Hastad.SourceRuntimeModel.rankControls`, `OAI.DFVSGames.Foundations.Hastad.SourceRuntimeModel.variableRankSlots` and 80 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_CookLevin_PolynomialMachine`, `DirectedFeedback_Encoding_Bounds`, `DirectedFeedback_Encoding_NameCompaction`, `DirectedFeedback_Encoding_Occurrences`, `DirectedFeedback_Encoding_PortTables`, `DirectedFeedback_Encoding_PoweringTables`, `DirectedFeedback_Encoding_VerifierCNF`, `DirectedFeedback_Games_AlphabetReduction`, `DirectedFeedback_Games_CompletedSampling`, `DirectedFeedback_Games_Decoder`, `DirectedFeedback_Games_FieldArray`, `DirectedFeedback_Games_Game`, `DirectedFeedback_Games_GeneratorModel`, `DirectedFeedback_Games_LocalEquation`, `DirectedFeedback_Games_Parameters`, `DirectedFeedback_Games_ProfileCorrection`, `DirectedFeedback_Games_QuestionMarginal`, `DirectedFeedback_Games_SelectedInformation`, `DirectedFeedback_Games_SelectedLikelihood`, `DirectedFeedback_Games_SharedSampling`, `DirectedFeedback_Games_SignaturePrepare`, `DirectedFeedback_Machines_ContextClear`, `DirectedFeedback_Machines_ContextLoad`, `DirectedFeedback_Machines_LoopInit`, `DirectedFeedback_Machines_MachineSubdivisionLoop`, `DirectedFeedback_Machines_Tape`, `DirectedFeedback_Machines_TupleOrder`, `DirectedFeedback_RankGraph_CloneGap`.
--
--   **Imports.** It imports the bundles `OAIQ085D006`, `OAIQ085D007`, `OAIQ085D008` and `OAIQ085D009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D022` and `OAIQ085D023`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ085D006
import Definitions.Def_OAIQ085D007
import Definitions.Def_OAIQ085D008
import Definitions.Def_OAIQ085D009

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSubdivisionLoop
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Hastad.SourceContexts.clauseAnswerFintype _root_.OAI.DFVSGames.Foundations.Hastad.SourceContexts.clauseAnswerInhabited _root_.OAI.DFVSGames.Foundations.Hastad.SourceContexts.slotFintype _root_.OAI.DFVSGames.Foundations.Hastad.SourceContexts.slotInhabited _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP

open Target

theorem honest_satisfies {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) :
    localSatisfies clause (honestAnswer clause assignment) = clause.eval assignment := rfl

theorem honest_answerAt {n : Nat} (clause : Clause n) (assignment : Fin n → Bool)
    (slot : Slot) : answerAt (honestAnswer clause assignment) slot =
      assignment (nameAt clause slot) := by
  cases slot <;> rfl

theorem local_rejection_bound {n : Nat} (clause : Clause n) (alice : ClauseAnswer)
    (bob : Fin n → Bool) :
    acceptedSlots clause alice (honestAnswer clause bob) + clauseFailure clause bob ≤ 3 := by
  have hle := matchingSlots_le alice (honestAnswer clause bob)
  by_cases hb : clause.eval bob = true
  · simp only [clauseFailure, hb, ↓reduceIte, Nat.add_zero]
    unfold acceptedSlots
    split <;> omega
  · have hfailure : clauseFailure clause bob = 1 := by simp [clauseFailure, hb]
    rw [hfailure]
    by_cases ha : localSatisfies clause alice = true
    · have hne : alice ≠ honestAnswer clause bob := by
        intro h
        subst alice
        exact hb ((honest_satisfies clause bob).symm.trans ha)
      have hlt : matchingSlots alice (honestAnswer clause bob) ≠ 3 := by
        intro h
        exact hne ((matchingSlots_eq_three _ _).mp h)
      simp only [acceptedSlots, ha, ↓reduceIte]
      omega
    · simp [acceptedSlots, ha]

def accepts (formula : Formula) (alice : AliceStrategy formula) (bob : BobStrategy formula)
    (event : RandomEvent formula) : Bool :=
  localSatisfies (clauseAt formula event.1) (alice event.1) &&
    decide (answerAt (alice event.1) event.2 = bob (nameAt (clauseAt formula event.1) event.2))

def acceptedCount (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) : List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => acceptedSlots (clauseAt formula i) (alice i)
      (honestAnswer (clauseAt formula i) bob) + acceptedCount formula alice bob rest

def failureCount (formula : Formula) (bob : BobStrategy formula) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => clauseFailure (clauseAt formula i) bob + failureCount formula bob rest

end DFVSGames.Foundations.PCP

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_NameCompaction
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.NameCompaction

open DFVSGames.Foundations.Target

theorem failureCount_evaluations (F : Formula) (A : Fin F.«variables» → Bool)
    (indices : List (Fin F.clauses.length)) :
    failureCount F A indices =
      (indices.map (fun i => (clauseAt F i).eval A)).count false := by
  induction indices with
  | nil => simp [failureCount]
  | cons i rest ih =>
    cases h : (clauseAt F i).eval A <;>
      simp [failureCount, clauseFailure, h, ih, Nat.add_comm]

theorem verifier_failureCount (F : Formula) (A : Fin F.«variables» → Bool) :
    failureCount F A (allIndices F) = failedCount F A := by
  rw [failureCount_evaluations, evaluations_allIndices]
  rfl

end DFVSGames.Foundations.PCP.NameCompaction


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_FieldArray
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceClauseLookup

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition SourceMachine

def program : Label → TM2.Stmt (fun _ : Tape => Bool) Label (Unit × Option Bool)
  | .copyOut => Reduction.MachineTransfer.loopAt .formula .scratch id false
      .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop .scratch .formula .work false
      .copyBack (some .headerFirst)
  | .headerFirst => MachineLookup.discard .work .headerFirst .headerSecond
  | .headerSecond => MachineLookup.discard .work .headerSecond .guard
  | .guard => MachineUnaryCounter.guard .index (skipLabel 0) (readStart 0)
  | .skip slot => MachineLookup.discard .work (.skip slot) (skipLabel (slot.val + 1))
  | .read slot =>
      if slot.1.val < 6 then
        if slot.2 then
          fieldLoop .work (fieldDestination slot.1.val) (.read (slot.1, true))
            (some (readStart (slot.1.val + 1)))
        else fieldStart (fieldDestination slot.1.val) (.read (slot.1, true))
      else SourceFieldArray.finish .work none

theorem atSkip (r : Nat) (hr : r < 6) :
    program (skipLabel r) = MachineLookup.discard .work (skipLabel r) (skipLabel (r + 1)) := by
  simp [skipLabel, hr, program]

theorem atReadStart (r : Nat) (hr : r < 6) :
    program (readStart r) = fieldStart (fieldDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 6) :
    program (readLoop r) = fieldLoop .work (fieldDestination r) (readLoop r)
      (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (readStart 6) = SourceFieldArray.finish .work none := by
  simp [program, readStart, SourceFieldArray.boundedIndex]

theorem discardHeadersTrace (base : Tape → List Bool) (variableCount clauses : Nat)
    (suffix : List Bool) (hinput : base .work = encodeWords [variableCount, clauses] ++ suffix) :
    (advance (TM2.step program))^[variableCount + clauses + 2]
      (some ⟨some .headerFirst, ((), none), base⟩) =
      some ⟨some .guard, ((), none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work headerLabel program base 0 [variableCount, clauses]
    suffix (by
      intro r hr
      have he : r = 0 ∨ r = 1 := by simp at hr; omega
      rcases he with rfl | rfl <;> rfl) hinput ()
  simpa [encodeWords_length, headerLabel] using ht

theorem discardSixTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    (advance (TM2.step program))^[(encodeWords values).length]
      (some ⟨some (skipLabel 0), ((), none), base⟩) =
      some ⟨some .guard, ((), none), Function.update base .work suffix⟩ := by
  have ht := discardFieldsTrace .work skipLabel program base 0 values suffix
    (by intro r hr; simpa only [Nat.zero_add] using atSkip r (by omega)) hinput ()
  simpa [hlen, skipLabel] using ht

theorem skipClausesTrace {n : Nat} (base : Tape → List Bool)
    (prior : List (Target.Clause n)) (indexSuffix suffix : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[(encodeWords (prior.flatMap clauseWords)).length + prior.length + 1]
      (some ⟨some .guard, ((), register), scanTapes base prior.length indexSuffix
        (encodeWords (prior.flatMap clauseWords) ++ suffix)⟩) =
      some ⟨some (readStart 0), ((), none), scanTapes base 0 indexSuffix suffix⟩ := by
  induction prior generalizing register with
  | nil =>
    simpa only [List.flatMap_nil, List.length_nil, encodeWords, List.nil_append,
      Nat.zero_add, Function.iterate_one, advance_some, scanTapes] using
      MachineUnaryCounter.guardStep_zero .index .guard (skipLabel 0) (readStart 0)
        program rfl (Function.update base .work suffix) indexSuffix () register
  | cons clause prior ih =>
    have hencoding : encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix =
        encodeWords (clauseWords clause) ++ (encodeWords (prior.flatMap clauseWords) ++ suffix) := by
      simp only [List.flatMap_cons, encodeWords_append, List.append_assoc]
    have htime : (encodeWords ((clause :: prior).flatMap clauseWords)).length +
        (clause :: prior).length + 1 =
        ((encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
          (encodeWords (clauseWords clause)).length) + 1 := by
      simp only [List.flatMap_cons, encodeWords_append, List.length_append, List.length_cons]
      omega
    rw [htime, Function.iterate_succ_apply]
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1 +
        (encodeWords (clauseWords clause)).length]
      (TM2.step program ⟨some .guard, ((), register),
        MachineUnaryCounter.counterTapes .index
          (Function.update base .work (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix))
          (prior.length + 1) indexSuffix⟩) = _
    rw [MachineUnaryCounter.guardStep_succ .index .guard (skipLabel 0) (readStart 0)
      program rfl]
    rw [Function.iterate_add_apply]
    have hd := discardSixTrace
      (scanTapes base prior.length indexSuffix
        (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix))
      (clauseWords clause) (clauseWords_length clause)
      (encodeWords (prior.flatMap clauseWords) ++ suffix) (by
        rw [scanTapes_work, hencoding])
    change (advance (TM2.step program))^[
      (encodeWords (prior.flatMap clauseWords)).length + prior.length + 1]
      ((advance (TM2.step program))^[(encodeWords (clauseWords clause)).length]
        (some ⟨some (skipLabel 0), ((), none), scanTapes base prior.length indexSuffix
          (encodeWords ((clause :: prior).flatMap clauseWords) ++ suffix)⟩)) = _
    rw [hd, update_scanTapes_work]
    exact ih none

theorem readSix_output_field (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool) (j : Fin 6) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix (.field j) =
      encodeWord (values[j.val]'(by omega)) ++ base (.field j) := by
  have ht := SourceFieldArray.sequenceTapes_selected .work fieldDestination base 0 values
    suffix j.val (by omega) (by intro r hr; simp [fieldDestination])
    (by
      intro r s hr hs he
      apply fieldDestination_injective_below r s (by omega) (by omega)
      simpa only [Nat.zero_add] using he)
  simpa only [Nat.zero_add, fieldDestination_eq] using ht

theorem readSix_output_work (base : Tape → List Bool) (values : List Nat)
    (_hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix .work = suffix := by
  apply SourceFieldArray.sequenceTapes_source _ _ _ _ _ _ _ hinput
  intro r hr
  simp [fieldDestination]

theorem readSix_output_frame (base : Tape → List Bool) (values : List Nat)
    (suffix : List Bool) (p : Tape) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 6, p ≠ .field j) :
    SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix p = base p := by
  apply SourceFieldArray.sequenceTapes_other _ _ _ hwork
  intro r hr
  exact hfield _

def outputTapes {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) : Tape → List Bool :=
  SourceFieldArray.sequenceTapes .work fieldDestination
    (scanTapes base 0 indexSuffix (encodeWords (clauseWords clause) ++ suffix))
    0 (clauseWords clause) suffix

theorem output_formula {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    outputTapes base clause indexSuffix suffix .formula = base .formula := by
  rw [outputTapes, readSix_output_frame _ _ _ .formula (by decide) (by intro j; simp)]
  exact scanTapes_other _ _ _ _ _ (by decide) (by decide)

theorem output_index {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    outputTapes base clause indexSuffix suffix .index = encodeWord 0 ++ indexSuffix := by
  rw [outputTapes, readSix_output_frame _ _ _ .index (by decide) (by intro j; simp),
    scanTapes_index]

theorem output_work {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    outputTapes base clause indexSuffix suffix .work = suffix := by
  apply readSix_output_work _ _ (clauseWords_length clause) _
  simp

theorem output_field {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) (j : Fin 6) :
    outputTapes base clause indexSuffix suffix (.field j) =
      encodeWord ((clauseWords clause)[j.val]'(by simp)) ++ base (.field j) := by
  rw [outputTapes, readSix_output_field _ _ (clauseWords_length clause)]
  rw [scanTapes_other _ _ _ _ (.field j) (by simp) (by simp)]

theorem output_frame {n : Nat} (base : Tape → List Bool) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) (p : Tape) (hindex : p ≠ .index) (hwork : p ≠ .work)
    (hfield : ∀ j : Fin 6, p ≠ .field j) :
    outputTapes base clause indexSuffix suffix p = base p := by
  rw [outputTapes, readSix_output_frame _ _ _ p hwork hfield]
  exact scanTapes_other _ _ _ _ p hindex hwork

end DFVSGames.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_ContextLoad
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceContextLoad

open Turing DFVSGames.Foundations.Complexity
open MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def program : Label u → TM2.Stmt (fun _ : Tape u Extra => Bool)
    (Label u) (Unit × Option Bool)
  | .copyOut j => Reduction.MachineTransfer.loopAt (.current j) .copyScratch id false
      (.copyOut j) (some (.copyBack j))
  | .copyBack j => MachineCopy.forkLoop .copyScratch (.current j) .index false
      (.copyBack j) (some (.lookup j .copyOut))
  | .lookup j l => placedStatement j (SourceClauseLookup.program l)
  | .clearWork j => MachineDrain.drain .work (.clearWork j) (some (.clearIndex j))
  | .clearIndex j => MachineDrain.drain .index (.clearIndex j) (some (nextLabel j))
  | .done => .halt

theorem placed_step (j : Fin u) (base : Tape u Extra → List Bool)
    (a b : TM2.Cfg (fun _ : SourceClauseLookup.Tape => Bool)
      SourceClauseLookup.Label (Unit × Option Bool))
    (h : TM2.step SourceClauseLookup.program a = some b) :
    TM2.step program (placedConfiguration j base a) =
      some (placedConfiguration j base b) := by
  cases a with
  | mk l state localTapes =>
    cases l with
    | none => contradiction
    | some l =>
      change some (TM2.stepAux (SourceClauseLookup.program l) state localTapes) = some b at h
      cases Option.some.inj h
      change some (TM2.stepAux (placedStatement j (SourceClauseLookup.program l))
        state (fill j base localTapes)) = _
      rw [placed_stepAux]

def lookupOutput (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool) : Tape u Extra → List Bool :=
  fill j base (SourceClauseLookup.outputTapes (base ∘ place j) F.clauses[i.val] suffix
    (encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords)))

theorem cleanup_lookupOutput (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool) :
    Function.update (Function.update
      (lookupOutput j F i (copiedTapes j base) suffix) .work []) .index [] =
      coordinateOutput j F.clauses[i.val] base := by
  funext p
  cases p with
  | formula => simp [lookupOutput, fill, coordinateOutput, SourceClauseLookup.output_formula,
      copiedTapes, place]
  | index => simp [coordinateOutput]
  | work => simp [coordinateOutput]
  | scratch =>
    simp only [Function.update_of_ne (by simp : (Tape.scratch : Tape u Extra) ≠ .index),
      Function.update_of_ne (by simp : (Tape.scratch : Tape u Extra) ≠ .work), lookupOutput, fill,
      coordinateOutput]
    rw [SourceClauseLookup.output_frame _ _ _ _ .scratch (by simp) (by simp) (by intro s; simp)]
    simp [copiedTapes, place]
  | field k s =>
    by_cases hk : k = j
    · subst k
      simp [lookupOutput, fill, coordinateOutput, SourceClauseLookup.output_field,
        copiedTapes, place]
    · simp [lookupOutput, fill, coordinateOutput, hk, copiedTapes]
  | copyScratch => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | current k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | remaining k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]
  | extra k => simp [lookupOutput, fill, coordinateOutput, copiedTapes]

omit [DecidableEq Extra] in
theorem stageTapes_clean (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (hi : base .index = []) (hw : base .work = []) :
    stageTapes F tuple base r .index = [] ∧ stageTapes F tuple base r .work = [] := by
  induction r with
  | zero => exact ⟨hi, hw⟩
  | succ r ih =>
    simp only [stageTapes]
    split
    · exact ⟨rfl, rfl⟩
    · exact ih

omit [DecidableEq Extra] in
theorem stageTapes_field (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (r : Nat) (j : Fin u) (s : Fin 6) :
    stageTapes F tuple base r (.field j s) = if j.val < r then
      encodeWord ((clauseWords F.clauses[(tuple j).val])[s.val]'(by simp)) ++ base (.field j s)
      else base (.field j s) := by
  induction r with
  | zero => simp [stageTapes]
  | succ r ih =>
    simp only [stageTapes]
    split
    next hr =>
      by_cases hj : j = (⟨r, hr⟩ : Fin u)
      · subst j
        simp only [coordinateOutput_field, ih]
        simp
      · rw [coordinateOutput_other_field _ _ _ _ _ hj, ih]
        have hval : j.val ≠ r := by intro h; apply hj; exact Fin.ext h
        have he : j.val < r + 1 ↔ j.val < r := by omega
        simp only [he]
    next hr =>
      rw [ih]
      have hjr : j.val < r := by omega
      have hjr' : j.val < r + 1 := by omega
      simp only [hjr, hjr', ite_true, if_true]

omit [DecidableEq Extra] in
theorem output_variable (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 3) :
    stageTapes F tuple base u (variableField j s) =
      encodeWord (F.clauses[(tuple j).val][s.val].variableIndex.val) ++ base (variableField j s) := by
  rw [variableField, stageTapes_field, ite_eq_left j.isLt, clauseWords_variable]

omit [DecidableEq Extra] in
theorem output_polarity (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 3) :
    stageTapes F tuple base u (polarityField j s) =
      encodeWord (if F.clauses[(tuple j).val][s.val].positive then 1 else 0) ++
        base (polarityField j s) := by
  rw [polarityField, stageTapes_field, ite_eq_left j.isLt, clauseWords_polarity]

end DFVSGames.Foundations.Hastad.SourceContextLoad


noncomputable section

namespace DFVSGames.Foundations.Hastad

open scoped BigOperators
open Finset

theorem walsh_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (𝔼 x, walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, walsh_sum_orthogonality]
  split_ifs <;> simp

theorem sign_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → Bool) :
    (∑ s, coefficient (fun x => bitSign (f x)) s ^ 2) = 1 := by
  rw [walsh_parseval]
  simp

end DFVSGames.Foundations.Hastad
end


noncomputable section

namespace DFVSGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem walsh_autocorrelation (B : Cube J → ℝ) (h : Cube J) :
    (𝔼 g, B g * B (cubeXor g h)) =
      ∑ s, coefficient B s ^ 2 * walsh s h := by
  conv_lhs =>
    enter [2, g, 2]
    rw [← walsh_inversion B (cubeXor g h)]
  simp_rw [Finset.mul_sum, walsh_xor]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm : (fun g => B g * (coefficient B s * (walsh s g * walsh s h))) =
      (fun g => (coefficient B s * walsh s h) * (B g * walsh s g)) := by
    funext g
    ring
  rw [hterm, ← Finset.mul_expect]
  change (coefficient B s * walsh s h) * coefficient B s = _
  ring

theorem testBias_fourier (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → ℝ) :
    testBias ε π A B = ∑ s,
      projectedCoefficient π A s * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
  unfold testBias thirdQuery
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  conv_lhs =>
    enter [2, f]
    rw [Finset.sum_comm]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hterm (f : Cube I) :
      (∑ μ, noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * walsh s (cubeXor (fun y => f (π y)) μ))) =
      (A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2 *
        (1 - 2 * ε) ^ (support s).card := by
    simp_rw [walsh_xor]
    have heq (μ : Cube J) : noiseWeight ε μ * A f *
        (coefficient B s ^ 2 * (walsh s (fun y => f (π y)) * walsh s μ)) =
      ((A f * walsh s (fun y => f (π y))) * coefficient B s ^ 2) *
        (noiseWeight ε μ * walsh s μ) := by ring
    simp_rw [heq]
    rw [← Finset.mul_sum, noise_walsh]
  simp_rw [hterm, ← Finset.expect_mul]
  rfl

end DFVSGames.Foundations.Hastad
end


noncomputable section

namespace DFVSGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem coefficient_zero_of_odd (F : Cube I → ℝ)
    (hF : ∀ f, F (cubeFlip f) = -F f) :
    coefficient F (fun _ => false) = 0 := by
  have hs : (∑ f, F f) = 0 := by
    have h := sum_cubeFlip F
    simp_rw [hF, Finset.sum_neg_distrib] at h
    linarith
  simp [coefficient, walsh, bitSign, Fintype.expect_eq_sum_div_card, hs]

theorem coefficient_sign_zero_of_folded (A : Cube I → Bool)
    (hA : ∀ f, A (cubeFlip f) = !(A f)) :
    coefficient (fun f => bitSign (A f)) (fun _ => false) = 0 := by
  apply coefficient_zero_of_odd
  intro f
  rw [hA, bitSign_not]

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_flip (i₀ : I) (table : HalfCube i₀ → Bool) (f : Cube I) :
    foldedAnswer i₀ table (cubeFlip f) = !(foldedAnswer i₀ table f) := by
  unfold foldedAnswer
  rw [canonicalInput_flip]
  change (table (canonicalInput i₀ f) ^^ !(f i₀)) =
    !(table (canonicalInput i₀ f) ^^ f i₀)
  cases table (canonicalInput i₀ f) <;> cases f i₀ <;> rfl

theorem foldedAnswer_zero_coefficient (i₀ : I) (table : HalfCube i₀ → Bool) :
    coefficient (fun f => bitSign (foldedAnswer i₀ table f)) (fun _ => false) = 0 :=
  coefficient_sign_zero_of_folded _ (foldedAnswer_flip i₀ table)

omit [Fintype I] [DecidableEq I] in
theorem foldedAnswer_dictator (i₀ i : I) (f : Cube I) :
    foldedAnswer i₀ (fun h => h.val i) f = f i := by
  cases hf : f i₀ <;> cases hi : f i <;>
    simp [foldedAnswer, canonicalInput, representative, cubeFlip, hf, hi]

theorem walsh_coordinateMask (s : Cube I) (i : I) :
    walsh s (coordinateMask i) = bitSign (s i) := by
  unfold walsh
  rw [Finset.prod_eq_single i]
  · simp [coordinateMask]
  · intro j _ hj
    simp [coordinateMask, hj, bitSign]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem walsh_cubeToggle (s : Cube I) (i : I) (f : Cube I) (hs : s i = true) :
    walsh s (cubeToggle i f) = -walsh s f := by
  rw [cubeToggle, walsh_xor, walsh_coordinateMask, hs]
  simp [bitSign]

theorem conditioned_coefficient_zero_invalid (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I) (i : I)
    (hi : valid i = false) (hs : s i = true) :
    coefficient (fun f => B (restrictQuery valid f)) s = 0 := by
  have hsum := sum_cubeToggle i (fun f => B (restrictQuery valid f) * walsh s f)
  simp_rw [restrictQuery_cubeToggle valid i hi, walsh_cubeToggle s i _ hs,
    mul_neg, Finset.sum_neg_distrib] at hsum
  have hz : (∑ f, B (restrictQuery valid f) * walsh s f) = 0 := by linarith
  simp [coefficient, Fintype.expect_eq_sum_div_card, hz]

theorem conditioned_coefficient_support (valid : I → Bool)
    (B : Cube {i : I // valid i = true} → ℝ) (s : Cube I)
    (hne : coefficient (fun f => B (restrictQuery valid f)) s ≠ 0) :
    ∀ i ∈ support s, valid i = true := by
  intro i hi
  have hs := (Finset.mem_filter.mp hi).2
  cases hv : valid i
  · exact False.elim (hne (conditioned_coefficient_zero_invalid valid B s i hv hs))
  · rfl

omit [Fintype I] [DecidableEq I] in
theorem conditionedFoldedAnswer_dictator (valid : I → Bool)
    (i₀ i : {i : I // valid i = true}) (f : Cube I) :
    conditionedFoldedAnswer valid i₀ (fun h => h.val i) f = f i.val := by
  exact foldedAnswer_dictator i₀ i (restrictQuery valid f)

end DFVSGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_CloneGap
attribute [-instance] _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.FoldedEquation

open DFVSGames.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

theorem equation_satisfied (π : J → I) (i₀ : I) (j₀ : J)
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (equation π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ foldedAnswer j₀ tableB g ^^
        foldedAnswer j₀ tableB (thirdQuery π f g μ)) := by
  change ((tableA (canonicalInput i₀ f) ^^ tableB (canonicalInput j₀ g) ^^
      tableB (canonicalInput j₀ (thirdQuery π f g μ))) == rhsCorrection π i₀ j₀ f μ) = _
  rw [← correction_eq π i₀ j₀ f g μ]
  exact xor_corrections _ _ _ _ _ _

theorem satisfied_repeated_right {Name : Type} (e : Equation Name)
    (assignment : Name → Bool) (h : e.second = e.third) :
    satisfied e assignment = (assignment e.first == e.rhs) := by
  unfold satisfied
  rw [← h]
  cases assignment e.first <;> cases assignment e.second <;> cases e.rhs <;> rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedEquation_satisfied (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedEquation valid π i₀ j₀ f g μ) (storedAssignment tableA tableB) =
      !(foldedAnswer i₀ tableA f ^^ conditionedFoldedAnswer valid j₀ tableB g ^^
        conditionedFoldedAnswer valid j₀ tableB (thirdQuery π f g μ)) := by
  unfold conditionedEquation
  rw [equation_satisfied]
  simp only [conditionedFoldedAnswer, restrict_thirdQuery]

end DFVSGames.Foundations.Hastad.FoldedEquation


namespace DFVSGames.Foundations.Hastad

open DFVSGames.Reduction.CloneGap
open scoped BigOperators

theorem satisfied_mapEquation {Name Name' : Type} (rename : Name → Name')
    (e : Equation Name) (assignment : Name' → Bool) :
    satisfied (mapEquation rename e) assignment = satisfied e (assignment ∘ rename) := rfl

namespace EmptyContext

variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

theorem equation_satisfied (i₀ : I) (assignment : Address i₀ → Bool) (f : Cube I) :
    satisfied (equation i₀ f) assignment =
      !(foldedAnswer i₀ (fun h => assignment (.inl h)) f) := by
  rw [FoldedEquation.satisfied_repeated_right (equation i₀ f) assignment rfl]
  change (assignment (.inl (canonicalInput i₀ f)) == f i₀) =
    !(assignment (.inl (canonicalInput i₀ f)) ^^ f i₀)
  cases assignment (.inl (canonicalInput i₀ f)) <;> cases f i₀ <;> rfl

end EmptyContext
end DFVSGames.Foundations.Hastad


noncomputable section

namespace DFVSGames.Foundations.Hastad

open scoped BigOperators
open DFVSGames.Reduction.FiniteNoise

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem noise_coordinate_sign (ε : ℝ) (j : J) :
    (∑ μ : Cube J, noiseWeight ε μ * bitSign (μ j)) = 1 - 2 * ε := by
  have hs : support (coordinateMask j) = {j} := by
    ext k
    simp [support, coordinateMask]
  have h := noise_walsh ε (coordinateMask j)
  simp_rw [walsh_symm (coordinateMask j), walsh_coordinateMask] at h
  simpa only [hs, Finset.card_singleton, pow_one] using h

theorem noise_coordinate_false (ε : ℝ) (j : J) :
    (∑ μ : Cube J, noiseWeight ε μ * if μ j then (0 : ℝ) else 1) = 1 - ε := by
  have hind (b : Bool) : (if b then (0 : ℝ) else 1) =
      (1 + bitSign b) * (2 : ℝ)⁻¹ := by
    cases b <;> norm_num [bitSign]
  have ht (μ : Cube J) : noiseWeight ε μ * (if μ j then (0 : ℝ) else 1) =
      (noiseWeight ε μ + noiseWeight ε μ * bitSign (μ j)) * (2 : ℝ)⁻¹ := by
    rw [hind]
    ring
  simp_rw [ht]
  rw [← Finset.sum_mul, Finset.sum_add_distrib, noiseWeight_sum, noise_coordinate_sign]
  ring

theorem testAcceptance_dictator (ε : ℝ) (π : J → I)
    (i : I) (j : J) (hπ : π j = i) :
    testAcceptance ε π (fun f => f i) (fun g => g j) = 1 - ε := by
  have hg (f : Cube I) (μ : Cube J) :
      (𝔼 g : Cube J, if f i ^^ g j ^^ (thirdQuery π f g μ) j then (0 : ℝ) else 1) =
        if μ j then 0 else 1 := by
    calc
      _ = 𝔼 _g : Cube J, if μ j then (0 : ℝ) else 1 := by
        apply Finset.expect_congr rfl
        intro g _
        rw [dictator_test_parity π i j hπ f g μ]
      _ = _ := Fintype.expect_const _
  change (𝔼 f : Cube I, ∑ μ : Cube J, noiseWeight ε μ *
    (𝔼 g : Cube J, if f i ^^ g j ^^ (thirdQuery π f g μ) j then (0 : ℝ) else 1)) = _
  simp_rw [hg]
  rw [Fintype.expect_const]
  exact noise_coordinate_false ε j

end DFVSGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_Tape
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceContexts

open Target PCP

theorem honestJ_valid (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    validJ F c (honestJ F c assignment) = true := by
  apply (validJ_eq_true_iff F c _).mpr
  constructor
  · intro t
    exact (honest_satisfies _ assignment).trans (hs _ (List.getElem_mem _))
  · intro t t' s s' hname
    simp only [honestJ, honest_answerAt]
    exact congrArg assignment hname

theorem pi_honest (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (v : VariableContext F u) (assignment : Fin F.«variables» → Bool)
    (hsupport : ∀ t, ∃ s, nameAt (clauseAt F (c t)) s = v t) :
    pi F c v (honestJ F c assignment) = honestI F v assignment := by
  funext t
  exact (honest_answerAt _ assignment _).trans
    (congrArg assignment (canonicalSlot_name _ _ (hsupport t)))

theorem pi_honest_sampled (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (assignment : Fin F.«variables» → Bool) :
    pi F c (sampledVariables F c s) (honestJ F c assignment) =
      honestI F (sampledVariables F c s) assignment :=
  pi_honest F c _ assignment (sampledVariables_supported F c s)

end DFVSGames.Foundations.Hastad.SourceContexts


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Occurrences
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceOccurrences

open DFVSGames.Reduction.CloneGap
open scoped BigOperators

section LocalEquations

variable {V C I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditionedOccurrence_satisfied
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (v : V) (c : C) (valid : J → Bool) (π : J → I)
    (i₀ : I) (j₀ : {j : J // valid j = true})
    (bits : Fin (globalEncoding vE cE iE jE).size → Bool)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedOccurrence vE cE iE jE v c valid π i₀ j₀ f g μ) bits =
      !(foldedAnswer i₀ (fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))) f ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) g ^^
        conditionedFoldedAnswer valid j₀
          (fun h => bits ((globalEncoding vE cE iE jE).code
            (.inr (.inl (c, extendRestricted valid h.val))))) (thirdQuery π f g μ)) := by
  rw [conditionedOccurrence, satisfied_mapEquation]
  let tableA : HalfCube i₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code (.inl (v, h.val)))
  let tableB : HalfCube j₀ → Bool :=
    fun h => bits ((globalEncoding vE cE iE jE).code
      (.inr (.inl (c, extendRestricted valid h.val))))
  have hbits : bits ∘ localAddress vE cE iE jE v c valid i₀ j₀ =
      FoldedEquation.storedAssignment tableA tableB := by
    funext a
    cases a <;> rfl
  rw [hbits]
  exact FoldedEquation.conditionedEquation_satisfied valid π i₀ j₀ tableA tableB f g μ

end LocalEquations

theorem occurrenceList_acceptance {Tape Name : Type} [Fintype Tape]
    (tape : Encoding Tape) (emit : Tape → Equation Name) (bits : Name → Bool) :
    ((occurrenceList tape emit).countP (fun e => satisfied e bits) : ℝ) /
        (occurrenceList tape emit).length =
      𝔼 x, if satisfied (emit x) bits then (1 : ℝ) else 0 := by
  rw [occurrenceList_length, Fintype.expect_eq_sum_div_card, tape.card_eq_size]
  congr 1
  simpa only [occurrenceList, List.countP_map, Function.comp_def] using
    countP_enumerate tape (fun x => satisfied (emit x) bits)


open SourceContexts
open DFVSGames.Reduction.FiniteNoise

theorem contextEquation_satisfied (F : Target.Formula) (u D : ℕ)
    (c : ClauseContext F u) (v : VariableContext F u)
    (t : SourceTape.TestTape (I u) (J u) D) (bits : Fin (nBits F u) → Bool) :
    satisfied (contextEquation F u D c v t) bits =
      !(leftResponse F u bits v t.1 ^^ rightResponse F u bits c t.2.2 ^^
        rightResponse F u bits c (thirdQuery (pi F c v) t.1 t.2.2 (realizedNoise t.2.1))) := by
  cases ha : rightAnchor F c with
  | none =>
    simp only [contextEquation, ha, satisfied_mapEquation, EmptyContext.equation_satisfied,
      rightResponse, Bool.xor_false]
    rfl
  | some j₀ =>
    simp only [contextEquation, ha, rightResponse]
    exact conditionedOccurrence_satisfied (variableEncoding F u) (clauseEncoding F u)
      (iEncoding u) (jEncoding u) v c (validJ F c) (pi F c v) (leftAnchor u) j₀
      bits t.1 t.2.2 (realizedNoise t.2.1)

theorem rawSourceList_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (bits : Fin (nBits F u) → Bool) :
    ((rawSourceList F u D).countP (fun e => satisfied e bits) : ℝ) /
        (rawSourceList F u D).length =
      𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
        testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
          (leftResponse F u bits (sampledVariables F c s)) (rightResponse F u bits c) := by
  rw [rawSourceList, occurrenceList_acceptance, SourceTape.expect_prod]
  rw [SourceTape.expect_prod]
  apply Finset.expect_congr rfl
  intro c _
  apply Finset.expect_congr rfl
  intro s _
  rw [← SourceTape.tapeAcceptance_eq_testAcceptance hD]
  unfold SourceTape.tapeAcceptance
  apply Finset.expect_congr rfl
  intro t _
  rw [sourceEquation, contextEquation_satisfied]
  cases h : leftResponse F u bits (sampledVariables F c s) t.1 ^^
    rightResponse F u bits c t.2.2 ^^
      rightResponse F u bits c
        (thirdQuery (pi F c (sampledVariables F c s)) t.1 t.2.2 (realizedNoise t.2.1)) <;> rfl

theorem emptyFormulaEquation_satisfied (F : Target.Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) :
    satisfied (emptyFormulaEquation F u) bits = !(bits (dummyIndex F u)) := by
  cases h : bits (dummyIndex F u) <;> simp [emptyFormulaEquation, satisfied, h]


end DFVSGames.Foundations.Hastad.SourceOccurrences


namespace DFVSGames.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

def signatureEquiv (u : ℕ) :
    Signature u ≃ (Position u → Bool) × NameProfile u × SlotContext u where
  toFun σ := (σ.signs, σ.sameName, σ.selected)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv σ := by cases σ; rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

instance signatureFintype (u : ℕ) : Fintype (Signature u) :=
  Fintype.ofEquiv ((Position u → Bool) × NameProfile u × SlotContext u)
    (signatureEquiv u).symm

def signatureValid {u : ℕ} (σ : Signature u) (j : J u) : Bool :=
  decide ((∀ t, signatureSatisfies σ j t = true) ∧
    ∀ t t' s s', σ.sameName (t, s) (t', s') = true →
      answerAt (j t) s = answerAt (j t') s')

theorem signature_validJ (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureValid (ofContext F c s) j = validJ F c j := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hs := of_decide_eq_true h
    apply (validJ_eq_true_iff F c j).mpr
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).symm.trans (hs.1 t)
    · intro t t' a a' hname
      apply hs.2 t t' a a'
      exact decide_eq_true hname
  · intro h
    have hs := (validJ_eq_true_iff F c j).mp h
    apply decide_eq_true
    constructor
    · intro t
      exact (signatureSatisfies_ofContext F c s j t).trans (hs.1 t)
    · intro t t' a a' heq
      exact hs.2 t t' a a' (of_decide_eq_true heq)

def signatureCanonicalSlot {u : ℕ} (σ : Signature u) (t : Fin u) : Slot :=
  if σ.sameName (t, .first) (t, σ.selected t) then .first
  else if σ.sameName (t, .second) (t, σ.selected t) then .second else .third

def signatureProjection {u : ℕ} (σ : Signature u) (j : J u) : I u :=
  fun t => answerAt (j t) (signatureCanonicalSlot σ t)

theorem signatureCanonicalSlot_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (t : Fin u) :
    signatureCanonicalSlot (ofContext F c s) t =
      canonicalSlot (clauseAt F (c t)) (sampledVariables F c s t) := by
  by_cases hfirst : nameAt (clauseAt F (c t)) .first =
      nameAt (clauseAt F (c t)) (s t)
  · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
      occurrenceName, sampledVariables, hfirst]
  · by_cases hsecond : nameAt (clauseAt F (c t)) .second =
        nameAt (clauseAt F (c t)) (s t)
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]
    · simp [signatureCanonicalSlot, canonicalSlot, ofContext, contextNameProfile,
        occurrenceName, sampledVariables, hfirst, hsecond]

theorem signature_pi (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (j : J u) :
    signatureProjection (ofContext F c s) j = pi F c (sampledVariables F c s) j := by
  funext t
  simp only [signatureProjection, signatureCanonicalSlot_ofContext, pi]

end DFVSGames.Foundations.Hastad.SourceLocalSignature

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Bounds
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceBounds

open Target
open DFVSGames.Reduction

theorem formulaBits_length (F : Formula) :
    (Complexity.formulaBits F).length = F.«variables» + F.clauses.length + 2 +
      (Complexity.encodeWords (F.clauses.flatMap Complexity.clauseWords)).length := by
  simp only [Complexity.formulaBits, Complexity.formulaWords,
    Complexity.encodeWords_append, List.length_append, Complexity.encodeWords,
    Complexity.encodeWord_length, List.length_nil]
  omega

theorem formulaBits_length_ge_variables (F : Formula) :
    F.«variables» ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_clauses (F : Formula) :
    F.clauses.length ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem formulaBits_length_ge_two (F : Formula) :
    2 ≤ (Complexity.formulaBits F).length := by
  rw [formulaBits_length]
  omega

theorem one_le_input_power (F : Formula) (u : ℕ) :
    1 ≤ (Complexity.formulaBits F).length ^ u := by
  apply Nat.one_le_pow
  have h := formulaBits_length_ge_two F
  omega

theorem bitCountFormula_le_input (F : Formula) (u : ℕ) :
    bitCountFormula F.«variables» F.clauses.length u ≤
      bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have hn := Nat.pow_le_pow_left (formulaBits_length_ge_variables F) u
  have hm := Nat.pow_le_pow_left (formulaBits_length_ge_clauses F) u
  have hpos := one_le_input_power F u
  unfold bitCountFormula bitCoefficient
  calc
    _ ≤ (Complexity.formulaBits F).length ^ u * 2 ^ (2 ^ u) +
        (Complexity.formulaBits F).length ^ u * 2 ^ (8 ^ u) +
        (Complexity.formulaBits F).length ^ u :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.mul_le_mul_right _ hm)) hpos
    _ = _ := by ring

open SourceOccurrences SourceContexts

theorem testTapeEncoding_size (u D : ℕ) :
    (SourceOccurrences.testTapeEncoding u D).size =
      2 ^ (2 ^ u) * (D ^ (8 ^ u) * 2 ^ (8 ^ u)) := rfl

theorem nBits_le_input (F : Formula) (u : ℕ) :
    nBits F u ≤ bitCoefficient u * (Complexity.formulaBits F).length ^ u := by
  have h := bitCountFormula_le_input F u
  simpa only [nBits_eq, bitCountFormula, Nat.add_assoc] using h

end DFVSGames.Foundations.Hastad.SourceBounds


namespace DFVSGames.Foundations.Hastad.SourceSignLoad

open Turing
open SourceLocalSignature
open DFVSGames.Foundations.Complexity

def positions (u : ℕ) : List (Position u) :=
  ((SourceOccurrences.Encoding.fin u).prod SourceOccurrences.slotEncoding).enumerate

theorem mem_positions {u : ℕ} (p : Position u) : p ∈ positions u :=
  SourceOccurrences.Encoding.mem_enumerate _ p

def fillSigns {u : ℕ} (values initial : Position u → Bool)
    (cells : List (Position u)) : Position u → Bool :=
  cells.foldl (fun signs p => Function.update signs p (values p)) initial

theorem fillSigns_apply {u : ℕ} (values initial : Position u → Bool)
    (cells : List (Position u)) (p : Position u) :
    fillSigns values initial cells p = if p ∈ cells then values p else initial p := by
  induction cells generalizing initial with
  | nil => simp [fillSigns]
  | cons q cells ih =>
    change fillSigns values (Function.update initial q (values q)) cells p = _
    rw [ih]
    by_cases hp : p ∈ cells
    · simp [hp]
    · by_cases hpq : p = q
      · subst q; simp [hp]
      · simp [hp, hpq]

theorem fillSigns_positions {u : ℕ} (values initial : Position u → Bool) :
    fillSigns values initial (positions u) = values := by
  funext p
  rw [fillSigns_apply]
  simp only [mem_positions, ↓reduceIte]


variable {u : ℕ} {K Λ τ : Type} [DecidableEq K]

abbrev State (u : ℕ) (τ : Type) := Signature u × τ

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State u τ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def peekChain (field : Position u → K) (exit : Option Λ) :
    List (Position u) → TM2.Stmt (Alphabet (K := K)) Λ (State u τ)
  | [] => finish exit
  | p :: rest =>
    .peek (field p) (fun state head =>
      ({state.1 with signs := Function.update state.1.signs p (head.getD false)}, state.2))
      (peekChain field exit rest)

def statement (field : Position u → K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State u τ) :=
  peekChain field exit (positions u)

def readSigns (field : Position u → K) (tapes : K → List Bool) : Position u → Bool :=
  fun p => (tapes (field p)).head?.getD false

theorem stepAux_peekChain (field : Position u → K) (exit : Option Λ)
    (cells : List (Position u)) (initial : Signature u) (ambient : τ)
    (tapes : K → List Bool) :
    TM2.stepAux (peekChain field exit cells) (initial, ambient) tapes =
      ⟨exit, ({initial with signs := fillSigns (readSigns field tapes) initial.signs cells},
        ambient), tapes⟩ := by
  induction cells generalizing initial with
  | nil => cases exit <;> rfl
  | cons p rest ih =>
    simp only [peekChain, TM2.stepAux]
    rw [ih]
    rfl

theorem stepAux_statement (field : Position u → K) (exit : Option Λ)
    (initial : Signature u) (ambient : τ) (tapes : K → List Bool) :
    TM2.stepAux (statement field exit) (initial, ambient) tapes =
      ⟨exit, ({initial with signs := readSigns field tapes}, ambient), tapes⟩ := by
  rw [statement, stepAux_peekChain, fillSigns_positions]

omit [DecidableEq K] in
theorem readSigns_of_unary (field : Position u → K) (tapes : K → List Bool)
    (values : Position u → Bool) (suffix : Position u → List Bool)
    (hfields : ∀ p, tapes (field p) = encodeWord (if values p then 1 else 0) ++ suffix p) :
    readSigns field tapes = values := by
  funext p
  rw [readSigns, hfields]
  cases values p <;> rfl


end DFVSGames.Foundations.Hastad.SourceSignLoad

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SignaturePrepare
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature
open DFVSGames.Foundations.Complexity

variable {u : ℕ} {Extra τ : Type}

def polarityField (p : Position u) : Arena u Extra :=
  SourceContextLoad.polarityField p.1 (slotEncoding.code p.2)

end DFVSGames.Foundations.Hastad.SourceSignaturePrepare


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_LocalEquation
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open DFVSGames.Reduction.CloneGap
open DFVSGames.Reduction.FiniteNoise

def signatureEncoding (u : ℕ) : Encoding (Signature u) :=
  let position := (Encoding.fin u).prod slotEncoding
  let fields := (position.function Encoding.bool).prod
    ((position.function (position.function Encoding.bool)).prod (slotContextEncoding u))
  ⟨fields.size, (signatureEquiv u).trans fields.code⟩

end DFVSGames.Foundations.Hastad.SourceLocalEquation


namespace DFVSGames.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences SourceLocalEquation SourceLocalSignature
open SourceAddressArithmetic
open DFVSGames.Reduction.CloneGap

def baseValue (F : Formula) (u : ℕ) (c : ClauseContext F u)
    (v : VariableContext F u) (side : Fin 3) : ℕ :=
  if side = 0 then 2 ^ (2 ^ u) * ((variableEncoding F u).code v).val
  else if side = 1 then F.«variables» ^ u * 2 ^ (2 ^ u) +
    2 ^ (8 ^ u) * ((clauseEncoding F u).code c).val
  else F.«variables» ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u)

end DFVSGames.Foundations.Hastad.SourceAddressDescriptors


namespace DFVSGames.Foundations.Hastad.SourceEquationEmit

open Turing Complexity
open SourceAddressDescriptors
open DFVSGames.Reduction.CloneGap
open DFVSGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def statement (sources : Fin 3 → K) (destination scratch : K)
    (e : Equation Descriptor) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => pushWord destination (encodeWord (rhsBit e)).reverse
      (.goto fun _ => labels .thirdDrain)
  | .thirdDrain => Reduction.MachineTransfer.loopAt (sources e.third.1) scratch id false
      (labels .thirdDrain) (some (labels .thirdFork))
  | .thirdFork => MachineCopy.forkLoop scratch (sources e.third.1) destination false
      (labels .thirdFork) (some (labels .thirdEmit))
  | .thirdEmit => MachineRegisterEmit.emitStatement destination e.third.2
      (some (labels .secondDrain))
  | .secondDrain => Reduction.MachineTransfer.loopAt (sources e.second.1) scratch id false
      (labels .secondDrain) (some (labels .secondFork))
  | .secondFork => MachineCopy.forkLoop scratch (sources e.second.1) destination false
      (labels .secondFork) (some (labels .secondEmit))
  | .secondEmit => MachineRegisterEmit.emitStatement destination e.second.2
      (some (labels .firstDrain))
  | .firstDrain => Reduction.MachineTransfer.loopAt (sources e.first.1) scratch id false
      (labels .firstDrain) (some (labels .firstFork))
  | .firstFork => MachineCopy.forkLoop scratch (sources e.first.1) destination false
      (labels .firstFork) (some (labels .firstEmit))
  | .firstEmit => MachineRegisterEmit.emitStatement destination e.first.2 exit

end DFVSGames.Foundations.Hastad.SourceEquationEmit


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_LoopInit
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceLoopInit

open Turing DFVSGames.Foundations.Complexity
open MachineComposition SourceMachine

variable {u : Nat} {Extra : Type}

def headerDestination (r : Nat) : Tape u Extra := if r = 0 then variableHeader else clauseHeader

def program : Label u → TM2.Stmt (fun _ : Tape u Extra => Bool) (Label u) (Unit × Option Bool)
  | .inputCopyOut => Reduction.MachineTransfer.loopAt .formula .scratch id false
      .inputCopyOut (some .inputCopyBack)
  | .inputCopyBack => MachineCopy.forkLoop .scratch .formula .work false
      .inputCopyBack (some (readStart 0))
  | .read slot => if slot.1.val < 2 then
      if slot.2 then fieldLoop .work (headerDestination slot.1.val) (.read (slot.1, true))
        (some (readStart (slot.1.val + 1)))
      else fieldStart (headerDestination slot.1.val) (.read (slot.1, true))
    else SourceFieldArray.finish .work (some .clearWork)
  | .clearWork => MachineDrain.drain .work .clearWork (some (labelAt 0))
  | .seed j => .push (.current j) (fun _ => false) (.goto fun _ => .digitCopyOut j)
  | .digitCopyOut j => Reduction.MachineTransfer.loopAt clauseHeader .copyScratch id false
      (.digitCopyOut j) (some (.digitCopyBack j))
  | .digitCopyBack j => MachineCopy.forkLoop .copyScratch clauseHeader (.remaining j) false
      (.digitCopyBack j) (some (.trim j))
  | .trim j => .pop (.remaining j) (fun state _ => state) (.goto fun _ => labelAt (j.val + 1))
  | .done => .halt

theorem atReadStart (r : Nat) (hr : r < 2) :
    program (u := u) (Extra := Extra) (readStart r) =
      fieldStart (headerDestination r) (readLoop r) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadLoop (r : Nat) (hr : r < 2) :
    program (u := u) (Extra := Extra) (readLoop r) = fieldLoop .work (headerDestination r)
      (readLoop r) (some (readStart (r + 1))) := by
  simp [program, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

theorem atReadDone : program (u := u) (Extra := Extra) (readStart 2) =
    SourceFieldArray.finish .work (some .clearWork) := by
  simp [program, readStart]

variable [DecidableEq Extra]

def copiedInput (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  Function.update base .work (base .formula)

def readOutput (F : Target.Formula) (base : Tape u Extra → List Bool) : Tape u Extra → List Bool :=
  SourceFieldArray.sequenceTapes .work headerDestination (copiedInput base) 0
    [F.«variables», F.clauses.length] (encodeWords (F.clauses.flatMap clauseWords))

theorem clear_readOutput (F : Target.Formula) (base : Tape u Extra → List Bool) :
    Function.update (readOutput F base) .work [] = headerOutput F base := by
  funext p
  cases p <;> simp [readOutput, headerOutput, SourceFieldArray.sequenceTapes,
    afterField, fieldTapes, copiedInput, headerDestination, variableHeader, clauseHeader]
  rename_i e
  cases e with
  | inl h => cases h <;> simp
  | inr e => simp

theorem readOutput_work (F : Target.Formula) (base : Tape u Extra → List Bool) :
    readOutput F base .work = encodeWords (F.clauses.flatMap clauseWords) := by
  simp [readOutput, SourceFieldArray.sequenceTapes, afterField, fieldTapes,
    headerDestination, variableHeader, clauseHeader, encodeWords]

end DFVSGames.Foundations.Hastad.SourceLoopInit


namespace DFVSGames.Foundations.Hastad.SourceRankPhase

open Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceAddressArithmetic

theorem horner_value_sum (radix : Nat) (digits : Nat → Nat) (n : Nat) :
    MachineHorner.value radix digits n =
      ∑ i ∈ Finset.range n, digits i * radix ^ (n - 1 - i) := by
  induction n with
  | zero => simp [MachineHorner.value]
  | succ n ih =>
    rw [MachineHorner.value, ih, Finset.sum_range_succ, Finset.mul_sum]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show n - i = (n - 1 - i) + 1 by omega, pow_succ]
    ac_rfl

theorem horner_reverse_eq_rank {width : Nat} (radix : Nat) (digits : Fin width → Nat) :
    MachineHorner.value radix (reverseDigits digits) width = rank radix digits := by
  rw [horner_value_sum, Finset.sum_range]
  calc
    (∑ i : Fin width, reverseDigits digits i.val * radix ^ (width - 1 - i.val)) =
        ∑ i : Fin width, digits i.rev * radix ^ i.rev.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [reverseDigits_apply]
      have he : width - 1 - i.val = i.rev.val := by
        simp only [Fin.rev]
        omega
      rw [he]
    _ = rank radix digits := by
      simpa only [rank, Fin.revPerm_apply] using
        Equiv.sum_comp (Fin.revPerm (n := width)) (fun i => digits i * radix ^ i.val)

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

omit [DecidableEq K] in
theorem clean_reverseSlots (slots : MachineHorner.Layout width ↪ K) (base : K → List Bool)
    (clean : MachineHorner.Clean slots base) : MachineHorner.Clean (reverseSlots slots) base where
  accA := by simpa only [reverseSlots_control] using clean.accA
  accB := by simpa only [reverseSlots_control] using clean.accB
  counter := by simpa only [reverseSlots_control] using clean.counter
  scratch := by simpa only [reverseSlots_control] using clean.scratch


variable {u : Nat} {Extra : Type}

theorem selectedDigits_loaded (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (controls : Fin 6 ↪ Extra) (base : SourceContextLoad.Tape u Extra → List Bool)
    (empty : ∀ i, base (SourceContextLoad.variableField i (slotEncoding.code (selected i))) = [])
    (i : Fin u) :
    SourceContextLoad.stageTapes F c base u (variableSlots controls selected (.inr i)) =
      encodeWord (sampledVariables F c selected i).val := by
  rw [variableSlots_digit]
  dsimp only [slotEncoding] at empty ⊢
  rw [SourceContextLoad.output_variable, empty i, List.append_nil]
  congr 1
  cases hs : selected i <;> simp [sampledVariables, PCP.nameAt, PCP.clauseAt, hs] <;> rfl


end DFVSGames.Foundations.Hastad.SourceRankPhase


namespace DFVSGames.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature

variable {u D : Nat} {Extra : Type}

def rankControls (header : SourceLoopInit.HeaderTape) : Fin 6 ↪ BodyExtra Extra where
  toFun
    | 0 => .inl header
    | 1 => .inr .accA
    | 2 => .inr .accB
    | 3 => .inr .rank
    | 4 => .inr .counter
    | 5 => .inr .arithScratch
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def clauseRankSlots : MachineHorner.Layout u ↪ Arena u Extra :=
  SourceRankPhase.clauseSlots (rankControls .clauseCount)

def variableRankSlots (selected : SlotContext u) : MachineHorner.Layout u ↪ Arena u Extra :=
  SourceRankPhase.variableSlots (rankControls .variableCount) selected

def baseSlots (right : Bool) : MachineHorner.Layout 2 ↪ Arena u Extra where
  toFun
    | .inl 0 => workTape .rank
    | .inl 1 => workTape .accA
    | .inl 2 => workTape .accB
    | .inl 3 => workTape (if right then .rightBase else .leftBase)
    | .inl 4 => workTape .counter
    | .inl 5 => workTape .arithScratch
    | .inr 0 => workTape .coefficient
    | .inr 1 => workTape (if right then .leftBlock else .zero)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]
      | inr b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]
    | inr a =>
      cases b with
      | inl b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]
      | inr b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]

def querySources : Fin 3 → Arena u Extra
  | 0 => workTape .leftBase
  | 1 => workTape .rightBase
  | 2 => workTape .dummy

def queryLayout : SourceTestAppend.Layout (Arena u Extra) where
  sources := querySources
  temporary := workTape .queryTemporary
  scratch := workTape .queryScratch
  accumulator := workTape .accumulator
  sourceTemporary side := by fin_cases side <;> simp [querySources, workTape]
  sourceScratch side := by fin_cases side <;> simp [querySources, workTape]
  sourceAccumulator side := by fin_cases side <;> simp [querySources, workTape]
  temporaryScratch := by simp [workTape]
  temporaryAccumulator := by simp [workTape]
  scratchAccumulator := by simp [workTape]

end DFVSGames.Foundations.Hastad.SourceRuntimeModel

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_CookLevin_PolynomialMachine
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

noncomputable section

theorem bitValue_eq_nBits (F : Target.Formula) (u : Nat) :
    bitValue u F.«variables» F.clauses.length = SourceOccurrences.nBits F u := by
  rw [SourceOccurrences.nBits_eq]
  simp [bitValue, dummyValue, leftValue, rightValue, Nat.mul_comm, Nat.add_assoc]

theorem occurrenceValue_eq_length (F : Target.Formula) (u D : Nat)
    (hm : 0 < F.clauses.length) :
    occurrenceValue u D F.clauses.length = (SourceOccurrences.sourceList F u D).length := by
  have hne : F.clauses ≠ [] := by intro h; simp [h] at hm
  have hfalse : ¬ F.clauses.isEmpty = true := by simpa using hne
  simp only [SourceOccurrences.sourceList, ite_eq_right hfalse]
  rw [SourceOccurrences.rawSourceList_length]
  unfold occurrenceValue
  rw [SourceBounds.testTapeEncoding_size]
  ac_rfl

variable {u D : Nat} {K Λ σ : Type}

structure Clean (slots : Layout u D ↪ K) (base : K → List Bool) : Prop where
  left : base (control slots .leftBlockSize) = []
  right : base (control slots .rightTemporary) = []
  dummy : base (control slots .dummyIndex) = []
  bits : base (control slots .bitCount) = []
  occurrences : base (control slots .occurrenceCount) = []
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients u D, base (slots (.inr i)) = []

variable [DecidableEq K]

structure WorkClean (slots : Layout u D ↪ K) (base : K → List Bool) : Prop where
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients u D, base (slots (.inr i)) = []

omit [DecidableEq K] in
theorem Clean.work {slots : Layout u D ↪ K} {base : K → List Bool} (clean : Clean slots base) :
    WorkClean slots base :=
  ⟨clean.accA, clean.accB, clean.counter, clean.scratch, clean.coefficients⟩

theorem WorkClean.update_output {slots : Layout u D ↪ K} {base : K → List Bool}
    (clean : WorkClean slots base) (kind : Kind) (value : List Bool) :
    WorkClean slots (Function.update base (control slots (outputControl kind)) value) := by
  cases kind <;> constructor
  all_goals try { simpa [outputControl] using clean.accA }
  all_goals try { simpa [outputControl] using clean.accB }
  all_goals try { simpa [outputControl] using clean.counter }
  all_goals try { simpa [outputControl] using clean.scratch }
  all_goals intro i; simpa [control, slots.injective.eq_iff] using clean.coefficients i

theorem result_frame (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) (k : K)
    (hl : k ≠ control slots .leftBlockSize) (ho : k ≠ control slots .occurrenceCount)
    (hd : k ≠ control slots .dummyIndex) (hb : k ≠ control slots .bitCount) :
    resultTapes slots base n m k = base k := by
  simp [resultTapes, hl, ho, hd, hb]

@[simp] theorem result_variableCount (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .variableCount) = base (control slots .variableCount) := by
  simp [resultTapes]
@[simp] theorem result_clauseCount (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .clauseCount) = base (control slots .clauseCount) := by
  simp [resultTapes]

end

end DFVSGames.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_TupleOrder
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace DFVSGames.Foundations.Hastad.SourceLoopOrder

open Complexity Complexity.MachineTupleOdometer
open Target SourceContexts SourceOccurrences
open DFVSGames.Reduction

theorem inputBits_eq_header_records (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.«variables», input.equations.length] ++
        input.equations.flatMap (fun e => encodeWords (SourceEncoding.equationWords e)) := by
  unfold SourceEncoding.inputBits SourceEncoding.inputWords
  rw [encodeWords_append]
  congr 1
  induction input.equations with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, encodeWords_append, ih]

end DFVSGames.Foundations.Hastad.SourceLoopOrder

end


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Decoder
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Foundations.Hastad

open scoped BigOperators
open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem walsh_support (s x : Cube I) :
    walsh s x = ∏ i ∈ support s, bitSign (x i) := by
  unfold walsh support
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [bitSign]

theorem walsh_pullback (π : J → I) (s : Cube J) (f : Cube I) :
    walsh s (fun y => f (π y)) = walsh (parityProjection π s) f := by
  rw [walsh_support]
  rw [← Finset.prod_fiberwise' (support s) π (fun i => bitSign (f i))]
  unfold walsh parityProjection
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.prod_const]
  exact sign_power_parity (f i) _

theorem projectedCoefficient_eq (π : J → I) (A : Cube I → ℝ) (s : Cube J) :
    projectedCoefficient π A s = coefficient A (parityProjection π s) := by
  simp only [projectedCoefficient, coefficient, walsh_pullback]

def decoderSuccess (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)

def decodingEnergy (π : J → I) (A : Cube I → ℝ) (B : Cube J → ℝ) : ℝ :=
  ∑ b, projectedCoefficient π A b ^ 2 * coefficient B b ^ 2 / (support b).card

theorem decodingEnergy_le_success (π : J → I) (A : Cube I → Bool) (B : Cube J → Bool)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    decodingEnergy π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ≤
      decoderSuccess π A B := by
  unfold decodingEnergy decoderSuccess
  apply Finset.sum_le_sum
  intro b _
  rw [projectedCoefficient_eq]
  have hsum :
      coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        agreementProbability π (parityProjection π b) b ≤
      ∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b := by
    apply Finset.single_le_sum (s := Finset.univ)
      (f := fun a => coefficient (fun f => bitSign (A f)) a ^ 2 * agreementProbability π a b)
    · intro a _
      exact mul_nonneg (sq_nonneg _) (agreementProbability_nonneg π a b)
    · exact Finset.mem_univ _
  have hm := mul_le_mul_of_nonneg_left hsum
    (sq_nonneg (coefficient (fun g => bitSign (B g)) b))
  by_cases ha : (support (parityProjection π b)).Nonempty
  · have hagree := agreementProbability_projection π b ha
    have ht := mul_le_mul_of_nonneg_left hagree
      (mul_nonneg (sq_nonneg (coefficient (fun f => bitSign (A f))
        (parityProjection π b))) (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    have heq : coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2 / (support b).card =
      (coefficient (fun f => bitSign (A f)) (parityProjection π b) ^ 2 *
        coefficient (fun g => bitSign (B g)) b ^ 2) * (1 / (support b).card) := by ring
    rw [heq]
    exact ht.trans (by convert hm using 1 ; ring)
  · have hempty : support (parityProjection π b) = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hz := (support_eq_empty_iff _).mp hempty
    simpa [hz, hzero] using hm

theorem bias_sq_le_weighted_energy (ε : ℝ) (π : J → I)
    (A : Cube I → ℝ) (B : Cube J → Bool) :
    testBias ε π A (fun g => bitSign (B g)) ^ 2 ≤
      ∑ b, (projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
        (1 - 2 * ε) ^ (support b).card) ^ 2 := by
  rw [testBias_fourier]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun b => projectedCoefficient π A b * coefficient (fun g => bitSign (B g)) b *
      (1 - 2 * ε) ^ (support b).card)
    (fun b => coefficient (fun g => bitSign (B g)) b)
  rw [sign_parseval, mul_one] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem decoder_four_epsilon_bias_sq (ε : ℝ) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2)
    (hzero : coefficient (fun f => bitSign (A f)) zeroMask = 0) :
    4 * ε * testBias ε π (fun f => bitSign (A f)) (fun g => bitSign (B g)) ^ 2 ≤
      decoderSuccess π A B := by
  apply le_trans _ (decodingEnergy_le_success π A B hzero)
  have hcs := mul_le_mul_of_nonneg_left
    (bias_sq_le_weighted_energy ε π (fun f => bitSign (A f)) B)
    (by linarith : 0 ≤ 4 * ε)
  apply hcs.trans
  rw [Finset.mul_sum]
  unfold decodingEnergy
  apply Finset.sum_le_sum
  intro b _
  by_cases hk : 0 < (support b).card
  · have hd := noise_decay_bound hε hε' hk
    have hm := mul_le_mul_of_nonneg_left hd
      (mul_nonneg (sq_nonneg (projectedCoefficient π (fun f => bitSign (A f)) b))
        (sq_nonneg (coefficient (fun g => bitSign (B g)) b)))
    first | (convert hm using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hm.trans (le_of_eq (by ring)))
  · have hb : support b = ∅ := Finset.card_eq_zero.mp (by omega)
    have hbzero := (support_eq_empty_iff b).mp hb
    subst b
    simp [projectedCoefficient_eq, parityProjection_zero, hzero, support, zeroMask]

theorem folded_decoder_bound (ε : ℝ) (π : J → I)
    (i₀ : I) (table : HalfCube i₀ → Bool) (B : Cube J → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ table f))
      (fun g => bitSign (B g)) ^ 2 ≤ decoderSuccess π (foldedAnswer i₀ table) B := by
  exact decoder_four_epsilon_bias_sq ε π (foldedAnswer i₀ table) B hε hε'
    (foldedAnswer_zero_coefficient i₀ table)

def validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  ∑ b, coefficient (fun g => bitSign (B g)) b ^ 2 *
    (∑ a, coefficient (fun f => bitSign (A f)) a ^ 2 *
      validAgreementProbability valid π a b)

theorem conditioned_validDecoderSuccess (valid : J → Bool) (π : J → I)
    (A : Cube I → Bool) (j₀ : {j : J // valid j = true})
    (table : HalfCube j₀ → Bool) :
    validDecoderSuccess valid π A (conditionedFoldedAnswer valid j₀ table) =
      decoderSuccess π A (conditionedFoldedAnswer valid j₀ table) := by
  unfold validDecoderSuccess decoderSuccess
  apply Finset.sum_congr rfl
  intro b _
  by_cases hc : coefficient (fun g => bitSign (conditionedFoldedAnswer valid j₀ table g)) b = 0
  · simp [hc]
  · have hb : ∀ y ∈ support b, valid y = true := by
      apply conditioned_coefficient_support valid (fun g => bitSign (foldedAnswer j₀ table g)) b
      exact hc
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [validAgreementProbability_eq valid π a b hb]

theorem conditioned_folded_decoder_bound (ε : ℝ) (π : J → I) (valid : J → Bool)
    (i₀ : I) (tableA : HalfCube i₀ → Bool)
    (j₀ : {j : J // valid j = true}) (tableB : HalfCube j₀ → Bool)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    4 * ε * testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun g => bitSign (conditionedFoldedAnswer valid j₀ tableB g)) ^ 2 ≤
      validDecoderSuccess valid π (foldedAnswer i₀ tableA)
        (conditionedFoldedAnswer valid j₀ tableB) := by
  rw [conditioned_validDecoderSuccess]
  exact folded_decoder_bound ε π i₀ tableA
    (conditionedFoldedAnswer valid j₀ tableB) hε hε'

end DFVSGames.Foundations.Hastad
end

noncomputable section

namespace DFVSGames.Foundations.Hastad

open scoped BigOperators
open Finset
open DFVSGames.Foundations.Games

variable {I J : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

theorem supportResponse_expectation (fallback : I) (s : Cube I) (H : I → ℝ)
    (hs : (support s).Nonempty) :
    (supportResponse fallback s).expectation H =
      (∑ i ∈ support s, H i) / ((support s).card : ℝ) := by
  simp only [FiniteDistribution.expectation, supportResponse, hs, ite_true, if_true]
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem]
  simp only [div_eq_mul_inv, one_mul, Finset.univ_inter]
  rw [← Finset.mul_sum]
  ring

def fourierResponse (fallback : I) (F : Cube I → Bool) : FiniteDistribution I where
  weight i := ∑ s, coefficient (fun f => bitSign (F f)) s ^ 2 *
    (supportResponse fallback s).weight i
  nonnegative i := Finset.sum_nonneg fun s _ =>
    mul_nonneg (sq_nonneg _) ((supportResponse fallback s).nonnegative i)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
    exact sign_parseval F

theorem fourierResponse_expectation (fallback : I) (F : Cube I → Bool)
    (H : I → ℝ) :
    (fourierResponse fallback F).expectation H =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 2 *
        (supportResponse fallback s).expectation H := by
  unfold FiniteDistribution.expectation fourierResponse
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem response_expectation_nonnegative {K : Type*} [Fintype K]
    (law : FiniteDistribution K) (H : K → ℝ) (hH : ∀ k, 0 ≤ H k) :
    0 ≤ law.expectation H :=
  Finset.sum_nonneg fun k _ => mul_nonneg (law.nonnegative k) (hH k)

def validResponseAgreement (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J)
    (A : Cube I → Bool) (B : Cube J → Bool) : ℝ :=
  (fourierResponse fallbackI A).expectation fun i =>
    (fourierResponse fallbackJ B).expectation fun j =>
      if π j = i ∧ valid j = true then 1 else 0

theorem supportResponse_validAgreement (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (a : Cube I) (b : Cube J)
    (ha : (support a).Nonempty) (hb : (support b).Nonempty) :
    (supportResponse fallbackI a).expectation (fun i =>
      (supportResponse fallbackJ b).expectation (fun j =>
        if π j = i ∧ valid j = true then 1 else 0)) =
      validAgreementProbability valid π a b := by
  rw [supportResponse_expectation fallbackI a _ ha]
  simp_rw [supportResponse_expectation fallbackJ b _ hb, Finset.sum_boole]
  unfold validAgreementProbability
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem validAgreement_le_supportResponses (valid : J → Bool) (π : J → I)
    (fallbackI : I) (fallbackJ : J) (a : Cube I) (b : Cube J) :
    validAgreementProbability valid π a b ≤
      (supportResponse fallbackI a).expectation (fun i =>
        (supportResponse fallbackJ b).expectation (fun j =>
          if π j = i ∧ valid j = true then 1 else 0)) := by
  by_cases ha : (support a).Nonempty
  · by_cases hb : (support b).Nonempty
    · exact le_of_eq (supportResponse_validAgreement valid π fallbackI fallbackJ a b ha hb).symm
    · have he : support b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      simp only [validAgreementProbability, he, Finset.card_empty, Nat.cast_zero,
        mul_zero, div_zero]
      apply response_expectation_nonnegative
      intro i
      apply response_expectation_nonnegative
      intro j
      split_ifs <;> norm_num
  · have he : support a = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    simp only [validAgreementProbability, he, Finset.sum_empty, Finset.card_empty,
      Nat.cast_zero, zero_mul, div_zero]
    apply response_expectation_nonnegative
    intro i
    apply response_expectation_nonnegative
    intro j
    split_ifs <;> norm_num

end DFVSGames.Foundations.Hastad
end

noncomputable section
namespace DFVSGames.Foundations.Hastad

open scoped BigOperators
open Finset
open DFVSGames.Foundations.Games

theorem distribution_sq_expectation_le {Ω : Type*} [Fintype Ω]
    (law : FiniteDistribution Ω) (F : Ω → ℝ) :
    law.expectation F ^ 2 ≤ law.expectation (fun x => F x ^ 2) := by
  let m := law.expectation F
  have h := response_expectation_nonnegative law (fun x => (F x - m) ^ 2)
    (fun x => sq_nonneg _)
  have he : law.expectation (fun x => (F x - m) ^ 2) =
      law.expectation (fun x => F x ^ 2) - m ^ 2 := by
    unfold FiniteDistribution.expectation
    calc
      _ = ∑ x, ((law.weight x * F x ^ 2 - 2 * m * (law.weight x * F x)) +
          law.weight x * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, law.normalized]
        change (law.expectation (fun x => F x ^ 2) - 2 * m * m) + 1 * m ^ 2 = _
        simp only [FiniteDistribution.expectation]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

variable {Q₁ Q₂ I J : Type*}
  [Fintype Q₁] [DecidableEq Q₁] [Fintype Q₂] [DecidableEq Q₂]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J]

def questionBias (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) (q : Q₁ × Q₂) : ℝ :=
  testBias ε (π q.1 q.2) (fun f => bitSign (A q.1 f)) (fun g => bitSign (B q.2 g))

omit [DecidableEq Q₁] [DecidableEq Q₂] [Nonempty I] [Nonempty J] in
theorem questionAcceptance_eq (questions : FiniteDistribution (Q₁ × Q₂))
    (ε : ℝ) (π : Q₁ → Q₂ → J → I)
    (A : Q₁ → Cube I → Bool) (B : Q₂ → Cube J → Bool) :
    questions.expectation (questionAcceptance ε π A B) =
      (1 + questions.expectation (questionBias ε π A B)) / 2 := by
  unfold questionAcceptance
  simp_rw [testAcceptance_eq]
  unfold questionBias FiniteDistribution.expectation
  simp only [div_eq_mul_inv, mul_add, mul_one, ← mul_assoc,
    Finset.sum_add_distrib, ← Finset.sum_mul, questions.normalized]

def ConditionedOracle.fallback {valid : J → Bool} (default : J) :
    ConditionedOracle valid → J
  | .empty _ => default
  | .stored j₀ _ => j₀.val

omit [Nonempty I] [Nonempty J] in
theorem empty_conditioned_bias (ε : ℝ) (π : J → I)
    (i₀ : I) (tableA : HalfCube i₀ → Bool) :
    testBias ε π (fun f => bitSign (foldedAnswer i₀ tableA f))
      (fun _ => bitSign false) = 0 := by
  simp only [bitSign, Bool.false_eq_true, ite_false]
  rw [testBias_constant_right]
  have hz := foldedAnswer_zero_coefficient i₀ tableA
  simpa [coefficient, walsh, bitSign] using hz

end DFVSGames.Foundations.Hastad
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SharedSampling
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
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

theorem sharedOutputLaw_weight {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) (x : X) (y : Y) (a b : S) :
    (sharedOutputLaw μ seedLaw left right).weight ((x,y),a,b) =
      μ.weight (x,y) * seedLaw.expectation
        (fun seed => if left seed x = a ∧ right seed y = b then 1 else 0) := by
  classical
  simp only [sharedOutputLaw, FiniteDistribution.pushforward,
    FiniteDistribution.product, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [and_assoc, ite_and]
  simp [FiniteDistribution.expectation, Finset.mul_sum, mul_ite]


open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerOutputLaw (thresholds : List ℝ) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) : FiniteDistribution ((X × Y) × S × S) :=
  sharedOutputLaw μ (traceSeedLaw (rectangleDistribution thresholds) n)
    (samplerLocal thresholds L fallback n) (samplerLocal thresholds R fallback n)


end
end DFVSGames.Foundations.Repetition


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Game
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace DFVSGames.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem eventLaw_probability (F : Formula) (hne : F.clauses ≠ [])
    (P : RandomEvent F → Bool) :
    (eventLaw F hne).probability P =
      (∑ e : RandomEvent F, if P e then (1 : ℝ) else 0) /
        (3 * F.clauses.length : ℕ) := by
  classical
  simp only [eventLaw, FiniteDistribution.uniform, FiniteDistribution.probability]
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  cases P e <;> simp [RandomEvent, Fintype.card_prod, card_slot, Nat.mul_comm]

theorem sum_slots (H : Slot → ℝ) :
    (∑ s : Slot, H s) = H .first + H .second + H .third := by
  have hu : (Finset.univ : Finset Slot) = {.first, .second, .third} := by
    ext s
    cases s <;> simp
  rw [hu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton]
  ring

theorem sum_slot_accepts (F : Formula) (alice : AliceStrategy F)
    (bob : BobStrategy F) (c : Fin F.clauses.length) :
    (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) =
      (acceptedSlots (clauseAt F c) (alice c)
        (honestAnswer (clauseAt F c) bob) : ℕ) := by
  rw [sum_slots]
  by_cases hs : localSatisfies (clauseAt F c) (alice c) = true
  · by_cases h₁ : (alice c).first = bob (clauseAt F c)[0].variableIndex <;>
      by_cases h₂ : (alice c).second = bob (clauseAt F c)[1].variableIndex <;>
      by_cases h₃ : (alice c).third = bob (clauseAt F c)[2].variableIndex <;>
      norm_num [accepts, hs, acceptedSlots, matchingSlots, honestAnswer, answerAt, nameAt,
        h₁, h₂, h₃]
  · simp [accepts, acceptedSlots, hs]

theorem failureCount_eq_sum_map (F : Formula) (bob : BobStrategy F)
    (cs : List (Fin F.clauses.length)) :
    failureCount F bob cs =
      (cs.map (fun c => clauseFailure (clauseAt F c) bob)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [failureCount, List.map_cons, List.sum_cons, ih]

theorem failureCount_allIndices (F : Formula) (bob : BobStrategy F) :
    failureCount F bob (allIndices F) =
      ∑ c : Fin F.clauses.length, clauseFailure (clauseAt F c) bob := by
  rw [failureCount_eq_sum_map]
  unfold allIndices
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

theorem verifier_probability_plus_failure (F : Formula) (hne : F.clauses ≠ [])
    (alice : AliceStrategy F) (bob : BobStrategy F) :
    (eventLaw F hne).probability (accepts F alice bob) +
      (failureCount F bob (allIndices F) : ℝ) / (3 * F.clauses.length : ℕ) ≤ 1 := by
  have hm : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
  have hlocal (c : Fin F.clauses.length) :
      (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) +
        (clauseFailure (clauseAt F c) bob : ℝ) ≤ 3 := by
    rw [sum_slot_accepts]
    exact_mod_cast local_rejection_bound (clauseAt F c) (alice c) bob
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset _)) => hlocal c)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [eventLaw_probability, failureCount_allIndices]
  push_cast
  push_cast at hm
  rw [Fintype.sum_prod_type, ← add_div]
  apply (div_le_one hm).mpr
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hsum

theorem base_success_le_verifier (F : Formula) (hne : F.clauses ≠ [])
    (strategy : Strategy (Fin F.«variables») (Fin F.clauses.length) Bool ClauseAnswer) :
    (baseGame F hne).success strategy ≤
      (eventLaw F hne).probability (accepts F strategy.2 strategy.1) := by
  unfold Game.success baseGame
  rw [FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro e he
  exact baseAccepts_implies_sampled F e.1 e.2 _ _ he

theorem base_value_le_of_clause_gap (F : Formula) (hne : F.clauses ≠ [])
    (δ : ℝ) (hgap : ∀ bob : BobStrategy F,
      δ * F.clauses.length ≤ (failureCount F bob (allIndices F) : ℝ)) :
    (baseGame F hne).value ≤ 1 - δ / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have hbase := base_success_le_verifier F hne strategy
  have hprob := verifier_probability_plus_failure F hne strategy.2 strategy.1
  have hm : (0 : ℝ) < F.clauses.length :=
    Nat.cast_pos.mpr (List.length_pos_iff.mpr hne)
  have hg : δ / 3 ≤ (failureCount F strategy.1 (allIndices F) : ℝ) /
      (3 * F.clauses.length : ℕ) := by
    have hden : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
      exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
    apply (le_div_iff₀ hden).mpr
    calc
      δ / 3 * (3 * F.clauses.length : ℕ) = δ * F.clauses.length := by push_cast; ring
      _ ≤ _ := hgap strategy.1
  linarith

theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (μ : FiniteDistribution X) (f : X → Y) (g : Y → Z) :
    (μ.pushforward f).pushforward g = μ.pushforward (g ∘ f) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.pushforward]
  calc
    _ = ∑ y : Y, ∑ x : X, if f x = y then
        (if g y = z then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : g y = z <;> simp [h]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem expectation_pushforward {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (f : X → Y) (H : Y → ℝ) :
    (μ.pushforward f).expectation H = μ.expectation (H ∘ f) := by
  classical
  simp only [FiniteDistribution.expectation, FiniteDistribution.pushforward,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

def repeatedVisible (F : Formula) (u : ℕ) (events : Fin u → RandomEvent F) :
    VariableContext F u × ClauseContext F u :=
  (fun t => nameAt (clauseAt F (events t).1) (events t).2,
   fun t => (events t).1)

theorem repeated_questions (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    ((baseGame F hne).repetition u).questions =
      ((eventLaw F hne).iid u).pushforward (repeatedVisible F u) := by
  change (((eventLaw F hne).pushforward (visibleQuestion F)).iid u).transport
    (Game.tupleQuestionEquiv u) = _
  rw [FiniteDistribution.iid_pushforward, ← FiniteDistribution.pushforward_equiv,
    pushforward_comp]
  rfl

def sourceProjectionGame (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    Game (VariableContext F u) (ClauseContext F u) (I u) (J u) :=
  projectionGame ((baseGame F hne).repetition u).questions
    (fun v c => pi F c v) (validJ F)

theorem projection_value_le_repetition (F : Formula) (hne : F.clauses ≠ [])
    (u : ℕ) :
    (sourceProjectionGame F hne u).value ≤ ((baseGame F hne).repetition u).value := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have h : (sourceProjectionGame F hne u).success strategy ≤
      ((baseGame F hne).repetition u).success strategy := by
    apply FiniteDistribution.probability_mono
    intro q hq
    have hlegal : pi F q.2 q.1 (strategy.2 q.2) = strategy.1 q.1 ∧
        validJ F q.2 (strategy.2 q.2) = true := by
      simpa only [Game.wins, sourceProjectionGame, projectionGame,
        decide_eq_true_eq] using hq
    apply (Game.repetition_accepts_iff _ _ _ _ _ _).mpr
    intro t
    exact projection_implies_coordinate_accepts F q.2 q.1
      (strategy.1 q.1) (strategy.2 q.2) hlegal.2 hlegal.1 t
  exact h.trans (Game.success_le_value _ strategy)

end DFVSGames.Foundations.Hastad.SourceGame

end


namespace DFVSGames.Foundations.Repetition

@[simp] theorem logTwo_one : logTwo 1 = 0 := by simp [logTwo]

theorem logTwo_inv_le_of_half_pow_le {p : ℝ} (m : ℕ)
    (h : (1 / 2 : ℝ) ^ m ≤ p) : logTwo (1 / p) ≤ m := by
  have hp : 0 < p := (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m).trans_le h
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m) h
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [Real.log_pow, hhalf] at hlog
  unfold logTwo
  rw [one_div, Real.log_inv]
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  nlinarith

theorem contraction_step {v ell : ℝ} {n m : ℕ} {p next : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hm : 1 ≤ m) (hmn : m < n) (hp : 0 ≤ p)
    (hmono : next ≤ p)
    (hprev : p ≤ ((1 + v) / 2) ^ m)
    (hcut : 2700 * (m : ℝ) * ell ≤ (1 - v) ^ 2 * ((n : ℝ) - m))
    (hstep : next ≤ p * (v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)))) :
    next ≤ ((1 + v) / 2) ^ (m + 1) := by
  by_cases hsmall : p ≤ ((1 + v) / 2) ^ (m + 1)
  · exact hmono.trans hsmall
  have hq : (1 / 2 : ℝ) ≤ (1 + v) / 2 := by linarith
  have hhalf : (1 / 2 : ℝ) ^ (m + 1) ≤ p :=
    (pow_le_pow_left₀ (by norm_num) hq (m + 1)).trans (le_of_not_ge hsmall)
  have hlog := logTwo_inv_le_of_half_pow_le (m + 1) hhalf
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (n : ℝ) - m := by
    have hmnreal : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hmell : (m : ℝ) ≤ (m : ℝ) * ell := by nlinarith
  have hbudget : (m : ℝ) * ell + logTwo (1 / p) ≤ 3 * (m : ℝ) * ell := by
    simp only [Nat.cast_add, Nat.cast_one] at hlog
    nlinarith
  have hsqrt : Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 - v) / 30 := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ (1 - v) / 30)).2
    apply (div_le_iff₀ hden).2
    nlinarith
  have hfactor : v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 + v) / 2 := by
    linarith
  calc
    next ≤ p * (v + 15 * Real.sqrt
        (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m))) := hstep
    _ ≤ p * ((1 + v) / 2) := mul_le_mul_of_nonneg_left hfactor hp
    _ ≤ ((1 + v) / 2) ^ m * ((1 + v) / 2) :=
      mul_le_mul_of_nonneg_right hprev (by linarith)
    _ = ((1 + v) / 2) ^ (m + 1) := (pow_succ _ _).symm

def ScalarRecurrence (p : ℕ → ℝ) (n : ℕ) (v ell : ℝ) : Prop :=
  ∀ m, m < n → p (m + 1) ≤ p m * (v + 15 * Real.sqrt
    (((m : ℝ) * ell + logTwo (1 / p m)) / ((n : ℝ) - m)))

theorem decay_to_cutoff (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ ((1 + v) / 2) ^
      ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) := by
  let T : ℝ := (n : ℝ) * (1 - v) ^ 2 / (2925 * ell)
  let M : ℕ := Nat.ceil T
  have hMn : M ≤ n := Nat.ceil_le.mpr (cutoff_le_length n hv0 hv1 hell)
  have hind : ∀ m, m ≤ M → p m ≤ ((1 + v) / 2) ^ m := by
    intro m
    induction m with
    | zero => intro _; simp [hp0]
    | succ m ih =>
        intro hmM
        have hmM' : m < M := Nat.lt_of_succ_le hmM
        have hmn : m < n := hmM'.trans_le hMn
        have hprev := ih (Nat.le_of_lt hmM')
        by_cases hm0 : m = 0
        · subst m
          have hinit : p 1 ≤ v := by
            have hs := hrec 0 hmn
            simpa [hp0] using hs
          simpa using hinit.trans (by linarith : v ≤ (1 + v) / 2)
        · have hmT : (m : ℝ) < T := Nat.lt_ceil.mp hmM'
          exact contraction_step hv0 hv1 hell (Nat.one_le_iff_ne_zero.mpr hm0)
            hmn (hpnonneg m) (hpmono (Nat.le_succ m)) hprev
            (cutoff_step hv0 hv1 hell hmT) (hrec m hmn)
  have hq0 : 0 < (1 + v) / 2 := by linarith
  have hq1 : (1 + v) / 2 ≤ 1 := by linarith
  calc
    p n ≤ p M := hpmono hMn
    _ ≤ ((1 + v) / 2) ^ M := hind M le_rfl
    _ = ((1 + v) / 2) ^ (M : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ((1 + v) / 2) ^ T :=
      Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (Nat.le_ceil T)

theorem scalar_bound_6000 (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) := by
  have hell0 : 0 < ell := by linarith
  have hq0 : 0 ≤ (1 + v) / 2 := by linarith
  have hexp : 0 ≤ (n : ℝ) / ell := by positivity
  have hblock := block_contraction hv0 hv1
  have hweak : 1 - (1 - v) ^ 3 / 5850 ≤ 1 - (1 - v) ^ 3 / 6000 := by
    have : 0 ≤ (1 - v) ^ 3 := by positivity
    nlinarith
  calc
    p n ≤ ((1 + v) / 2) ^
        ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) :=
      decay_to_cutoff p n hv0 hv1 hell hp0 hpnonneg hpmono hrec
    _ = (((1 + v) / 2) ^ ((1 - v) ^ 2 / 2925 : ℝ)) ^ ((n : ℝ) / ell) := by
      rw [← Real.rpow_mul hq0]
      congr 1
      ring
    _ ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hq0 _) (hblock.trans hweak) hexp

end DFVSGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ProfileCorrection
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem revealLaw_weight (μ : FiniteDistribution (X × Y)) (q : X × Y) (r : X ⊕ Y) :
    (revealLaw μ).weight (q,r) =
      (if r = Sum.inl q.1 then μ.weight q / 2 else 0) +
      (if r = Sum.inr q.2 then μ.weight q / 2 else 0) := by
  classical
  rcases q with ⟨x,y⟩
  simp only [revealLaw, FiniteDistribution.pushforward, FiniteDistribution.product,
    Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
  simp [revealEndpoint, FiniteDistribution.uniform, div_eq_mul_inv, add_comm, eq_comm]

def revealFallback (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  match r with
  | Sum.inl x => μ.pushforward (fun q => (x,q.2))
  | Sum.inr y => μ.pushforward (fun q => (q.1,y))

def revealProfile (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    FiniteDistribution (X × Y) :=
  gameConditionalKernel (revealFirstLaw μ) (revealFallback μ r) r

theorem revealProfile_inl_support (μ : FiniteDistribution (X × Y))
    (x : X) (q : X × Y) (h : q.1 ≠ x) :
    (revealProfile μ (Sum.inl x)).weight q = 0 := by
  classical
  rcases q with ⟨x',y⟩
  dsimp at h
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel]
  split
  · simp [revealFallback, FiniteDistribution.pushforward, Fintype.sum_prod_type,
      Prod.mk.injEq, Ne.symm h]
  · simp [revealLaw_weight, Ne.symm h]

theorem revealProfile_inr_support (μ : FiniteDistribution (X × Y))
    (y : Y) (q : X × Y) (h : q.2 ≠ y) :
    (revealProfile μ (Sum.inr y)).weight q = 0 := by
  classical
  rcases q with ⟨x,y'⟩
  dsimp at h
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel]
  split
  · simp [revealFallback, FiniteDistribution.pushforward, Fintype.sum_prod_type,
      Prod.mk.injEq, Ne.symm h]
  · simp [revealLaw_weight, Ne.symm h]

def revealInputLaw (μ : FiniteDistribution (X × Y)) : FiniteDistribution (X ⊕ Y) :=
  (revealLaw μ).pushforward Prod.snd

theorem revealInputLaw_weight (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) :
    (revealInputLaw μ).weight r = firstMarginal (revealFirstLaw μ).weight r := by
  classical
  cases r <;>
    simp [revealInputLaw, FiniteDistribution.pushforward, firstMarginal, Fintype.sum_prod_type]

theorem reveal_profile_recombination (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (q : X × Y) :
    (revealInputLaw μ).weight r * (revealProfile μ r).weight q =
      (revealLaw μ).weight (q,r) := by
  rw [revealInputLaw_weight]
  exact gameConditionalKernel_recombine (revealFirstLaw μ) (revealFallback μ r) r q

theorem revealInputLaw_inl (μ : FiniteDistribution (X × Y)) (x : X) :
    (revealInputLaw μ).weight (Sum.inl x) = (∑ y, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight,
    div_eq_mul_inv]
  rw [Finset.sum_comm]
  simp [← Finset.sum_mul]

theorem revealInputLaw_inr (μ : FiniteDistribution (X × Y)) (y : Y) :
    (revealInputLaw μ).weight (Sum.inr y) = (∑ x, μ.weight (x,y)) / 2 := by
  classical
  rw [revealInputLaw_weight]
  simp [firstMarginal, Fintype.sum_prod_type, revealLaw_weight,
    div_eq_mul_inv, ← Finset.sum_mul]

theorem revealProfile_inl_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inl x)).weight (x,y) =
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight x y := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inl x) =
      firstMarginal μ.weight x / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inl]
    rfl
  have hf : (revealFallback μ (Sum.inl x)).weight (x,y) =
      (μ.pushforward Prod.snd).weight y := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.2 = y <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal μ.weight x = 0
  · simpa [h] using hf
  · have hh : firstMarginal μ.weight x / 2 ≠ 0 := div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, if_true, Sum.inl_ne_inr, ite_false, add_zero]
    field_simp

theorem revealProfile_inr_diagonal (μ : FiniteDistribution (X × Y)) (x : X) (y : Y) :
    (revealProfile μ (Sum.inr y)).weight (x,y) =
      conditionalKernel (μ.transport (Equiv.prodComm X Y)).weight
        (μ.pushforward Prod.fst).weight y x := by
  classical
  have hm : firstMarginal (revealFirstLaw μ).weight (Sum.inr y) =
      firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 := by
    rw [← revealInputLaw_weight, revealInputLaw_inr]
    rfl
  have hf : (revealFallback μ (Sum.inr y)).weight (x,y) =
      (μ.pushforward Prod.fst).weight x := by
    simp [revealFallback, FiniteDistribution.pushforward, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q.1 = x <;> simp [hq]
  simp only [revealProfile, gameConditionalKernel, toGameLaw, conditionalKernel, hm]
  by_cases h : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y = 0
  · simpa [h] using hf
  · have hh : firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2 ≠ 0 :=
      div_ne_zero h (by norm_num)
    simp only [ite_eq_right h, ite_eq_right hh, revealFirstLaw_weight, revealLaw_weight,
      ite_true, if_true, Sum.inr_ne_inl, ite_false, zero_add]
    change (μ.weight (x,y) / 2) / (firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y / 2) =
      μ.weight (x,y) / firstMarginal (μ.transport (Equiv.prodComm X Y)).weight y
    field_simp

theorem revealLaw_sum_left (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ x, (revealLaw μ).weight (q, Sum.inl x)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem revealLaw_sum_right (μ : FiniteDistribution (X × Y)) (q : X × Y) :
    (∑ y, (revealLaw μ).weight (q, Sum.inr y)) = μ.weight q / 2 := by
  classical
  simp [revealLaw_weight]

theorem reveal_product_factorization {ι : Type*} [Fintype ι]
    (μ : FiniteDistribution (X × Y)) (r : ι → X ⊕ Y) (q : ι → X × Y) :
    (∏ i, (revealInputLaw μ).weight (r i)) *
      (∏ i, (revealProfile μ (r i)).weight (q i)) =
        ∏ i, (revealLaw μ).weight (q i,r i) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact reveal_profile_recombination μ (r i) (q i)

theorem reveal_product_forget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (q : ι → X × Y) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        (∏ i, (revealProfile μ (r i)).weight (q i))) =
      ∏ i, μ.weight (q i) := by
  classical
  simp_rw [reveal_product_factorization]
  calc
    _ = ∏ i, ∑ r : X ⊕ Y, (revealLaw μ).weight (q i,r) :=
      (Fintype.prod_sum (fun (i : ι) (r : X ⊕ Y) => (revealLaw μ).weight (q i,r))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_sum_type, revealLaw_sum_left, revealLaw_sum_right]
      ring

theorem reveal_product_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FiniteDistribution (X × Y)) (f : (ι → X × Y) → ℝ) :
    (∑ r : ι → X ⊕ Y,
      (∏ i, (revealInputLaw μ).weight (r i)) *
        ∑ q : ι → X × Y, (∏ i, (revealProfile μ (r i)).weight (q i)) * f q) =
      ∑ q : ι → X × Y, (∏ i, μ.weight (q i)) * f q := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  rw [reveal_product_forget]

end
end DFVSGames.Foundations.Repetition

namespace DFVSGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem sqrt_distance_le_relativeEntropy_term {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : x ≠ 0 → y ≠ 0) :
    (Real.sqrt x - Real.sqrt y)^2 ≤ x * Real.log (x / y) - x + y := by
  by_cases hxzero : x = 0
  · subst x
    simp [Real.sq_sqrt hy]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm (hs hxzero))
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsy hsx)
  have hlogid : Real.log (Real.sqrt y / Real.sqrt x) =
      -(Real.log (x / y)) / 2 := by
    rw [Real.log_div hsy.ne' hsx.ne', Real.log_sqrt hy, Real.log_sqrt hx,
      Real.log_div hxzero (hs hxzero)]
    ring
  have hprod : x * (Real.sqrt y / Real.sqrt x) = Real.sqrt x * Real.sqrt y := by
    calc
      x * (Real.sqrt y / Real.sqrt x) = (Real.sqrt x)^2 * (Real.sqrt y / Real.sqrt x) := by
        rw [Real.sq_sqrt hx]
      _ = Real.sqrt x * Real.sqrt y := by field_simp [hsx.ne']
  have hm := mul_le_mul_of_nonneg_left hlog hx
  rw [hlogid, mul_sub, mul_one, hprod] at hm
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem hellingerSquared_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    hellingerSquared p q ≤ relativeEntropy p q := by
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) =>
    sqrt_distance_le_relativeEntropy_term (hp.1 a) (hq.1 a) (hs a))
  simpa only [hellingerSquared, relativeEntropy, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hp.2, hq.2, sub_add_cancel] using hsum

theorem totalVariation_sq_le_hellingerSquared (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) : totalVariation p q ^ 2 ≤ hellingerSquared p q := by
  have hfactor : ∀ a, |Real.sqrt (p a) - Real.sqrt (q a)| *
      (Real.sqrt (p a) + Real.sqrt (q a)) = |p a - q a| := by
    intro a
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => |Real.sqrt (p a) - Real.sqrt (q a)|)
    (fun a => Real.sqrt (p a) + Real.sqrt (q a))
  simp only [hfactor, sq_abs] at hcs
  have hpoint : ∀ a, (Real.sqrt (p a) + Real.sqrt (q a)) ^ 2 ≤ 2 * (p a + q a) := by
    intro a
    nlinarith [sq_nonneg (Real.sqrt (p a) - Real.sqrt (q a)),
      Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hp.2, hq.2] at hsum
  have hnonneg : 0 ≤ ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsum hnonneg
  dsimp [totalVariation, hellingerSquared]
  nlinarith

theorem totalVariation_sq_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    totalVariation p q ^ 2 ≤ relativeEntropy p q :=
  (totalVariation_sq_le_hellingerSquared p q hp hq).trans
    (hellingerSquared_le_relativeEntropy p q hp hq hs)

end DFVSGames.Foundations.Information

namespace DFVSGames.Foundations.Information

open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

theorem coordinateMarginal_isProbability (p : (ι → α) → ℝ) (hp : IsProbability p) (i : ι) :
    IsProbability (coordinateMarginal p i) := by
  classical
  constructor
  · intro a
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hp.1 x
    · exact le_rfl
  · simp only [coordinateMarginal]
    rw [Finset.sum_comm]
    simpa using hp.2

theorem point_le_coordinateMarginal (p : (ι → α) → ℝ) (hp : IsProbability p)
    (i : ι) (x : ι → α) : p x ≤ coordinateMarginal p i (x i) := by
  classical
  have h := Finset.single_le_sum
    (f := fun y : ι → α => if y i = x i then p y else 0)
    (fun y _ => by split_ifs; exact hp.1 y; exact le_rfl) (Finset.mem_univ x)
  simpa [coordinateMarginal] using h

theorem marginal_expectation (p : (ι → α) → ℝ) (i : ι) (f : α → ℝ) :
    (∑ x, p x * f (x i)) = ∑ a, coordinateMarginal p i a * f a := by
  classical
  simp only [coordinateMarginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem joint_supportedBy_product_coordinateMarginals (p : (ι → α) → ℝ)
    (hp : IsProbability p) : SupportedBy p (independentProduct (coordinateMarginal p)) := by
  intro x hx
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
    (point_le_coordinateMarginal p hp i x))

theorem relativeEntropy_independent_reference (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (_hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    relativeEntropy p (independentProduct q) =
      relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
  classical
  have hpoint : ∀ x : ι → α, p x * Real.log (p x / independentProduct q x) =
      p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
        ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
    intro x
    by_cases hx : p x = 0
    · simp [hx]
    have hm : ∀ i, coordinateMarginal p i (x i) ≠ 0 := by
      intro i
      exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
        (point_le_coordinateMarginal p hp i x))
    have hqne : ∀ i, q i (x i) ≠ 0 := fun i => hs i (x i) (hm i)
    have hmp : (∏ i, coordinateMarginal p i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hm i)
    have hqp : (∏ i, q i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hqne i)
    simp only [independentProduct, Real.log_div hx hmp, Real.log_div hx hqp,
      Real.log_prod (fun i _ => hm i), Real.log_prod (fun i _ => hqne i)]
    simp_rw [Real.log_div (hm _) (hqne _)]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  calc
    relativeEntropy p (independentProduct q) =
        ∑ x, (p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
          ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i))) := by
      exact Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, ∑ x, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      rfl
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact marginal_expectation p i (fun a => Real.log (coordinateMarginal p i a / q i a))

theorem coordinate_relativeEntropy_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, relativeEntropy (coordinateMarginal p i) (q i)) ≤
      relativeEntropy p (independentProduct q) := by
  rw [relativeEntropy_independent_reference p q hp hq hs]
  exact le_add_of_nonneg_left (relativeEntropy_nonneg _ _ hp
    (independentProduct_isProbability _ (coordinateMarginal_isProbability p hp))
    (joint_supportedBy_product_coordinateMarginals p hp))

theorem coordinate_totalVariation_sq_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, totalVariation (coordinateMarginal p i) (q i) ^ 2) ≤
      relativeEntropy p (independentProduct q) := by
  exact (Finset.sum_le_sum (fun i _ => totalVariation_sq_le_relativeEntropy _ _
    (coordinateMarginal_isProbability p hp i) (hq i) (hs i))).trans
      (coordinate_relativeEntropy_sum_le p q hp hq hs)

theorem posterior_coordinate_supportedBy (q : ι → α → ℝ) (w : (ι → α) → ℝ)
    (z : ℝ) (i : ι) :
    SupportedBy (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) := by
  classical
  intro a ha hqa
  apply ha
  unfold coordinateMarginal
  apply Finset.sum_eq_zero
  intro x _
  by_cases hxa : x i = a
  · have hzprod : independentProduct q x = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa only [hxa] using hqa)
    simp [hxa, posterior, hzprod]
  · simp [hxa]

theorem posterior_coordinate_totalVariation_sq_sum_le_log
    (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) (w : (ι → α) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw_one : ∀ x, w x ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ x, independentProduct q x * w x = z) :
    (∑ i, totalVariation
      (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) ^ 2) ≤
        Real.log (1 / z) := by
  have hp := independentProduct_isProbability q hq
  exact (coordinate_totalVariation_sq_sum_le _ q
    (posterior_isProbability _ w hp hw hz hmass) hq
    (posterior_coordinate_supportedBy q w z)).trans
      (posterior_relativeEntropy_le _ w hp hw hw_one hz hmass)

end DFVSGames.Foundations.Information

namespace DFVSGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem relativeEntropy_normalize_right (p b : α → ℝ) (hp : IsProbability p)
    (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B) :
    relativeEntropy p (fun a => b a / B) = relativeEntropy p b + Real.log B := by
  have hpoint : ∀ a, p a * Real.log (p a / (b a / B)) =
      p a * Real.log (p a / b a) + p a * Real.log B := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    rw [Real.log_div hpa (div_ne_zero hbne hB.ne'), Real.log_div hbne hB.ne',
      Real.log_div hpa hbne]
    ring
  simp only [relativeEntropy, hpoint, Finset.sum_add_distrib, ← Finset.sum_mul, hp.2, one_mul]

theorem neg_relativeEntropy_le_log_mass (p b : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) (hs : SupportedBy p b) {B : ℝ} (hB : 0 < B)
    (hmass : ∑ a, b a = B) : -relativeEntropy p b ≤ Real.log B := by
  have hs' : SupportedBy p (fun a => b a / B) :=
    fun a ha => div_ne_zero (hs a ha) hB.ne'
  have hnonneg := relativeEntropy_nonneg p (fun a => b a / B) hp
    (normalize_isProbability b hb hB hmass) hs'
  rw [relativeEntropy_normalize_right p b hp hs hB] at hnonneg
  linarith

theorem posterior_weighted_log_inverse_le (p b c : α → ℝ) (hp : IsProbability p)
    (hb : ∀ a, 0 ≤ b a) {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hmass : ∑ a, b a = B) (hpost : ∀ a, p a = b a * c a / z) :
    (∑ a, p a * Real.log (1 / c a)) ≤ Real.log (B / z) := by
  have hs : SupportedBy p b := by
    intro a ha hba
    apply ha
    rw [hpost, hba, zero_mul, zero_div]
  have hpoint : ∀ a, p a * Real.log (1 / c a) =
      p a * Real.log (1 / z) - p a * Real.log (p a / b a) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa]
    have hbne := hs a hpa
    have hcne : c a ≠ 0 := by
      intro hca
      apply hpa
      rw [hpost, hca, mul_zero, zero_div]
    have hratio : p a / b a = c a / z := by
      rw [hpost]
      field_simp [hbne, hz.ne']
    rw [hratio, Real.log_div hcne hz.ne', Real.log_div one_ne_zero hcne,
      Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  have hid : (∑ a, p a * Real.log (1 / c a)) =
      Real.log (1 / z) - relativeEntropy p b := by
    simp only [hpoint, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul,
      relativeEntropy]
  have hkl := neg_relativeEntropy_le_log_mass p b hp hb hs hB hmass
  rw [hid, Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
  linarith

end DFVSGames.Foundations.Information

namespace DFVSGames.Foundations.Information
open scoped BigOperators

theorem mass_mul_posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ)
    (hp : IsProbability p) (he : ∀ a, 0 ≤ e a)
    {c : ℝ} (hmass : ∑ a, p a * e a = c) (x : A) :
    c * posteriorOrOriginal p e c x = p x * e x := by
  classical
  by_cases hc : 0 < c
  · simp only [posteriorOrOriginal, ite_eq_left hc, posterior]
    field_simp [hc.ne']
  · have hcnonneg : 0 ≤ c := by
      rw [← hmass]
      exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp.1 a) (he a))
    have hc0 : c = 0 := le_antisymm (le_of_not_gt hc) hcnonneg
    have hpoint := Finset.single_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset A)) => mul_nonneg (hp.1 a) (he a))
      (Finset.mem_univ x)
    rw [hmass, hc0] at hpoint
    have hzero : p x * e x = 0 := le_antisymm hpoint (mul_nonneg (hp.1 x) (he x))
    simp [posteriorOrOriginal, hc0, hzero]

theorem weighted_coordinate_posterior_recombine
    {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (p e : (I → A) → ℝ) (hp : IsProbability p) (he : ∀ x, 0 ≤ e x)
    {c : ℝ} (hmass : ∑ x, p x * e x = c) (b z : ℝ) (i : I) (a : A) :
    (b * c / z) * coordinateMarginal (posteriorOrOriginal p e c) i a =
      (b / z) * ∑ x, if x i = a then p x * e x else 0 := by
  classical
  simp only [coordinateMarginal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxa : x i = a
  · simp only [ite_eq_left hxa]
    calc
      (b * c / z) * posteriorOrOriginal p e c x =
          (b / z) * (c * posteriorOrOriginal p e c x) := by ring
      _ = (b / z) * (p x * e x) := by
        rw [mass_mul_posteriorOrOriginal p e hp he hmass x]
  · simp [hxa]

variable {J I A : Type*}
variable [Fintype J] [Fintype I] [Fintype A] [DecidableEq I]

theorem side_information_bound
    (w b c : J → ℝ)
    (q : J → I → A → ℝ)
    (e : J → (I → A) → ℝ)
    (hw : IsProbability w)
    (hb : ∀ j, 0 ≤ b j)
    (hq : ∀ j i, IsProbability (q j i))
    (he : ∀ j x, 0 ≤ e j x)
    (he_one : ∀ j x, e j x ≤ 1)
    (hmass : ∀ j, ∑ x, independentProduct (q j) x * e j x = c j)
    {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hbase : ∑ j, b j = B)
    (hweight : ∀ j, w j = b j * c j / z) :
    (∑ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) (c ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) * Real.log (B / z)) := by
  classical
  let d : J → I → ℝ := fun j i => totalVariation
    (coordinateMarginal
      (posteriorOrOriginal (independentProduct (q j)) (e j) (c j)) i)
    (q j i)
  have hbudget : ∀ j,
      w j * (∑ i, d j i ^ 2) ≤ w j * Real.log (1 / c j) := by
    intro j
    by_cases hwzero : w j = 0
    · simp [hwzero]
    have hcne : c j ≠ 0 := by
      intro hczero
      apply hwzero
      rw [hweight j, hczero, mul_zero, zero_div]
    have hcnonneg : 0 ≤ c j := by
      rw [← hmass j]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg
        ((independentProduct_isProbability (q j) (hq j)).1 x) (he j x))
    have hcpos : 0 < c j := lt_of_le_of_ne hcnonneg (Ne.symm hcne)
    have hlocal := posterior_coordinate_totalVariation_sq_sum_le_log
      (q j) (hq j) (e j) (he j) (he_one j) hcpos (hmass j)
    have hweighted := mul_le_mul_of_nonneg_left hlocal (hw.1 j)
    simpa only [d, posteriorOrOriginal, ite_eq_left hcpos] using hweighted
  have hcs := weighted_coordinate_sum_sq_le
    w d (fun j => Real.log (1 / c j)) hw hbudget
  have hlog := posterior_weighted_log_inverse_le w b c hw hb hz hB hbase hweight
  have hsq : (∑ i, ∑ j, w j * d j i)^2 ≤
      (Fintype.card I : ℝ) * Real.log (B / z) :=
    hcs.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
  have htv : ∀ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) (c ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2) =
      ∑ j, w j * d j i := by
    intro i
    exact totalVariation_joint_common_weights w
      (fun j => coordinateMarginal
        (posteriorOrOriginal (independentProduct (q j)) (e j) (c j)) i)
      (fun j => q j i) hw.1
  simp_rw [htv]
  have hradicand : 0 ≤ (Fintype.card I : ℝ) * Real.log (B / z) :=
    (sq_nonneg _).trans hsq
  have hsqrt := Real.sq_sqrt hradicand
  have hsqrt_nonneg := Real.sqrt_nonneg ((Fintype.card I : ℝ) * Real.log (B / z))
  nlinarith

variable {T V : Type*} [Fintype T] [Fintype V] [Nonempty V]

theorem finite_side_information_bound
    (pT : T → ℝ) (q : T → I → A → ℝ)
    (e : T × V → (I → A) → ℝ) (c w : T × V → ℝ)
    (hpT : IsProbability pT)
    (hq : ∀ t i, IsProbability (q t i))
    (he : ∀ tv x, 0 ≤ e tv x)
    (he_sum : ∀ t x, (∑ v, e (t, v) x) ≤ 1)
    (hc : ∀ tv, ∑ x, independentProduct (q tv.1) x * e tv x = c tv)
    {z : ℝ} (hz : 0 < z)
    (hZ : ∑ tv, pT tv.1 * c tv = z)
    (hweight : ∀ tv, w tv = pT tv.1 * c tv / z) :
    (∑ i, totalVariation
      (fun tva : (T × V) × A => w tva.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q tva.1.1))
          (e tva.1) (c tva.1)) i tva.2)
      (fun tva : (T × V) × A => w tva.1 * q tva.1.1 i tva.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) *
        (Real.log (Fintype.card V : ℝ) + Real.log (1 / z))) := by
  classical
  have hcnonneg : ∀ tv, 0 ≤ c tv := by
    intro tv
    rw [← hc tv]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg
      ((independentProduct_isProbability (q tv.1) (hq tv.1)).1 x) (he tv x))
  have hw : IsProbability w := by
    constructor
    · intro tv
      rw [hweight tv]
      exact div_nonneg (mul_nonneg (hpT.1 tv.1) (hcnonneg tv)) hz.le
    · simp_rw [hweight, div_eq_mul_inv]
      rw [← Finset.sum_mul, hZ, mul_inv_cancel₀ hz.ne']
  have he_one : ∀ tv x, e tv x ≤ 1 := by
    intro tv x
    have hsingle : e tv x ≤ ∑ v, e (tv.1, v) x :=
      Finset.single_le_sum (fun v _ => he (tv.1, v) x) (Finset.mem_univ tv.2)
    exact hsingle.trans (he_sum tv.1 x)
  have hB : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hbase : (∑ tv : T × V, pT tv.1) = (Fintype.card V : ℝ) := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, hpT.2, mul_one]
  have h := side_information_bound w (fun tv : T × V => pT tv.1) c
    (fun tv => q tv.1) e hw (fun tv => hpT.1 tv.1) (fun tv => hq tv.1)
    he he_one hc hz hB hbase hweight
  have hlog : Real.log ((Fintype.card V : ℝ) / z) =
      Real.log (Fintype.card V : ℝ) + Real.log (1 / z) := by
    rw [Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  simpa only [hlog] using h

end DFVSGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SelectedInformation
attribute [-instance] _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem iid_coordinate_split {Ω : Type*} [Fintype Ω] {n : Nat}
    (μ : FiniteDistribution Ω) (selected : Finset (Fin n)) :
    (μ.iid n).transport (coordinateSplitEquiv selected) =
      (FiniteDistribution.table (fun _ : selected => μ)).product
        (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => μ)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, μ.weight (mergeCoordinates selected x.1 x.2 i)) =
    (∏ i : selected, μ.weight (x.1 i)) *
      ∏ i : {i : Fin n // i ∉ selected}, μ.weight (x.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ selected)
    (fun i => μ.weight (mergeCoordinates selected x.1 x.2 i))
  have hi : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : {i : Fin n // i ∈ selected},
        μ.weight (mergeCoordinates selected x.1 x.2 i.1)) *
        ∏ i : {i : Fin n // i ∉ selected},
          μ.weight (mergeCoordinates selected x.1 x.2 i.1) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

def selectedSplitLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution ((selected → Q₁ × Q₂) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => G.questions))

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (selectedSplitLaw G selected).probability
      (fun q => G.selectedWins strategy selected (selectedQuestionTuple selected q.1 q.2)) =
        G.selectedSuccess strategy selected := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability _
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

def selectedInputLaw (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n)) :
    FiniteDistribution (SelectedInput Q₁ Q₂ selected) :=
  (FiniteDistribution.table (fun _ : selected => G.questions)).product
    (FiniteDistribution.table (fun _ : {i : Fin n // i ∉ selected} => revealInputLaw G.questions))

def selectedInputProfile (G : Game Q₁ Q₂ A₁ A₂) (selected : Finset (Fin n))
    (t : SelectedInput Q₁ Q₂ selected) (i : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (Q₁ × Q₂) := revealProfile G.questions (t.2 i)

def selectedSideMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  ∑ u, independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
    selectedLikelihood G strategy selected tv.1.1 tv.2 u

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSideMass_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (t : SelectedInput Q₁ Q₂ selected) :
    (∑ v, selectedSideMass G strategy selected (t,v)) =
      ∑ u, independentProduct (fun i => (selectedInputProfile G selected t i).weight) u *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u)
        then 1 else 0) := by
  classical
  simp only [selectedSideMass]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, selectedLikelihood_sum]

theorem selectedSideMass_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ tv, (selectedInputLaw G selected).weight tv.1 *
      selectedSideMass G strategy selected tv) = G.selectedSuccess strategy selected := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, selectedSideMass_sum]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u)
        then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_probability G strategy selected
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

def selectedSideWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (tv : SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ :=
  (selectedInputLaw G selected).weight tv.1 * selectedSideMass G strategy selected tv /
    G.selectedSuccess strategy selected

theorem selected_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected}, totalVariation
      (fun tva : (SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) × (Q₁ × Q₂) =>
        selectedSideWeight G strategy selected tva.1 * coordinateMarginal
          (posteriorOrOriginal
            (independentProduct (fun j => (selectedInputProfile G selected tva.1.1 j).weight))
            (selectedLikelihood G strategy selected tva.1.1.1 tva.1.2)
            (selectedSideMass G strategy selected tva.1)) i tva.2)
      (fun tva => selectedSideWeight G strategy selected tva.1 *
        (selectedInputProfile G selected tva.1.1 i).weight tva.2)) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  exact finite_side_information_bound (selectedInputLaw G selected).weight
    (fun t i => (selectedInputProfile G selected t i).weight)
    (fun tv => selectedLikelihood G strategy selected tv.1.1 tv.2)
    (selectedSideMass G strategy selected) (selectedSideWeight G strategy selected)
    (gameLaw_isProbability _) (fun t i => gameLaw_isProbability _)
    (fun tv => selectedLikelihood_nonnegative G strategy selected tv.1.1 tv.2)
    (fun t => selectedLikelihood_sum_le_one G strategy selected t.1)
    (fun _ => rfl) positive (selectedSideMass_total G strategy selected) (fun _ => rfl)

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedJointWeight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (z : (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ × Q₂)) : ℝ :=
  (selectedInputLaw G selected).weight z.1.1 *
    independentProduct (fun i => (selectedInputProfile G selected z.1.1 i).weight) z.2 *
      selectedLikelihood G strategy selected z.1.1.1 z.1.2 z.2 /
        G.selectedSuccess strategy selected

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) :
    firstMarginal (selectedJointWeight G strategy selected) tv =
      selectedSideWeight G strategy selected tv := by
  simp only [firstMarginal, selectedJointWeight, selectedSideWeight, selectedSideMass,
    div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem selectedJointWeight_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (tv) (u) :
    selectedJointWeight G strategy selected (tv,u) =
      (∏ i : selected, G.questions.weight (tv.1.1 i)) *
        (∏ i : {i : Fin n // i ∉ selected}, (revealLaw G.questions).weight (u i,tv.1.2 i)) *
          selectedLikelihood G strategy selected tv.1.1 tv.2 u /
            G.selectedSuccess strategy selected := by
  unfold selectedJointWeight
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    independentProduct, selectedInputProfile]
  rw [mul_assoc (∏ i : selected, G.questions.weight (tv.1.1 i)), reveal_product_factorization]

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (maskedJoint p) z.1 * (revealProfile μ z.1.2).weight z.2

def leftRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ y, p (z.1, (z.2.1, y))) * (revealProfile μ (Sum.inl z.2.1)).weight z.2

def rightRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ x, p (z.1, (x, z.2.2))) * (revealProfile μ (Sum.inr z.2.2)).weight z.2

omit [Fintype S] in
theorem abs_masked_inl (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (u x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inl u), (x, y)) - maskedModel μ p ((s, Sum.inl u), (x, y))| =
      if x = u then |p (s, (x, y)) - leftRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hx : x = u
  · subst x
    simp only [maskedModel, maskedJoint_firstMarginal_inl]
    simpa [maskedJoint, leftRevealModel] using
      abs_half_sub_half_mul_inline_MaskedVariation (p (s, (u, y))) (∑ v, p (s, (u, v)))
        ((revealProfile μ (Sum.inl u)).weight (u, y))
  · have hs := revealProfile_inl_support μ u (x, y) hx
    simp [maskedJoint, maskedModel, hs, hx, Ne.symm hx]

omit [Fintype S] in
theorem abs_masked_inr (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (v : Y) (x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inr v), (x, y)) - maskedModel μ p ((s, Sum.inr v), (x, y))| =
      if y = v then |p (s, (x, y)) - rightRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hy : y = v
  · subst y
    simp only [maskedModel, maskedJoint_firstMarginal_inr]
    simpa [maskedJoint, rightRevealModel] using
      abs_half_sub_half_mul_inline_MaskedVariation (p (s, (x, v))) (∑ u, p (s, (u, v)))
        ((revealProfile μ (Sum.inr v)).weight (x, v))
  · have hs := revealProfile_inr_support μ v (x, y) hy
    simp [maskedJoint, maskedModel, hs, hy, Ne.symm hy]

theorem masked_totalVariation_identity (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) =
      Information.totalVariation p (leftRevealModel μ p) +
        Information.totalVariation p (rightRevealModel μ p) := by
  have hleft (s : S) :
      (∑ u : X, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) =
      (∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 := by
    simp_rw [Fintype.sum_prod_type, abs_masked_inl]
    simp [Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]
  have hright (s : S) :
      (∑ v : Y, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
      (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2 := by
    have hcollapse :
        (∑ v : Y, ∑ q : X × Y,
          |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
        ∑ v : Y, ∑ x : X, |p (s, (x, v)) - rightRevealModel μ p (s, (x, v))| / 2 := by
      simp [Fintype.sum_prod_type, abs_masked_inr]
    rw [hcollapse, Finset.sum_comm]
    simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_mul]
  have hmass :
      (∑ z : (S × (X ⊕ Y)) × (X × Y), |maskedJoint p z - maskedModel μ p z|) =
      ((∑ z : S × (X × Y), |p z - leftRevealModel μ p z|) +
       (∑ z : S × (X × Y), |p z - rightRevealModel μ p z|)) / 2 := by
    calc
      _ = ∑ s : S,
          ((∑ u : X, ∑ q : X × Y, |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) +
           (∑ v : Y, ∑ q : X × Y, |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|)) := by
        simp only [Fintype.sum_prod_type, Fintype.sum_sum_type]
      _ = ∑ s : S,
          ((∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 +
           (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2) := by
        simp_rw [hleft, hright]
      _ = _ := by
        simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul, add_mul]
  unfold Information.totalVariation
  rw [hmass]
  ring

theorem leftRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (leftRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (rightRevealModel μ p)]

theorem rightRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (rightRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (leftRevealModel μ p)]

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def partialRevealWeight (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) : ℝ :=
  μ.weight (u j) * ∏ i : {i : I // i ≠ j}, (revealLaw μ).weight (u i.1,rest i)

theorem product_reveal_at (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (r : X ⊕ Y) (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    (∏ i, (revealLaw μ).weight (u i,mergeAt j r rest i)) =
      (if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
      (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [mergeAt_self, mergeAt_other, revealLaw_weight]
  by_cases hl : r = Sum.inl (u j).1 <;> by_cases hr : r = Sum.inr (u j).2 <;>
    simp [hl, hr, partialRevealWeight, revealLaw_weight] <;> ring

def partialRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    partialRevealWeight μ j z.1.2 u * likelihood z.1.1 u else 0

def fullRevealMarginal (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then
    (∏ i, (revealLaw μ).weight (u i,z.1.2 i)) * likelihood z.1.1 u else 0

omit [Fintype T] in

theorem fullRevealMarginal_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealMarginal μ j likelihood ((t,mergeAt j r rest),q) =
      maskedJoint (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  classical
  unfold fullRevealMarginal
  simp_rw [product_reveal_at]
  have hpoint (u : I → X × Y) :
      (if u j = q then
        ((if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
         (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0)) *
          likelihood t u else 0) =
      (if r = Sum.inl q.1 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) +
      (if r = Sum.inr q.2 then
        (if u j = q then partialRevealWeight μ j rest u * likelihood t u else 0) / 2 else 0) := by
    by_cases hu : u j = q
    · rw [hu]
      by_cases hl : r = Sum.inl q.1 <;> by_cases hr : r = Sum.inr q.2 <;>
        simp [hl, hr] <;> ring
    · simp [hu]
  simp_rw [hpoint]
  simp [maskedJoint, partialRevealMarginal, Finset.sum_add_distrib,
    Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]

def fullRevealModel (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    (T × (I → X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (fullRevealMarginal μ j likelihood) z.1 *
    (revealProfile μ (z.1.2 j)).weight z.2

omit [Fintype T] in
theorem fullRevealModel_merge (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) (t : T)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (r : X ⊕ Y) (q : X × Y) :
    fullRevealModel μ j likelihood ((t,mergeAt j r rest),q) =
      maskedModel μ (partialRevealMarginal μ j likelihood) (((t,rest),r),q) := by
  simp only [fullRevealModel, Information.firstMarginal, fullRevealMarginal_merge,
    mergeAt_self, maskedModel]

theorem fullReveal_totalVariation (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (fullRevealMarginal μ j likelihood) (fullRevealModel μ j likelihood) =
      Information.totalVariation (maskedJoint (partialRevealMarginal μ j likelihood))
        (maskedModel μ (partialRevealMarginal μ j likelihood)) := by
  calc
    _ = Information.totalVariation
        (fun z => fullRevealMarginal μ j likelihood ((revealSplitEquiv (T := T) j).symm z))
        (fun z => fullRevealModel μ j likelihood ((revealSplitEquiv (T := T) j).symm z)) :=
      (totalVariation_comp_equiv (revealSplitEquiv (T := T) j).symm _ _).symm
    _ = _ := by
      congr 1 <;> funext z
      · exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
      · exact fullRevealModel_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2

theorem leftReveal_full_error (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (partialRevealMarginal μ j likelihood)
      (leftRevealModel μ (partialRevealMarginal μ j likelihood)) ≤
      2 * Information.totalVariation (fullRevealMarginal μ j likelihood)
        (fullRevealModel μ j likelihood) := by
  rw [fullReveal_totalVariation]
  exact leftRevealModel_totalVariation_le μ _

theorem rightReveal_full_error (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    Information.totalVariation (partialRevealMarginal μ j likelihood)
      (rightRevealModel μ (partialRevealMarginal μ j likelihood)) ≤
      2 * Information.totalVariation (fullRevealMarginal μ j likelihood)
        (fullRevealModel μ j likelihood) := by
  rw [fullReveal_totalVariation]
  exact rightRevealModel_totalVariation_le μ _

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedRawMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂) → ℝ := by
  classical
  exact fun z => ∑ u, if u j = z.2 then selectedJointWeight G strategy selected (z.1,u) else 0

theorem selectedPosterior_eq_raw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) (q) :
    selectedSideWeight G strategy selected tv * coordinateMarginal
      (posteriorOrOriginal
        (independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight))
        (selectedLikelihood G strategy selected tv.1.1 tv.2)
        (selectedSideMass G strategy selected tv)) j q =
      selectedRawMarginal G strategy selected j (tv,q) := by
  classical
  rw [selectedSideWeight]
  have h := weighted_coordinate_posterior_recombine
    (independentProduct (fun i => (selectedInputProfile G selected tv.1 i).weight))
    (selectedLikelihood G strategy selected tv.1.1 tv.2)
    (independentProduct_isProbability _
      (fun i => gameLaw_isProbability (selectedInputProfile G selected tv.1 i)))
    (selectedLikelihood_nonnegative G strategy selected tv.1.1 tv.2)
    (c := selectedSideMass G strategy selected tv) rfl
    ((selectedInputLaw G selected).weight tv.1) (G.selectedSuccess strategy selected) j q
  rw [h]
  simp only [Finset.mul_sum, selectedRawMarginal, selectedJointWeight]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = q
  · simp only [ite_eq_left hu]
    ring
  · simp [hu]

theorem selectedRawMarginal_firstMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (tv) :
    firstMarginal (selectedRawMarginal G strategy selected j) tv =
      selectedSideWeight G strategy selected tv := by
  classical
  simp only [firstMarginal, selectedRawMarginal]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  exact selectedJointWeight_firstMarginal G strategy selected tv

theorem selected_raw_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, totalVariation
      (selectedRawMarginal G strategy selected j)
      (fun z => selectedSideWeight G strategy selected z.1 *
        (selectedInputProfile G selected z.1.1 j).weight z.2)) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  have h := selected_information_bound G strategy selected positive
  simp_rw [selectedPosterior_eq_raw] at h
  exact h

def selectedOutsideLikelihood (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) : ℝ :=
  (∏ i : selected, G.questions.weight (t.1 i)) *
    selectedLikelihood G strategy selected t.1 t.2 u / G.selectedSuccess strategy selected

theorem selectedRawMarginal_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    selectedRawMarginal G strategy selected j
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  classical
  change selectedRawMarginal G strategy selected j
    (((z.1.1.1,z.1.2),z.1.1.2),z.2) = _
  simp only [selectedRawMarginal, fullRevealMarginal]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : u j = z.2
  · simp only [ite_eq_left hu, selectedJointWeight_factorization, selectedOutsideLikelihood]
    ring
  · simp [hu]

theorem selectedRawReference_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) (z) :
    (fun w => selectedSideWeight G strategy selected w.1 *
      (selectedInputProfile G selected w.1.1 j).weight w.2)
        ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z) =
      fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected) z := by
  change selectedSideWeight G strategy selected ((z.1.1.1,z.1.2),z.1.1.2) *
    (revealProfile G.questions (z.1.2 j)).weight z.2 = _
  rw [← selectedRawMarginal_firstMarginal G strategy selected j]
  unfold firstMarginal fullRevealModel
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact selectedRawMarginal_fullReveal G strategy selected j (z.1,q)

theorem selected_raw_error_eq_fullReveal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedRawMarginal G strategy selected j)
      (fun z => selectedSideWeight G strategy selected z.1 *
        (selectedInputProfile G selected z.1.1 j).weight z.2) =
      totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
  rw [← totalVariation_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm]
  congr 1 <;> funext z
  · exact selectedRawMarginal_fullReveal G strategy selected j z
  · exact selectedRawReference_fullReveal G strategy selected j z

theorem selected_fullReveal_information_bound [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected))) ≤
      Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
        (Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) +
          Real.log (1 / G.selectedSuccess strategy selected))) := by
  have h := selected_raw_information_bound G strategy selected positive
  simp_rw [selected_raw_error_eq_fullReveal] at h
  exact h

theorem selected_leftReveal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected)))) ≤
      2 * selectedInformationRadius G strategy selected := by
  calc
    _ ≤ ∑ j : {i : Fin n // i ∉ selected},
        2 * totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
      apply Finset.sum_le_sum
      intro j _
      exact leftReveal_full_error G.questions j _
    _ = 2 * ∑ j : {i : Fin n // i ∉ selected},
        totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (selected_fullReveal_information_bound G strategy selected positive) (by norm_num)

theorem selected_rightReveal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected)))) ≤
      2 * selectedInformationRadius G strategy selected := by
  calc
    _ ≤ ∑ j : {i : Fin n // i ∉ selected},
        2 * totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) := by
      apply Finset.sum_le_sum
      intro j _
      exact rightReveal_full_error G.questions j _
    _ = 2 * ∑ j : {i : Fin n // i ∉ selected},
        totalVariation (fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
          (fullRevealModel G.questions j (selectedOutsideLikelihood G strategy selected)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (selected_fullReveal_information_bound G strategy selected positive) (by norm_num)

end
end DFVSGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_QuestionMarginal
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_question_probability (G : Game Q₁ Q₂ A₁ A₂)
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedSplitLaw G selected).probability
      (fun q => event (selectedQuestionTuple selected q.1 q.2)) =
        (G.repetition n).questions.probability event := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability event
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

theorem selectedJoint_eventMass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ tv : SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
      (selectedInputLaw G selected).weight tv.1 *
        ∑ u, independentProduct
          (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
            selectedLikelihood G strategy selected tv.1.1 tv.2 u *
              (if event (selectedQuestionTuple selected tv.1.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) := by
  classical
  have hlabel (t : SelectedInput Q₁ Q₂ selected) :
      (∑ v, ∑ u, independentProduct
        (fun i => (selectedInputProfile G selected t i).weight) u *
          selectedLikelihood G strategy selected t.1 v u *
            (if event (selectedQuestionTuple selected t.1 u) then 1 else 0)) =
      ∑ u, independentProduct
        (fun i => (selectedInputProfile G selected t i).weight) u *
          (if G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u) &&
            event (selectedQuestionTuple selected t.1 u) then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_mul, ← Finset.mul_sum, selectedLikelihood_sum]
    cases hw : G.selectedWins strategy selected (selectedQuestionTuple selected t.1 u) <;>
      cases he : event (selectedQuestionTuple selected t.1 u) <;> simp []
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hlabel]
  rw [Fintype.sum_prod_type]
  simp only [selectedInputLaw, FiniteDistribution.product, FiniteDistribution.table,
    selectedInputProfile, independentProduct]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hforget (fixed : selected → Q₁ × Q₂) :=
    reveal_product_expectation G.questions
      (fun u : {i : Fin n // i ∉ selected} → Q₁ × Q₂ =>
        if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
          event (selectedQuestionTuple selected fixed u) then (1 : ℝ) else 0)
  simp_rw [hforget]
  have h := selectedSplit_question_probability G selected
    (fun q => G.selectedWins strategy selected q && event q)
  simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.table, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_assoc] using h

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games Information

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedTupleLikelihood_mass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) :
    (∑ questions, independentProduct (fun _ : Fin n => G.questions.weight) questions *
      selectedTupleLikelihood G strategy selected questions) =
        G.selectedSuccess strategy selected := by
  classical
  change _ = ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability
    (G.selectedWins strategy selected)
  rw [FiniteDistribution.probability_transport]
  simp only [FiniteDistribution.probability, FiniteDistribution.iid, independentProduct,
    selectedTupleLikelihood, mul_ite, mul_one, mul_zero]

def selectedQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (i : Fin n) : FiniteDistribution (Q₁ × Q₂) :=
  ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).pushforward
    (fun questions => (questions.1 i, questions.2 i))

theorem selectedQuestionMarginal_weight (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (i : Fin n) :
    (selectedQuestionMarginal G strategy selected positive i).weight =
      coordinateMarginal
        (posterior (independentProduct (fun _ : Fin n => G.questions.weight))
          (selectedTupleLikelihood G strategy selected) (G.selectedSuccess strategy selected)) i := by
  classical
  funext a
  simp only [selectedQuestionMarginal, FiniteDistribution.pushforward,
    FiniteDistribution.condition, coordinateMarginal]
  refine Fintype.sum_equiv (Game.tupleQuestionEquiv (Q₁ := Q₁) (Q₂ := Q₂) n).symm _ _ ?_
  intro questions
  cases he : G.selectedWins strategy selected questions <;>
    simp [Game.repetition_question_weight, Game.tupleQuestionEquiv,
      posterior, independentProduct, selectedTupleLikelihood, Game.selectedSuccess, he]

theorem selectedQuestionMarginal_totalVariation_sq_sum_le_log
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : Fin n,
      (selectedQuestionMarginal G strategy selected positive i).totalVariation G.questions ^ 2) ≤
        Real.log (1 / G.selectedSuccess strategy selected) := by
  classical
  change (∑ i : Fin n, Information.totalVariation
    (selectedQuestionMarginal G strategy selected positive i).weight G.questions.weight ^ 2) ≤ _
  simp_rw [selectedQuestionMarginal_weight]
  exact posterior_coordinate_totalVariation_sq_sum_le_log
    (fun _ : Fin n => G.questions.weight) (fun _ => gameLaw_isProbability G.questions)
    (selectedTupleLikelihood G strategy selected)
    (selectedTupleLikelihood_nonnegative G strategy selected)
    (selectedTupleLikelihood_le_one G strategy selected)
    positive (selectedTupleLikelihood_mass G strategy selected)

theorem unselectedQuestionMarginal_totalVariation_sq_sum_le_log
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions ^ 2) ≤
        Real.log (1 / G.selectedSuccess strategy selected) := by
  classical
  let d : Fin n → ℝ := fun i =>
    (selectedQuestionMarginal G strategy selected positive i).totalVariation G.questions
  have hfull := selectedQuestionMarginal_totalVariation_sq_sum_le_log G strategy selected positive
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => i ∈ selected)
    (fun i => d i ^ 2)
  have hinst : Subtype.fintype (fun i : Fin n => i ∈ selected) =
      Finset.Subtype.fintype selected := Subsingleton.elim _ _
  rw [hinst] at hsplit
  have hselected : 0 ≤ ∑ i : {i : Fin n // i ∈ selected}, d i.1 ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  change (∑ i : {i : Fin n // i ∉ selected}, d i.1 ^ 2) ≤ _
  change (∑ i : Fin n, d i ^ 2) ≤ _ at hfull
  linarith

theorem unselectedQuestionMarginal_totalVariation_sum_le_sqrt
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ i : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions) ≤
        Real.sqrt ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
          Real.log (1 / G.selectedSuccess strategy selected)) := by
  classical
  let d : {i : Fin n // i ∉ selected} → ℝ := fun i =>
    (selectedQuestionMarginal G strategy selected positive i.1).totalVariation G.questions
  have hsq := unselectedQuestionMarginal_totalVariation_sq_sum_le_log G strategy selected positive
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset {i : Fin n // i ∉ selected}) d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hln : 0 ≤ Real.log (1 / G.selectedSuccess strategy selected) :=
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)).trans hsq
  have hcard : 0 ≤ (Fintype.card {i : Fin n // i ∉ selected} : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsq hcard
  have hsqrt := Real.sq_sqrt (mul_nonneg hcard hln)
  have hsqrtpos := Real.sqrt_nonneg
    ((Fintype.card {i : Fin n // i ∉ selected} : ℝ) *
      Real.log (1 / G.selectedSuccess strategy selected))
  change (∑ i, d i) ≤ _
  change (∑ i, d i ^ 2) ≤ _ at hsq
  change (Fintype.card {i : Fin n // i ∉ selected} : ℝ) * (∑ i, d i ^ 2) ≤ _ at hmul
  nlinarith

end

end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem partialRevealMarginal_isProbability
    {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ)
    (hp : IsProbability (fullRevealMarginal μ j likelihood)) :
    IsProbability (partialRevealMarginal μ j likelihood) := by
  apply (maskedJoint_isProbability_iff _).mp
  have h := isProbability_comp_equiv (revealSplitEquiv (T := T) j).symm _ hp
  have he : (fun z => fullRevealMarginal μ j likelihood
      ((revealSplitEquiv (T := T) j).symm z)) =
      maskedJoint (partialRevealMarginal μ j likelihood) := by
    funext z
    exact fullRevealMarginal_merge μ j likelihood z.1.1.1 z.1.1.2 z.1.2 z.2
  rw [he] at h
  exact h

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem leftCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1) ≤
      totalVariation p (leftRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapSeedLeft (S := S) (X := X) (Y := Y)
  let p' : X × (S × Y) → ℝ := fun z => p (e z)
  have h := ProfileCorrection.left_profile_correction p' μ.weight fallback
    (μ.pushforward Prod.snd).weight
    (isProbability_comp_equiv e p hp) (gameLaw_isProbability μ) hf
    (gameLaw_isProbability (μ.pushforward Prod.snd))
  have hs : ProfileCorrection.seedQuestionMarginal p' = leftCommonMarginal p := rfl
  have hc : (fun z : X × (S × Y) => ProfileCorrection.seedQuestionMarginal p' (z.1,z.2.1) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2) =
      fun z => leftRevealModel μ p (e z) := by
    funext z
    change (∑ y, p (z.2.1,(z.1,y))) *
      conditionalKernel μ.weight (μ.pushforward Prod.snd).weight z.1 z.2.2 =
      (∑ y, p (z.2.1,(z.1,y))) *
        (revealProfile μ (Sum.inl z.1)).weight (z.1,z.2.2)
    rw [revealProfile_inl_diagonal]
  have hd : (fun z : X × (S × Y) => μ.weight (z.1,z.2.2) *
      conditionalKernel (ProfileCorrection.seedQuestionMarginal p') fallback z.1 z.2.1) =
      fun z => μ.weight (e z).2 * leftCommonProfile p fallback (e z).2.1 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (leftRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * leftCommonProfile p fallback z.2.1 z.1)] at h
  have hm : firstMarginal p' = firstMarginal (secondMarginal p) := by
    funext x
    simp only [firstMarginal, secondMarginal, Fintype.sum_prod_type, p', e, swapSeedLeft]
    exact Finset.sum_comm
  rw [hm] at h
  exact h.trans (add_le_add le_rfl (firstMarginal_totalVariation_le (secondMarginal p) μ.weight))

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem finiteDistribution_nonempty {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    Nonempty A := by
  have hsum : (∑ a, μ.weight a) ≠ 0 := by rw [μ.normalized]; norm_num
  obtain ⟨a, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨a⟩

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem partialRevealMarginal_secondMarginal
    (μ : FiniteDistribution (X × Y)) (j : I)
    (likelihood : T → (I → X × Y) → ℝ) :
    secondMarginal (partialRevealMarginal μ j likelihood) =
      secondMarginal (fullRevealMarginal μ j likelihood) := by
  classical
  funext q
  calc
    _ = ∑ z : (T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y),
        maskedJoint (partialRevealMarginal μ j likelihood) (z,q) := by
      simp [secondMarginal, Fintype.sum_prod_type, maskedJoint]
    _ = _ := by
      apply Fintype.sum_equiv (revealDataSplitEquiv (T := T) j).symm
      intro z
      exact (fullRevealMarginal_merge μ j likelihood z.1.1 z.1.2 z.2 q).symm

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedFullReveal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) =
        secondMarginal (selectedRawMarginal G strategy selected j) := by
  classical
  funext q
  apply Fintype.sum_equiv
    (selectedObservationDataEquiv (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected).symm
  intro z
  exact (selectedRawMarginal_fullReveal G strategy selected j (z,q)).symm

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedQuestionMarginal_error_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected},
      (selectedQuestionMarginal G strategy selected positive j.1).totalVariation G.questions) ≤
      selectedInformationRadius G strategy selected :=
  (unselectedQuestionMarginal_totalVariation_sum_le_sqrt G strategy selected positive).trans
    (selectedQuestionRadius_le_informationRadius G strategy selected)

end
end DFVSGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SelectedLikelihood
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealLeftFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (x : X) : ℝ :=
  match r with
  | Sum.inl u => if x = u then 1 else 0
  | Sum.inr v => μ.weight (x,v) / 2

def revealRightFactor (μ : FiniteDistribution (X × Y)) (r : X ⊕ Y) (y : Y) : ℝ :=
  match r with
  | Sum.inl u => μ.weight (u,y) / 2
  | Sum.inr v => if y = v then 1 else 0

omit [DecidableEq Y] in
theorem revealLeftFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) : 0 ≤ revealLeftFactor μ r x := by
  cases r with
  | inl u => simp only [revealLeftFactor]; split <;> norm_num
  | inr v => exact div_nonneg (μ.nonnegative _) (by norm_num)

omit [DecidableEq X] in
theorem revealRightFactor_nonnegative (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (y : Y) : 0 ≤ revealRightFactor μ r y := by
  cases r with
  | inl u => exact div_nonneg (μ.nonnegative _) (by norm_num)
  | inr v => simp only [revealRightFactor]; split <;> norm_num

theorem revealLaw_factorization (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) (y : Y) :
    (revealLaw μ).weight ((x,y),r) =
      revealLeftFactor μ r x * revealRightFactor μ r y := by
  rw [revealLaw_weight]
  cases r with
  | inl u =>
    by_cases h : x = u
    · subst x; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]
  | inr v =>
    by_cases h : y = v
    · subst y; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]

def partialLeftFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (x : I → X) : ℝ :=
  ∏ i, revealLeftFactor μ (rest i) (x i.1)

def partialRightFactor (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (y : I → Y) : ℝ :=
  ∏ i, revealRightFactor μ (rest i) (y i.1)

theorem partialRevealWeight_factorization (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    partialRevealWeight μ j rest u =
      μ.weight (u j) * partialLeftFactor μ j rest (fun i => (u i).1) *
        partialRightFactor μ j rest (fun i => (u i).2) := by
  have hpoint (i : {i : I // i ≠ j}) :
      (revealLaw μ).weight (u i.1,rest i) =
        revealLeftFactor μ (rest i) (u i.1).1 * revealRightFactor μ (rest i) (u i.1).2 :=
    revealLaw_factorization μ (rest i) (u i.1).1 (u i.1).2
  simp only [partialRevealWeight, partialLeftFactor, partialRightFactor,
    hpoint, Finset.prod_mul_distrib]
  ring

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

def updatedTableFallback (μ : FiniteDistribution X) (j : I) (x : X) :
    FiniteDistribution (I → X) :=
  (FiniteDistribution.table (fun _ : I => μ)).pushforward
    (fun l => Function.update l j x)

theorem updatedTableFallback_zero (μ : FiniteDistribution X) (j : I) (x : X)
    (l : I → X) (hne : l j ≠ x) :
    (updatedTableFallback μ j x).weight l = 0 := by
  classical
  simp only [updatedTableFallback, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  apply ite_eq_right
  intro h
  have he := congrFun h j
  exact hne (by simpa only [Function.update_self] using he.symm)

theorem normalizeOr_weight_eq_zero_of_zero
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (fallback : FiniteDistribution X)
    (x : X) (hraw : w x = 0) (hdefault : fallback.weight x = 0) :
    (normalizeOr w hw fallback).weight x = 0 := by
  classical
  unfold normalizeOr
  split
  · change normalizedWeight w x = 0
    simp only [normalizedWeight, hraw, zero_div]
  · exact hdefault

end LocalNormalization

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedLeftRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) : ℝ :=
  (if l j = x then 1 else 0) * partialLeftFactor G.questions j s.2 l *
    selectedLocalTest strategy.1 selected (fun i => (s.1.1 i).1) s.1.2.1 l

def selectedRightRaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) : ℝ :=
  (if r j = y then 1 else 0) * partialRightFactor G.questions j s.2 r *
    selectedLocalTest strategy.2 selected (fun i => (s.1.1 i).2) s.1.2.2 r

omit [DecidableEq Q₂] in
theorem selectedLeftRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) :
    0 ≤ selectedLeftRaw G strategy selected j s x l := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealLeftFactor_nonnegative G.questions (s.2 i) (l i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

omit [DecidableEq Q₁] in
theorem selectedRightRaw_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) :
    0 ≤ selectedRightRaw G strategy selected j s y r := by
  apply mul_nonneg
  · apply mul_nonneg
    · split <;> norm_num
    · exact Finset.prod_nonneg (fun i _ => revealRightFactor_nonnegative G.questions (s.2 i) (r i.1))
  · exact selectedLocalTest_nonnegative _ _ _ _ _

def selectedLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₁) :=
  normalizeOr (selectedLeftRaw G strategy selected j s x)
    (selectedLeftRaw_nonnegative G strategy selected j s x)
    (updatedTableFallback (G.questions.pushforward Prod.fst) j x)

def selectedRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) : FiniteDistribution ({i : Fin n // i ∉ selected} → Q₂) :=
  normalizeOr (selectedRightRaw G strategy selected j s y)
    (selectedRightRaw_nonnegative G strategy selected j s y)
    (updatedTableFallback (G.questions.pushforward Prod.snd) j y)

omit [DecidableEq Q₂] in
theorem selectedLeftCompletion_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) (hne : l j ≠ x) :
    (selectedLeftCompletion G strategy selected j s x).weight l = 0 := by
  apply normalizeOr_weight_eq_zero_of_zero
  · simp only [selectedLeftRaw, ite_eq_right hne, zero_mul]
  · exact updatedTableFallback_zero _ j x l hne

omit [DecidableEq Q₁] in
theorem selectedRightCompletion_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) (hne : r j ≠ y) :
    (selectedRightCompletion G strategy selected j s y).weight r = 0 := by
  apply normalizeOr_weight_eq_zero_of_zero
  · simp only [selectedRightRaw, ite_eq_right hne, zero_mul]
  · exact updatedTableFallback_zero _ j y r hne

def selectedCompletionScale (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) : ℝ :=
  G.questions.weight xy * (∏ i : selected, G.questions.weight (s.1.1 i)) *
    (if selectedLabelAccepts G selected s.1.1 s.1.2 then 1 else 0) /
      G.selectedSuccess strategy selected

theorem selected_completion_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂)
    (l : {i : Fin n // i ∉ selected} → Q₁)
    (r : {i : Fin n // i ∉ selected} → Q₂) :
    selectedCompletionScale G strategy selected j s xy *
        selectedLeftRaw G strategy selected j s xy.1 l *
        selectedRightRaw G strategy selected j s xy.2 r =
      if (l j, r j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (l i,r i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (l i,r i))
      else 0 := by
  rcases xy with ⟨x,y⟩
  by_cases hl : l j = x <;> by_cases hr : r j = y
  · rw [ite_eq_left (Prod.ext hl hr), partialRevealWeight_factorization]
    cases hacc : selectedLabelAccepts G selected s.1.1 s.1.2 <;>
      simp [selectedOutsideLikelihood, selectedLikelihood_factorization,
        selectedCompletionScale, selectedLeftRaw, selectedRightRaw, hl, hr, hacc] ; ring
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]

end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section

theorem partialRevealWeight_forget
    {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I) (u : I → X × Y) :
    (∑ rest : {i : I // i ≠ j} → X ⊕ Y, partialRevealWeight μ j rest u) =
      ∏ i, μ.weight (u i) := by
  have h := reveal_product_forget μ (fun i : {i : I // i ≠ j} => u i.1)
  simp_rw [reveal_product_factorization] at h
  simp only [partialRevealWeight, ← Finset.mul_sum]
  rw [h]
  exact (Fintype.prod_eq_mul_prod_subtype_ne (fun i => μ.weight (u i)) j).symm

theorem partialReveal_event_forget
    {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I) (f : (I → X × Y) → ℝ) :
    (∑ rest : {i : I // i ≠ j} → X ⊕ Y,
      ∑ u : I → X × Y, partialRevealWeight μ j rest u * f u) =
      ∑ u, (∏ i, μ.weight (u i)) * f u := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul, partialRevealWeight_forget]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedOutsideLikelihood_event_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        (∏ i, G.questions.weight (u i)) * selectedOutsideLikelihood G strategy selected t u *
          (if event (selectedQuestionTuple selected t.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) /
          G.selectedSuccess strategy selected := by
  classical
  have hlabel (fixed : selected → Q₁ × Q₂)
      (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
      (∑ label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
        (∏ i, G.questions.weight (u i)) *
          selectedOutsideLikelihood G strategy selected (fixed,label) u *
            (if event (selectedQuestionTuple selected fixed u) then 1 else 0)) =
      ((∏ i : selected, G.questions.weight (fixed i)) * (∏ i, G.questions.weight (u i)) *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
          event (selectedQuestionTuple selected fixed u) then 1 else 0)) /
            G.selectedSuccess strategy selected := by
    calc
      _ = (∏ i, G.questions.weight (u i)) *
          (∏ i : selected, G.questions.weight (fixed i)) *
          (∑ label, selectedLikelihood G strategy selected fixed label u) *
          (if event (selectedQuestionTuple selected fixed u) then 1 else 0) /
            G.selectedSuccess strategy selected := by
        simp only [selectedOutsideLikelihood, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro label _
        ring
      _ = _ := by
        rw [selectedLikelihood_sum]
        cases hw : G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) <;>
          cases he : event (selectedQuestionTuple selected fixed u) <;> simp [] ; ring
  calc
    _ = ∑ fixed : selected → Q₁ × Q₂,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          ∑ label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
            (∏ i, G.questions.weight (u i)) *
              selectedOutsideLikelihood G strategy selected (fixed,label) u *
                (if event (selectedQuestionTuple selected fixed u) then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro fixed _
      rw [Finset.sum_comm]
    _ = (∑ fixed : selected → Q₁ × Q₂,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          (∏ i : selected, G.questions.weight (fixed i)) * (∏ i, G.questions.weight (u i)) *
            (if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
              event (selectedQuestionTuple selected fixed u) then 1 else 0)) /
                G.selectedSuccess strategy selected := by
      simp_rw [hlabel]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by
      congr 1
      have h := selectedSplit_question_probability G selected
        (fun q => G.selectedWins strategy selected q && event q)
      simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
        FiniteDistribution.table, Fintype.sum_prod_type, mul_ite] using h

theorem selected_partial_event_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j,
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        partialRevealWeight G.questions j s.2 u *
          selectedOutsideLikelihood G strategy selected s.1 u *
            (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) /
          G.selectedSuccess strategy selected := by
  have hrest (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) :=
    partialReveal_event_forget G.questions j
      (fun u => selectedOutsideLikelihood G strategy selected t u *
        (if event (selectedQuestionTuple selected t.1 u) then 1 else 0))
  simp only [← mul_assoc] at hrest
  rw [Fintype.sum_prod_type]
  simp_rw [hrest]
  exact selectedOutsideLikelihood_event_sum G strategy selected event

def selectedFullLeftCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₁ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₁) :=
  (selectedLeftCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).1))

def selectedFullRightCompletion (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₂ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j) :
    FiniteDistribution (Fin n → Q₂) :=
  (selectedRightCompletion G strategy selected j q.2 q.1).pushforward
    (mergeCoordinates selected (fun i => (q.2.1.1 i).2))

omit [DecidableEq Q₂] in
theorem selectedFullLeftCompletion_support (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₁ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (l : Fin n → Q₁) (h : (selectedFullLeftCompletion G strategy selected j q).weight l ≠ 0) :
    l j.1 = q.1 := by
  classical
  by_contra hne
  apply h
  simp only [selectedFullLeftCompletion, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  split
  · rename_i he
    apply selectedLeftCompletion_zero
    intro ht
    apply hne
    have hcoord := congrFun he j.1
    simpa [mergeCoordinates, j.property, ht] using hcoord.symm
  · rfl

omit [DecidableEq Q₁] in
theorem selectedFullRightCompletion_support (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₂ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (r : Fin n → Q₂) (h : (selectedFullRightCompletion G strategy selected j q).weight r ≠ 0) :
    r j.1 = q.1 := by
  classical
  by_contra hne
  apply h
  simp only [selectedFullRightCompletion, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  split
  · rename_i he
    apply selectedRightCompletion_zero
    intro ht
    apply hne
    have hcoord := congrFun he j.1
    simpa [mergeCoordinates, j.property, ht] using hcoord.symm
  · rfl

theorem selected_full_completion_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    ((selectedFullLeftCompletion G strategy selected j (xy.1,s)).product
      (selectedFullRightCompletion G strategy selected j (xy.2,s))).probability event =
    ∑ lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂),
      ((selectedLeftCompletion G strategy selected j s xy.1).product
        (selectedRightCompletion G strategy selected j s xy.2)).weight lr *
          (if event (selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i)))
            then 1 else 0) := by
  rw [selectedFullLeftCompletion, selectedFullRightCompletion,
    ← FiniteDistribution.product_pushforward, FiniteDistribution.probability_pushforward]
  unfold FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro lr _
  have he : selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i)) =
      (mergeCoordinates selected (fun i => (s.1.1 i).1) lr.1,
       mergeCoordinates selected (fun i => (s.1.1 i).2) lr.2) :=
    Prod.ext (selectedQuestionTuple_left selected s.1.1 _)
      (selectedQuestionTuple_right selected s.1.1 _)
  rw [he]
  cases hevent : event (mergeCoordinates selected (fun i => (s.1.1 i).1) lr.1,
    mergeCoordinates selected (fun i => (s.1.1 i).2) lr.2) <;> simp [hevent]

end
end DFVSGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_CompletedSampling
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section DistributionIdentities

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem product_pushforward_eq_mixture_right (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (f : A × B → C) :
    (μ.product ν).pushforward f =
      ν.mixture (fun b => μ.pushforward (fun a => f (a, b))) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f (a, b) = c <;> simp [h, mul_comm]

theorem product_product_pushforward_eq_mixture (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (κ : FiniteDistribution C) (f : A → B → C → D) :
    (μ.product (ν.product κ)).pushforward (fun z => f z.1 z.2.1 z.2.2) =
      (μ.product ν).mixture
        (fun z => κ.pushforward (fun c => f z.1 z.2 c)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro d
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

theorem mixture_totalVariation_le (μ ν : FiniteDistribution A)
    (K : A → FiniteDistribution B) :
    (μ.mixture K).totalVariation (ν.mixture K) ≤ μ.totalVariation ν := by
  simpa only [FiniteDistribution.totalVariation, FiniteDistribution.mixture,
    Information.totalVariation, kernelPushforward] using
      totalVariation_kernelPushforward_le μ.weight ν.weight
        (fun a => (K a).weight) (fun a => Information.gameLaw_isProbability (K a))

end DistributionIdentities

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

def diagonalLaw (σ : FiniteDistribution (Z × S)) : FiniteDistribution (Z × S × S) :=
  Information.toGameLaw (diagonalWeights σ.weight)
    (diagonalWeights_isProbability _ (Information.gameLaw_isProbability σ))

theorem diagonalLaw_eq_pushforward (σ : FiniteDistribution (Z × S)) :
    diagonalLaw σ = σ.pushforward (fun z => (z.1, z.2, z.2)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨z, a, b⟩
  change diagonalWeights σ.weight (z, a, b) =
    (σ.pushforward (fun t => (t.1, t.2, t.2))).weight (z, a, b)
  simp only [diagonalWeights, FiniteDistribution.pushforward,
    Fintype.sum_prod_type, Prod.mk.injEq]
  by_cases hab : a = b
  · subst b
    simp [ite_and]
  · simp [hab, ite_and]

end Diagonal

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def seedLaw (γ : FiniteDistribution Γ)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (Seed Γ X Y S U V) :=
  γ.product (KernelSampling.seedLaw L R)

def completionKernel (L : X × S → FiniteDistribution U)
    (R : Y × S → FiniteDistribution V) (z : (X × Y) × S × S) :
    FiniteDistribution (U × V) :=
  (L (z.1.1, z.2.1)).product (R (z.1.2, z.2.2))

def outputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    FiniteDistribution (U × V) :=
  (seedLaw γ L R).mixture (fun seed =>
    μ.pushforward (fun q => (left sL seed q.1, right sR seed q.2)))

theorem outputLaw_eq_product_pushforward
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (μ.product (seedLaw γ L R)).pushforward
        (fun z => (left sL z.2 z.1.1, right sR z.2 z.1.2)) := by
  exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
    (fun z : (X × Y) × Seed Γ X Y S U V =>
      (left sL z.2 z.1.1, right sR z.2 z.1.2))).symm

end Completion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

def coordinateOutputLaw (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y)) :
    FiniteDistribution ((I → X) × (I → Y)) :=
  (seedLaw γ L R).mixture (fun seed => μ.pushforward
    (fun q => (coordinateLeft j sL seed q.1, coordinateRight j sR seed q.2)))

end

end DFVSGames.Foundations.Repetition.CompletedSampling

namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : ℕ}

theorem log_le_logTwo {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ logTwo x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_le : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 ; norm_num
  unfold logTwo
  apply (le_div_iff₀ htwo).2
  simpa using mul_le_mul_of_nonneg_left htwo_le hlog

theorem selectedLabels_log_le [Nonempty A₁] [Nonempty A₂]
    (selected : Finset (Fin n)) (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) ≤
      (selected.card : ℝ) * ell := by
  have ha : (1 : ℝ) ≤ Fintype.card A₁ := by exact_mod_cast Fintype.card_pos (α := A₁)
  have hb : (1 : ℝ) ≤ Fintype.card A₂ := by exact_mod_cast Fintype.card_pos (α := A₂)
  have hab : (1 : ℝ) ≤ (Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ) := by nlinarith
  rw [selectedLabels_card, Nat.cast_pow, Nat.cast_mul, Real.log_pow]
  exact mul_le_mul_of_nonneg_left ((log_le_logTwo hab).trans hell) (Nat.cast_nonneg _)

end
end DFVSGames.Foundations.Repetition

namespace DFVSGames.Foundations.Repetition.SelectionSequence

def SetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (S : Finset (Fin n)) (j : Fin n) : Prop :=
  P (insert j S) ≤ P S *
    (v + 15 * Real.sqrt (((S.card : ℝ) * ell + logTwo (1 / P S)) /
      ((n : ℝ) - S.card)))

theorem totalSetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∀ S, S.card < n → ∃ j, j ∉ S ∧ SetStep P v ell S j := by
  intro S hcard
  by_cases hp : 0 < P S
  · exact hpositive S hcard hp
  · obtain ⟨j, hj⟩ := exists_unused_inline_SelectionSequence S hcard
    have hz : P S = 0 := le_antisymm (le_of_not_gt hp) (hnonneg S)
    have hnext : P (insert j S) = 0 := le_antisymm
      ((hanti (Finset.subset_insert j S)).trans (le_of_eq hz)) (hnonneg (insert j S))
    refine ⟨j, hj, ?_⟩
    simpa only [SetStep, hnext, hz, zero_mul] using (le_refl (0 : ℝ))

theorem exists_scalar_sequence {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hempty : P ∅ = 1) (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∃ p : Nat → ℝ, p 0 = 1 ∧ (∀ m, 0 ≤ p m) ∧ Antitone p ∧
      ScalarRecurrence p n v ell ∧ p n = P Finset.univ := by
  let witness := totalSetStep P v ell hnonneg hanti hpositive
  let sets := selectedSet (SetStep P v ell) witness
  let p := fun m => P (sets m)
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · change P (selectedSet (SetStep P v ell) witness 0) = 1
    simpa only [selectedSet] using hempty
  · intro m
    exact hnonneg (sets m)
  · intro i j hij
    exact hanti (selectedSet_monotone (SetStep P v ell) witness hij)
  · intro m hm
    obtain ⟨j, _, hnext, hbound⟩ :=
      selectedSet_step (SetStep P v ell) witness m hm
    have hc : (selectedSet (SetStep P v ell) witness m).card = m := by
      rw [selectedSet_card, Nat.min_eq_left (Nat.le_of_lt hm)]
    change P (selectedSet (SetStep P v ell) witness (m + 1)) ≤ _
    rw [hnext]
    simpa only [SetStep, hc] using hbound
  · change P (selectedSet (SetStep P v ell) witness n) = P Finset.univ
    rw [selectedSet_univ]

open DFVSGames.Foundations.Games

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
variable [Nonempty A₁] [Nonempty A₂]

def ConditionalCoordinateBound (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (_hcard : S.card < n)
    (hp : 0 < G.selectedSuccess strategy S),
    ∃ j, j ∉ S ∧
      (((G.repetition n).questions.condition (G.selectedWins strategy S) hp).probability
        (G.coordinateWin strategy j)) ≤
        G.value + 15 * Real.sqrt
          (((S.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy S)) /
            ((n : ℝ) - S.card))

end DFVSGames.Foundations.Repetition.SelectionSequence

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_GeneratorModel
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceGeneratorModel

open Turing Complexity SourceRuntimeModel

def outputTape (u D : Nat) : Tape u D := workTape (.extra (.inr ()))

def headerControl (u D : Nat) : SourceHeaderCounts.Control ↪ Tape u D where
  toFun
    | .variableCount => variableHeader
    | .clauseCount => clauseHeader
    | .leftBlockSize => workTape .leftBlock
    | .rightTemporary => workTape .rank
    | .dummyIndex => workTape .dummy
    | .bitCount => workTape .bitCount
    | .occurrenceCount => workTape .occurrenceCount
    | .accA => workTape .accA
    | .accB => workTape .accB
    | .counter => workTape .counter
    | .scratch => workTape .arithScratch
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [variableHeader, clauseHeader,
      SourceLoopInit.variableHeader, SourceLoopInit.clauseHeader, workTape]

def headerSlots (u D : Nat) : SourceHeaderCounts.Layout u D ↪ Tape u D where
  toFun
    | .inl c => headerControl u D c
    | .inr i => workTape (.extra (.inl i))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((headerControl u D).injective h)
      | inr b => cases a <;> cases h
    | inr a =>
      cases b with
      | inl b => cases b <;> cases h
      | inr b => simpa [workTape] using h

noncomputable def coefficientKeys (u D : Nat) : List (SourceHeaderCounts.Coefficients u D) :=
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .left))).map Sum.inl ++
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .right))).map (fun i => Sum.inr (Sum.inl i)) ++
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .occurrences))).map (fun i => Sum.inr (Sum.inr i))

theorem mem_coefficientKeys (u D : Nat) (i : SourceHeaderCounts.Coefficients u D) :
    i ∈ coefficientKeys u D := by
  cases i with
  | inl i => simp [coefficientKeys]
  | inr i => cases i <;> simp [coefficientKeys]

noncomputable def workKeys (u D : Nat) : List (BodyWork (Extra u D)) :=
  [.leftBlock, .dummy, .bitCount, .occurrenceCount, .zero, .rank, .rightBase, .leftBase,
    .accA, .accB, .counter, .arithScratch, .coefficient, .queryTemporary,
    .queryScratch, .accumulator] ++
  (coefficientKeys u D).map (fun i => .extra (.inl i)) ++ [.extra (.inr ())]

theorem mem_workKeys (u D : Nat) (i : BodyWork (Extra u D)) : i ∈ workKeys u D := by
  cases i
  case extra e =>
    cases e with
    | inl i =>
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i, mem_coefficientKeys u D i, rfl⟩))
    | inr i => cases i; simp [workKeys]
  all_goals simp [workKeys]

noncomputable def allTapes (u D : Nat) : List (Tape u D) :=
  [.formula, .index, .work, .scratch, .copyScratch] ++
  (List.finRange u).map SourceContextLoad.Tape.current ++
  (List.finRange u).map SourceContextLoad.Tape.remaining ++
  (List.finRange u).flatMap (fun i =>
    (List.finRange 6).map (SourceContextLoad.Tape.field i)) ++
  [variableHeader, clauseHeader] ++ (workKeys u D).map workTape

theorem mem_allTapes (u D : Nat) (k : Tape u D) : k ∈ allTapes u D := by
  cases k with
  | formula => simp [allTapes]
  | index => simp [allTapes]
  | work => simp [allTapes]
  | scratch => simp [allTapes]
  | copyScratch => simp [allTapes]
  | current i => simp [allTapes]
  | remaining i => simp [allTapes]
  | field i j => simp [allTapes]
  | extra e =>
    cases e with
    | inl h => cases h <;> simp [allTapes, variableHeader, clauseHeader,
        SourceLoopInit.variableHeader, SourceLoopInit.clauseHeader]
    | inr w =>
      have h : workTape (u := u) w ∈ (workKeys u D).map (workTape (u := u)) :=
        List.mem_map.mpr ⟨w, mem_workKeys u D w, rfl⟩
      simp only [allTapes, List.mem_append]
      tauto

noncomputable def clearKeys (u D : Nat) : List (Tape u D) := by
  classical
  exact (allTapes u D).filter
    (fun k => decide (k ≠ accumulatorTape u D ∧ k ≠ outputTape u D))

theorem mem_clearKeys (u D : Nat) (k : Tape u D) :
    k ∈ clearKeys u D ↔ k ≠ accumulatorTape u D ∧ k ≠ outputTape u D := by
  classical
  simp [clearKeys, mem_allTapes]

theorem accumulator_ne_output (u D : Nat) : accumulatorTape u D ≠ outputTape u D := by
  simp [accumulatorTape, outputTape, workTape]

end DFVSGames.Foundations.Hastad.SourceGeneratorModel


namespace DFVSGames.Foundations.Hastad.SourceStartup

open Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.DFVSGames.Foundations.Hastad.SourceStartup.generatorModelExtraDecidableEq
def headerLayout (u D : Nat) : SourceHeaderAccumulate.Layout (Tape u D) where
  bits := workTape .bitCount
  count := workTape .occurrenceCount
  accumulator := workTape .accumulator
  bits_count := by simp [workTape]
  bits_accumulator := by simp [workTape]
  count_accumulator := by simp [workTape]

def countedTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceHeaderCounts.resultTapes (headerSlots u D) (initializedTapes F)
    F.«variables» F.clauses.length

def outputTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceHeaderAccumulate.resultTapes (headerLayout u D) (countedTapes F)
    (SourceHeaderCounts.bitValue u F.«variables» F.clauses.length)
    (SourceHeaderCounts.occurrenceValue u D F.clauses.length)

theorem initialized_clean (F : Target.Formula) :
    SourceHeaderCounts.Clean (headerSlots u D) (initializedTapes F) := by
  constructor
  · exact initialized_work F .leftBlock
  · exact initialized_work F .rank
  · exact initialized_work F .dummy
  · exact initialized_work F .bitCount
  · exact initialized_work F .occurrenceCount
  · exact initialized_work F .accA
  · exact initialized_work F .accB
  · exact initialized_work F .counter
  · exact initialized_work F .arithScratch
  · intro i; exact initialized_work F (.extra (.inl i))

theorem output_eq_ready (F : Target.Formula) (hm : 0 < F.clauses.length) :
    outputTapes (u := u) (D := D) F = readyTapes F := by
  funext tape
  cases tape
  case' extra extra =>
    cases extra <;> rename_i role <;> cases role
  case extra.inr.accumulator =>
    change outputTapes F (headerLayout u D).accumulator = _
    rw [outputTapes, SourceHeaderAccumulate.result_accumulator]
    have clean : countedTapes F (headerLayout u D).accumulator = [] := by
      rw [countedTapes, SourceHeaderCounts.result_frame]
      · exact initialized_work F .accumulator
      all_goals
        simp [headerLayout, SourceHeaderCounts.control, headerSlots, headerControl, workTape]
    rw [clean, List.append_nil, SourceHeaderCounts.bitValue_eq_nBits,
      SourceHeaderCounts.occurrenceValue_eq_length F u D hm]
    rfl
  all_goals
    simp [-SourceOccurrences.nBits_eq,
      outputTapes, SourceHeaderAccumulate.resultTapes, headerLayout,
      countedTapes, SourceHeaderCounts.resultTapes, SourceHeaderCounts.control,
      headerSlots, headerControl, workTape, readyTapes, SourceHeaderCounts.bitValue_eq_nBits,
      SourceHeaderCounts.occurrenceValue_eq_length F u D hm]

end

end DFVSGames.Foundations.Hastad.SourceStartup


namespace DFVSGames.Foundations.Hastad.SourceBasePhase

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceAddressDescriptors
open DFVSGames.Reduction.MachineSubstitution

theorem horner_value (coefficient rank offset : Nat) :
    MachineHorner.value rank (digits coefficient offset) 2 = coefficient * rank + offset := by
  simp [MachineHorner.value, digits, Nat.mul_comm]

def steps (coefficient rank offset : Nat) : Nat :=
  MachineHorner.steps rank (digits coefficient offset) 2 + coefficient + 2

def operandLength (rank offset : Nat) : Nat :=
  (encodeWord rank).length + (encodeWord offset).length

noncomputable def timePolynomial (coefficient : Nat) : Polynomial Nat :=
  (MachineHorner.timePolynomial 2).comp (Polynomial.X + Polynomial.C coefficient) +
    Polynomial.C (coefficient + 2)

theorem timePolynomial_eval (coefficient n : Nat) :
    (timePolynomial coefficient).eval n =
      (MachineHorner.timePolynomial 2).eval (n + coefficient) + coefficient + 2 := by
  simp [timePolynomial, Polynomial.eval_comp, Nat.add_assoc]

theorem steps_le_timePolynomial (coefficient rank offset : Nat) :
    steps coefficient rank offset ≤ (timePolynomial coefficient).eval (operandLength rank offset) := by
  have hr : rank ≤ operandLength rank offset + coefficient := by
    simp only [operandLength, encodeWord_length]
    omega
  have hd : ∀ i, i < 2 → digits coefficient offset i ≤ operandLength rank offset + coefficient := by
    intro i _
    simp only [digits, operandLength, encodeWord_length]
    split <;> omega
  have h := MachineHorner.steps_le_timePolynomial rank (digits coefficient offset) 2
    (operandLength rank offset + coefficient) hr hd
  rw [timePolynomial_eval]
  unfold steps
  omega

end DFVSGames.Foundations.Hastad.SourceBasePhase

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_ContextClear
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceContextClear

open Turing Complexity MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

theorem lengthSum_update_inline_SourceContextClear {K : Type} [DecidableEq K] (chosen : List K)
    (base : K → List Bool) (source : K) (h : source ∉ chosen) :
    MachineDrainMany.lengthSum chosen (Function.update base source []) =
      MachineDrainMany.lengthSum chosen base := by
  unfold MachineDrainMany.lengthSum
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [Function.update_of_ne (by intro he; subst k; exact h hk)]

theorem steps_eq_of_nodup_inline_SourceContextClear {K : Type} [DecidableEq K] (chosen : List K)
    (h : chosen.Nodup) (base : K → List Bool) :
    MachineDrainMany.steps chosen base =
      MachineDrainMany.lengthSum chosen base + chosen.length := by
  induction chosen generalizing base with
  | nil => rfl
  | cons source chosen ih =>
      obtain ⟨hn, hd⟩ := List.nodup_cons.mp h
      rw [MachineDrainMany.steps, ih hd, lengthSum_update_inline_SourceContextClear chosen base source hn]
      simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem variables_add_two_le_input (F : Target.Formula) :
    F.«variables» + 2 ≤ (formulaBits F).length := by
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end DFVSGames.Foundations.Hastad.SourceContextClear


namespace DFVSGames.Foundations.Hastad.SourceQueryOrder

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceAddressDescriptors SourceLoopOrder

def occurrenceBits (F : Formula) (u D : Nat) (p : SourceIndex F u D) : List Bool :=
  encodeWords (DFVSGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D p))

def slotBits (F : Formula) (u D : Nat) (c : ClauseContext F u) (s : SlotContext u) :
    List Bool :=
  (testTapeEncoding u D).enumerate.flatMap (fun t => occurrenceBits F u D ((c, s), t))

def tupleBits (F : Formula) (u D : Nat) (c : ClauseContext F u) : List Bool :=
  (slotContextEncoding u).enumerate.flatMap (slotBits F u D c)

end DFVSGames.Foundations.Hastad.SourceQueryOrder


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Parameters
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Integration.SourceParameters

theorem logTwo_sixteen : DFVSGames.Foundations.Repetition.logTwo 16 = 4 := by
  unfold DFVSGames.Foundations.Repetition.logTwo
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  simp [hlog]

end DFVSGames.Integration.SourceParameters

namespace DFVSGames.Foundations.Hastad.SourceGeneratorProgram

open Turing Complexity SourceGeneratorModel

noncomputable section

abbrev Tape (u D : Nat) := SourceGeneratorModel.Tape u D

end

end DFVSGames.Foundations.Hastad.SourceGeneratorProgram

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PortTables
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace DFVSGames.Foundations.PCP.AssignmentTester

open DFVSGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem disagree_nonneg (a b : Bool) : 0 ≤ disagree a b := by
  cases a <;> cases b <;> norm_num [disagree]

theorem disagree_eq (a b : Bool) :
    disagree a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagree, bitSign]

theorem disagree_xor_le (a b c d : Bool) :
    disagree (a ^^ b) (c ^^ d) ≤ disagree a c + disagree b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [disagree]

omit [Fintype A] [DecidableEq A] in
theorem cubeXor_comm (f g : Cube A) : cubeXor f g = cubeXor g f := by
  funext a
  simp [cubeXor, Bool.xor_comm]

theorem expect_cubeXor (F : Cube A → ℝ) (g : Cube A) :
    (𝔼 f, F (cubeXor f g)) = 𝔼 f, F f := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  congr 1
  refine Finset.sum_bij (fun f _ => cubeXor f g) ?_ ?_ ?_ ?_
  · intro f _
    exact Finset.mem_univ _
  · intro f _ h _ heq
    have hh := congrArg (fun x => cubeXor x g) heq
    simpa only [cubeXor_right_twice] using hh
  · intro f _
    exact ⟨cubeXor f g, Finset.mem_univ _, cubeXor_right_twice f g⟩
  · intro f _
    rfl

theorem distance_parity (F : Cube A → Bool) (s : Cube A) :
    distance F (parity s) = (1 - coefficient (fun f => bitSign (F f)) s) / 2 := by
  unfold distance
  simp_rw [disagree_eq, bitSign_parity, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rfl

def blrReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, disagree (F f ^^ F g) (F (cubeXor f g))

theorem blrReject_nonneg (F : Cube A → Bool) : 0 ≤ blrReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  exact disagree_nonneg _ _

theorem blr_correlation (F : Cube A → Bool) :
    (𝔼 f, 𝔼 g, bitSign (F f) * bitSign (F g) * bitSign (F (cubeXor f g))) =
      ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3 := by
  simp_rw [mul_assoc, ← Finset.mul_expect]
  conv_lhs =>
    enter [2, f, 2, 2, g, 2, 1]
    rw [cubeXor_comm]
  simp_rw [walsh_autocorrelation, Finset.mul_sum]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have heq (f : Cube A) : bitSign (F f) *
      (coefficient (fun f => bitSign (F f)) s ^ 2 * walsh s f) =
    coefficient (fun f => bitSign (F f)) s ^ 2 * (bitSign (F f) * walsh s f) := by ring
  simp_rw [heq, ← Finset.mul_expect]
  change coefficient (fun f => bitSign (F f)) s ^ 2 *
    coefficient (fun f => bitSign (F f)) s = _
  ring

theorem blrReject_fourier (F : Cube A → Bool) :
    blrReject F = (1 - ∑ s, coefficient (fun f => bitSign (F f)) s ^ 3) / 2 := by
  unfold blrReject
  simp_rw [disagree_eq, bitSign_xor, div_eq_mul_inv,
    ← Finset.expect_mul, Finset.expect_sub_distrib]
  simp only [Fintype.expect_const]
  rw [blr_correlation]

theorem blr_near_parity (F : Cube A → Bool) :
    ∃ s : Cube A, distance F (parity s) ≤ blrReject F := by
  classical
  let c := coefficient (fun f => bitSign (F f))
  have hmass : (∑ s, c s ^ 2) = 1 := sign_parseval F
  have hlarge : ∃ s, (∑ t, c t ^ 3) ≤ c s := by
    by_contra hn
    push Not at hn
    have hpos : ∃ s, 0 < c s ^ 2 := by
      by_contra hh
      push Not at hh
      have hz := Finset.sum_nonpos (s := Finset.univ) (fun s _ => hh s)
      linarith
    obtain ⟨s₀, hs₀⟩ := hpos
    have hle (s : Cube A) (_ : s ∈ Finset.univ) :
        c s ^ 3 ≤ (∑ t, c t ^ 3) * c s ^ 2 := by
      have h := mul_le_mul_of_nonneg_right (hn s).le (sq_nonneg (c s))
      nlinarith
    have hlt : c s₀ ^ 3 < (∑ t, c t ^ 3) * c s₀ ^ 2 := by
      have h := mul_lt_mul_of_pos_right (hn s₀) hs₀
      nlinarith
    have hsum := Finset.sum_lt_sum hle ⟨s₀, Finset.mem_univ _, hlt⟩
    rw [← Finset.mul_sum, hmass, mul_one] at hsum
    exact (lt_irrefl _ hsum)
  obtain ⟨s, hs⟩ := hlarge
  refine ⟨s, ?_⟩
  rw [distance_parity, blrReject_fourier]
  dsimp [c] at hs
  linarith

def selfCorrect (F : Cube A → Bool) (x r : Cube A) : Bool :=
  F r ^^ F (cubeXor r x)

theorem parity_selfCorrect (s x r : Cube A) :
    (parity s r ^^ parity s (cubeXor r x)) = parity s x := by
  rw [parity_xor]
  cases parity s r <;> cases parity s x <;> rfl

theorem selfCorrect_error (F : Cube A → Bool) (s x : Cube A) :
    (𝔼 r, disagree (selfCorrect F x r) (parity s x)) ≤ 2 * distance F (parity s) := by
  have hle (r : Cube A) :
      disagree (selfCorrect F x r) (parity s x) ≤
      disagree (F r) (parity s r) +
        disagree (F (cubeXor r x)) (parity s (cubeXor r x)) := by
    rw [← parity_selfCorrect s x r]
    exact disagree_xor_le _ _ _ _
  have h := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hle r)
  rw [Finset.expect_add_distrib,
    expect_cubeXor (fun r => disagree (F r) (parity s r)) x] at h
  change _ ≤ distance F (parity s) + distance F (parity s) at h
  linarith

theorem expect_flipAt (F : Cube A → ℝ) (i : A) :
    (𝔼 f, F (flipAt i f)) = 𝔼 f, F f := by
  simp_rw [flipAt_eq_xor]
  exact expect_cubeXor F _

def andLawFailure (s f g : Cube A) : Bool :=
  parity s (cubeAnd f g) ^^ (parity s f && parity s g)

theorem andLawFailure_flipAt_second (s : Cube A) (i : A) (f g : Cube A)
    (hi : s i = true) :
    andLawFailure s f (flipAt i g) =
      (andLawFailure s f g ^^ (parity s f ^^ f i)) := by
  have hAnd : cubeAnd f (flipAt i g) =
      (if f i then flipAt i (cubeAnd f g) else cubeAnd f g) := by
    funext a
    by_cases ha : a = i
    · subst a
      cases hfi : f i <;> simp [cubeAnd, flipAt, hfi]
    · cases hfi : f i <;> simp [cubeAnd, flipAt, ha]
  have hg := parity_flipAt s i g hi
  have hfg := parity_flipAt s i (cubeAnd f g) hi
  cases hfi : f i <;> cases hf : parity s f <;>
    cases hg₀ : parity s g <;> cases ha : parity s (cubeAnd f g) <;>
    simp [andLawFailure, hAnd, hg, hfg, hfi, hf, hg₀, ha]

theorem four_truth_lower_inline_AssignmentTester (e₀ e₁ d : Bool) :
    (1 : ℝ) ≤ truth e₀ + truth (e₀ ^^ d) + truth e₁ + truth (e₁ ^^ (!d)) := by
  cases e₀ <;> cases e₁ <;> cases d <;> norm_num [truth]

theorem parity_and_rejection (s : Cube A) (i j : A)
    (hi : s i = true) (hj : s j = true) (hij : i ≠ j) :
    (1 : ℝ) / 4 ≤ 𝔼 f, 𝔼 g, truth (andLawFailure s f g) := by
  have hpoint (f g : Cube A) : (1 : ℝ) ≤
      truth (andLawFailure s f g) + truth (andLawFailure s f (flipAt i g)) +
      truth (andLawFailure s (flipAt j f) g) +
      truth (andLawFailure s (flipAt j f) (flipAt i g)) := by
    rw [andLawFailure_flipAt_second s i f g hi,
      andLawFailure_flipAt_second s i (flipAt j f) g hi]
    have hD : (parity s (flipAt j f) ^^ (flipAt j f) i) =
        !(parity s f ^^ f i) := by
      rw [parity_flipAt s j f hj]
      simp only [flipAt, ite_eq_right hij]
      cases hf : parity s f <;> cases hfi : f i <;> simp []
    rw [hD]
    exact four_truth_lower_inline_AssignmentTester _ _ _
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hpoint f g))
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
  have hinner (f : Cube A) :
      (𝔼 g, truth (andLawFailure s f (flipAt i g))) =
        𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun g => truth (andLawFailure s f g)) i
  have houter : (𝔼 f, 𝔼 g, truth (andLawFailure s (flipAt j f) g)) =
      𝔼 f, 𝔼 g, truth (andLawFailure s f g) :=
    expect_flipAt (fun f => 𝔼 g, truth (andLawFailure s f g)) j
  simp only [hinner, houter] at havg
  linarith

theorem truth_xor (a b : Bool) : truth (a ^^ b) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

theorem disagree_triangle (a b c : Bool) :
    disagree a c ≤ disagree a b + disagree b c := by
  cases a <;> cases b <;> cases c <;> norm_num [disagree]

theorem and_disagree_transfer (p₀ p₁ p₂ q₀ q₁ q₂ : Bool) :
    disagree p₀ (p₁ && p₂) ≤ disagree q₀ (q₁ && q₂) +
      disagree q₀ p₀ + disagree q₁ p₁ + disagree q₂ p₂ := by
  cases p₀ <;> cases p₁ <;> cases p₂ <;>
    cases q₀ <;> cases q₁ <;> cases q₂ <;> norm_num [disagree]

def andReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    disagree (selfCorrect F (cubeAnd f g) r₀)
      (selfCorrect F f r₁ && selfCorrect F g r₂)

def unitReject (F : Cube A → Bool) : ℝ :=
  𝔼 r, disagree (selfCorrect F (fun _ => true) r) true

variable {K : Type*} [Fintype K] [Nonempty K]

def inputReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 k, 𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)

def testerReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  (blrReject F + andReject F + unitReject F + inputReject label σ F) / 4

theorem andReject_nonneg (F : Cube A → Bool) : 0 ≤ andReject F := by
  apply Finset.expect_nonneg
  intro f _
  apply Finset.expect_nonneg
  intro g _
  apply Finset.expect_nonneg
  intro r₀ _
  apply Finset.expect_nonneg
  intro r₁ _
  apply Finset.expect_nonneg
  intro r₂ _
  exact disagree_nonneg _ _

theorem unitReject_nonneg (F : Cube A → Bool) : 0 ≤ unitReject F := by
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

omit [Nonempty K] in
theorem inputReject_nonneg (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) :
    0 ≤ inputReject label σ F := by
  apply Finset.expect_nonneg
  intro k _
  apply Finset.expect_nonneg
  intro r _
  exact disagree_nonneg _ _

theorem andReject_transfer (F : Cube A → Bool) (s : Cube A) :
    (𝔼 f, 𝔼 g, truth (andLawFailure s f g)) ≤
      andReject F + 6 * distance F (parity s) := by
  have hlocal (f g : Cube A) : truth (andLawFailure s f g) ≤
      (𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
        disagree (selfCorrect F (cubeAnd f g) r₀)
          (selfCorrect F f r₁ && selfCorrect F g r₂)) +
      6 * distance F (parity s) := by
    have hp (r₀ r₁ r₂ : Cube A) := and_disagree_transfer
      (parity s (cubeAnd f g)) (parity s f) (parity s g)
      (selfCorrect F (cubeAnd f g) r₀) (selfCorrect F f r₁) (selfCorrect F g r₂)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r₀ _ =>
      Finset.expect_le_expect (s := Finset.univ) (fun r₁ _ =>
        Finset.expect_le_expect (s := Finset.univ) (fun r₂ _ => hp r₀ r₁ r₂)))
    simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
    have h₀ := selfCorrect_error F s (cubeAnd f g)
    have h₁ := selfCorrect_error F s f
    have h₂ := selfCorrect_error F s g
    rw [andLawFailure, truth_xor]
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun f _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun g _ => hlocal f g))
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, andReject] using h

theorem parity_zero (f : Cube A) : parity (fun _ => false) f = false := by
  apply bitSign_injective
  rw [bitSign_parity]
  simp [walsh, bitSign]

theorem unitReject_zero_parity (F : Cube A → Bool) :
    1 - 2 * distance F (parity (fun _ => false)) ≤ unitReject F := by
  have herr := selfCorrect_error F (fun _ => false) (fun _ => true)
  simp only [parity_zero] at herr
  have heq : unitReject F +
      (𝔼 r, disagree (selfCorrect F (fun _ => true) r) false) = 1 := by
    unfold unitReject
    rw [← Finset.expect_add_distrib]
    have hp (b : Bool) : disagree b true + disagree b false = 1 := by
      cases b <;> norm_num [disagree]
    simp only [hp, Fintype.expect_const]
  linarith

theorem parity_singleMask_eval (a : A) (f : Cube A) :
    parity (singleMask a) f = f a := by
  apply bitSign_injective
  rw [bitSign_parity, walsh_symm, walsh_singleMask]

theorem inputReject_transfer (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) (a : A) :
    distance σ (label a) ≤ inputReject label σ F +
      2 * distance F (parity (singleMask a)) := by
  have hlocal (k : K) : disagree (σ k) (label a k) ≤
      (𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)) +
        2 * distance F (parity (singleMask a)) := by
    have hp (r : Cube A) := disagree_triangle (σ k)
      (selfCorrect F (fun a => label a k) r) (label a k)
    have havg := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hp r)
    simp only [Fintype.expect_const, Finset.expect_add_distrib] at havg
    have herr := selfCorrect_error F (singleMask a) (fun a => label a k)
    simp only [parity_singleMask_eval] at herr
    linarith
  have h := Finset.expect_le_expect (s := Finset.univ) (fun k _ => hlocal k)
  simpa only [Finset.expect_add_distrib, Fintype.expect_const, inputReject, distance] using h

theorem tester_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ testerReject label σ F := by
  have hblr := blrReject_nonneg F
  have hand := andReject_nonneg F
  have hunit := unitReject_nonneg F
  have hin := inputReject_nonneg label σ F
  by_cases hb : δ / 64 ≤ blrReject F
  · unfold testerReject
    linarith
  obtain ⟨s, hs⟩ := blr_near_parity F
  by_cases hz : s = fun _ => false
  · subst s
    have hu := unitReject_zero_parity F
    unfold testerReject
    linarith
  have hsome : ∃ i, s i = true := by
    by_contra hh
    push Not at hh
    apply hz
    funext i
    have h := hh i
    cases hi : s i <;> simp_all
  obtain ⟨i, hi⟩ := hsome
  by_cases htwo : ∃ j, i ≠ j ∧ s j = true
  · obtain ⟨j, hij, hj⟩ := htwo
    have ha := parity_and_rejection s i j hi hj hij
    have ht := andReject_transfer F s
    unfold testerReject
    linarith
  · have heq : s = singleMask i := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [singleMask, hi]
      · have hj : s j = false := by
          cases hv : s j
          · rfl
          · exact False.elim (htwo ⟨j, Ne.symm hji, hv⟩)
        simp [singleMask, hji, hj]
    subst s
    have ht := inputReject_transfer label σ F i
    have hf := hfar i
    unfold testerReject
    linarith

def oracleAnswer (σ : K → Bool) (F : Cube A → Bool) : K ⊕ Cube A → Bool :=
  Sum.elim σ F

def eventReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) : ℝ :=
  truth (!(eventAccepts kind (fun slot =>
    oracleAnswer σ F (eventQueries label kind k f g r₀ r₁ r₂ slot))))

theorem truth_not_decide_eq (a b : Bool) : truth (!(decide (a = b))) = disagree a b := by
  cases a <;> cases b <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_blr (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 0 k f g r₀ r₁ r₂ =
      disagree (F f ^^ F g) (F (cubeXor f g)) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer, truth_not_decide_eq]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_and (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 1 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (cubeAnd f g) r₀)
        (selfCorrect F f r₁ && selfCorrect F g r₂) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_unit (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 2 k f g r₀ r₁ r₂ =
      disagree (selfCorrect F (fun _ => true) r₀) true := by
  simp only [eventReject, eventAccepts, eventQueries, oracleAnswer]
  norm_num
  change truth (!(selfCorrect F (fun _ => true) r₀)) =
    disagree (selfCorrect F (fun _ => true) r₀) true
  cases selfCorrect F (fun _ => true) r₀ <;> norm_num [truth, disagree]

omit [Fintype A] [DecidableEq A] [Fintype K] [Nonempty K] in
theorem eventReject_input (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (k : K) (f g r₀ r₁ r₂ : Cube A) :
    eventReject label σ F 3 k f g r₀ r₁ r₂ =
      disagree (σ k) (selfCorrect F (fun a => label a k) r₀) := by
  simp [eventReject, eventAccepts, eventQueries, oracleAnswer,
    truth_not_decide_eq, selfCorrect]

def explicitTesterReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 kind : Fin 4, 𝔼 k, 𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    eventReject label σ F kind k f g r₀ r₁ r₂

theorem explicitTesterReject_eq (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) : explicitTesterReject label σ F = testerReject label σ F := by
  unfold explicitTesterReject
  rw [Fintype.expect_eq_sum_div_card]
  simp [Fin.sum_univ_succ, eventReject_blr, eventReject_and, eventReject_unit,
    eventReject_input, testerReject, blrReject, andReject, unitReject, inputReject, add_assoc]

theorem explicit_proximity_soundness (label : A → K → Bool) (σ : K → Bool)
    (F : Cube A → Bool) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hfar : ∀ a, δ ≤ distance σ (label a)) :
    δ / 256 ≤ explicitTesterReject label σ F := by
  rw [explicitTesterReject_eq]
  exact tester_proximity_soundness label σ F hδ hδ' hfar

end DFVSGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PoweringTables
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace DFVSGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open DFVSGames.Foundations.Hastad

@[simp] theorem disagreement_self (a : Bool) : disagreement a a = 0 := by
  simp [disagreement]

theorem disagreement_eq_sign (a b : Bool) :
    disagreement a b = (1 - bitSign a * bitSign b) / 2 := by
  cases a <;> cases b <;> norm_num [disagreement, bitSign]

def relativeDistance {X : Type*} [Fintype X] (f g : X → Bool) : ℝ :=
  𝔼 x, disagreement (f x) (g x)

@[simp] theorem relativeDistance_self {X : Type*} [Fintype X] (f : X → Bool) :
    relativeDistance f f = 0 := by
  simp [relativeDistance]

theorem relativeDistance_eq_sign {X : Type*} [Fintype X] [Nonempty X]
    (f g : X → Bool) :
    relativeDistance f g = (1 - 𝔼 x, bitSign (f x) * bitSign (g x)) / 2 := by
  simp only [relativeDistance, disagreement_eq_sign]
  rw [← Finset.expect_div, Finset.expect_sub_distrib]
  simp

def singletonMask_inline_CodeComposition {A : Type*} [DecidableEq A] (a : A) : Cube A :=
  fun i => decide (i = a)

theorem exists_nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) :
    ∃ a : A, ∀ b : A, relativeDistance f (codeword a) ≤ relativeDistance f (codeword b) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun a : A => relativeDistance f (codeword a)) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

def nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (f : Cube A → Bool) : A :=
  Classical.choose (exists_nearest f)

end DFVSGames.Foundations.PCP.CodeComposition
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AlphabetReduction
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

namespace DFVSGames.Foundations.PCP.AlphabetReduction

open DFVSGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeTesterReject (accepts : A → A → Bool) (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool) : ℝ :=
  AssignmentTester.explicitTesterReject (pairEncoding accepts) (pairWord left right) F

end DFVSGames.Foundations.PCP.AlphabetReduction
end


noncomputable section

namespace DFVSGames.Foundations.PCP.AlphabetGraph

open DFVSGames.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeOracle (G : ConstraintGraph V E A) (assignment : Address V E A → Bool) (e : E) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) → Bool :=
  fun tape => assignment (.inr (e, extendTape G e tape))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem oracleAnswer_globalize (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E)
    (x : AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    assignment (globalizeQuery G e x) =
      AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) x := by
  rcases x with ⟨side, tape⟩ | tape
  · cases side <;> rfl
  · rfl

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem response_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    QueryIncidence.response (verifier G) assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      fun slot => AssignmentTester.oracleAnswer
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e)
        (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
          (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
          (restrictTape G e r₁) (restrictTape G e r₂) slot) := by
  funext slot
  exact oracleAnswer_globalize G assignment e _

def eventReject (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (event : Event E A) : ℝ :=
  AssignmentTester.truth (!((verifier G).accepts event (QueryIncidence.response (verifier G) assignment event)))

omit [Fintype A] [DecidableEq A] [Nonempty A] in
theorem eventReject_eq_local (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) (kind : Fin 4)
    (k : AlphabetReduction.InputCoordinate A) (f g r₀ r₁ r₂ : Cube (A × A)) :
    eventReject G assignment (e, kind, k, f, g, r₀, r₁, r₂) =
      AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
        (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
          (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind k
        (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
        (restrictTape G e r₁) (restrictTape G e r₂) := by
  unfold eventReject
  rw [response_eq_local]
  rfl

def localAverage (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (e : E) : ℝ := 𝔼 sample : LocalEvent A, eventReject G assignment (e, sample)

omit [Nonempty A] in
theorem localAverage_eq_tester (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) (e : E) :
    localAverage G assignment e = AlphabetReduction.edgeTesterReject (G.accepts e)
      (vertexBlock assignment (G.tail e)) (vertexBlock assignment (G.head e))
      (edgeOracle G assignment e) := by
  unfold localAverage AlphabetReduction.edgeTesterReject AssignmentTester.explicitTesterReject
  simp only [LocalEvent, expect_prod, eventReject_eq_local, restrictTape]
  apply Finset.expect_congr rfl
  intro kind _
  apply Finset.expect_congr rfl
  intro side _
  apply Finset.expect_congr rfl
  intro tape _
  exact expect_restrict_five (legal G e)
    (AssignmentTester.eventReject (AlphabetReduction.pairEncoding (G.accepts e))
      (CodeComposition.pairWord (vertexBlock assignment (G.tail e))
        (vertexBlock assignment (G.head e))) (edgeOracle G assignment e) kind (side, tape))

def average [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) : ℝ :=
  𝔼 event : Event E A, eventReject G assignment event

def decodedLabeling (assignment : Address V E A → Bool) : V → A :=
  fun v => CodeComposition.nearest (vertexBlock assignment v)

omit [Nonempty A] in
theorem average_eq_count [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) :
    average G assignment = (QueryIncidence.verifierRejectionCount (verifier G) assignment : ℝ) /
      Fintype.card (Event E A) :=
  expect_rejection_eq_count _

end DFVSGames.Foundations.PCP.AlphabetGraph

end


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_VerifierCNF
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.VerifierToCNF

open Target

def clauseFailures {n : Nat} (clauses : List (Clause n)) (A : Fin n → Bool) : Nat :=
  (clauses.map (fun c => c.eval A)).count false

theorem forbiddenLiteral_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) (i : Fin q) :
    (forbiddenLiteral V e p i).eval A = false ↔ A (V.query e i) = patternAt q p i := by
  cases hp : patternAt q p i <;> cases ha : A (V.query e i) <;>
    simp [forbiddenLiteral, Literal.eval, hp, ha]

theorem forbiddenClause_values {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (forbiddenClause V e p).map (fun l => l.eval B) =
      mismatchBits V (restrictAssignment V B) e p := by
  simp [forbiddenClause, mismatchBits, List.map_ofFn, Function.comp_def, liftLiteral, Literal.eval,
    restrictAssignment]

theorem mismatchBits_false {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q)
    (actual : ∀ i, A (V.query e i) = patternAt q p i) :
    (mismatchBits V A e p).any id = false := by
  apply List.any_eq_false.mpr
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  have h := (forbiddenLiteral_false V A e p i).mpr (actual i)
  simp [h]

theorem clauseFailures_append {n : Nat} (xs ys : List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs ++ ys) A = clauseFailures xs A + clauseFailures ys A := by
  simp [clauseFailures, List.map_append, List.count_append]

theorem clauseFailures_le_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) (x : α) (hx : x ∈ xs) :
    clauseFailures (f x) A ≤ clauseFailures (xs.flatMap f) A := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [List.flatMap_cons, clauseFailures_append]
      omega
    · have h := ih hx
      simp only [List.flatMap_cons, clauseFailures_append]
      omega

theorem clauseFailures_flatMap {α : Type*} {n : Nat} (xs : List α)
    (f : α → List (Clause n)) (A : Fin n → Bool) :
    clauseFailures (xs.flatMap f) A = (xs.map (fun x => clauseFailures (f x) A)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, clauseFailures_append, List.map_cons, List.sum_cons, ih]

end DFVSGames.Foundations.PCP.VerifierToCNF

end OAI
end


