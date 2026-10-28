-- Prove2me | Definitions.Def_OAIQ086U012
-- name    : OAIQ086U012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:10:00.853659+00:00
-- url     : https://prove2.me/theorems/ca8261d3-22ce-4279-a0fe-b56f924e2274
-- title:
--   Definitions bundle OAIQ086U012 of the split of OpenAI, The Unique Games Theorem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 291 declarations of OpenAI's Lean: 141 definitions, 5 inductive types or structures and 145 theorems. The definitions and types are `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup.lookupInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup.lookupWithSplitInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextClear.Label`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextClear.clearLoadedInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextClear.clearLoadedToBaseInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextClear.main`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextClear.program`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.loadInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.loadUnaryInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.lookupOutput`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.placedLookupInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.prefixInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare.loadInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare.preparationConfiguration`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare.prepareEntry`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare.prepareInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare.program`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare.signatureInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGap.ClauseGap`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGap.forError`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGap.source`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.beforeFinish`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.computableInPolyTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.enterFinishInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.forErrorComputableInPolyTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.instDecidableEqExtra`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.instDecidableEqExtra_1`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.outputInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.prefixInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.prefixPolynomial`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.startupInTime`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGenerator.timePolynomial`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorContract.NonemptyFormula`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorContract.errorMap`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorContract.inputEncoding`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorContract.sourceMap`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel.allTapes`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel.clearKeys`, `OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel.headerControl` and 106 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `UniqueGames_PCP_BinaryParityReduction`, `UniqueGames_PCP_FinalTableFormula`, `UniqueGames_PCP_LoopInitializationLemmas`, `UniqueGames_PCP_RawInitialTablesLemmas`, `UniqueGames_PCP_SourceContextClear`, `UniqueGames_PCP_SourceContextLoad`, `UniqueGames_PCP_SourceDescriptorEmissionLemmas`, `UniqueGames_PCP_SourceFieldArrayLemmas`, `UniqueGames_PCP_SourceGapLemmas`, `UniqueGames_PCP_SourceIncidence`, `UniqueGames_PCP_SourceQueryLoopLemmas`, `UniqueGames_PCP_SourceQueryOrderLemmas`, `UniqueGames_PCP_SourceSignaturePrepareLemmas`, `UniqueGames_PCP_SourceTupleBody`, `UniqueGames_PCP_SourceTupleBound`, `UniqueGames_PCP_TableGapReductionLemmas`, `UniqueGames_PCP_TableIteration`, `UniqueGames_Reduction_FromMatrixGap`.
--
--   **Imports.** It imports the published bundle `Def_UniqueGamesTheorem`; the bundles `OAIQ086U010` and `OAIQ086U011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ086U014`; the proofs of `OAI.UniqueGamesTheorem.Decoder.ActualMatrixContradiction.contradiction` and `OAI.UniqueGamesTheorem.theorem11`.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U010
import Definitions.Def_OAIQ086U011

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceFieldArrayLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition SourceMachine

/-- A complete skip-and-read phase after the non-destructive formula copy. -/
theorem scanReadTrace {n : Nat} (base : Tape → List Bool) (variableCount declaredClauses : Nat)
    (prior : List (Target.Clause n)) (clause : Target.Clause n)
    (indexSuffix suffix : List Bool) :
    (advance (TM2.step program))^[scanSteps variableCount declaredClauses prior clause]
      (some ⟨some .headerFirst, ((), none), scanTapes base prior.length indexSuffix
        (encodeWords [variableCount, declaredClauses] ++
          (encodeWords (prior.flatMap clauseWords) ++
            (encodeWords (clauseWords clause) ++ suffix)))⟩) =
      some ⟨none, ((), none), outputTapes base clause indexSuffix suffix⟩ := by
  have hh := discardHeadersTrace
    (scanTapes base prior.length indexSuffix
      (encodeWords [variableCount, declaredClauses] ++
        (encodeWords (prior.flatMap clauseWords) ++ (encodeWords (clauseWords clause) ++ suffix))))
    variableCount declaredClauses
    (encodeWords (prior.flatMap clauseWords) ++ (encodeWords (clauseWords clause) ++ suffix))
    (by simp)
  have hs := skipClausesTrace base prior indexSuffix (encodeWords (clauseWords clause) ++ suffix) none
  have hr := readSixTrace
    (scanTapes base 0 indexSuffix (encodeWords (clauseWords clause) ++ suffix))
    (clauseWords clause) (clauseWords_length clause) suffix (by simp)
  rw [show scanSteps variableCount declaredClauses prior clause =
      ((encodeWords (clauseWords clause)).length + 7 +
        ((encodeWords (prior.flatMap clauseWords)).length + prior.length + 1)) +
        (variableCount + declaredClauses + 2) by unfold scanSteps; omega]
  rw [Function.iterate_add_apply, hh, update_scanTapes_work,
    Function.iterate_add_apply, hs]
  exact hr

/-- Actual formula lookup with a displayed prefix/selected-clause/suffix split.
The formula stack is restored before scanning, and the index is consumed down
to its retained zero delimiter. Field-stack suffixes are preserved. -/
theorem lookupWithSplitTrace (F : Target.Formula) (prior : List (Target.Clause F.variables))
    (clause : Target.Clause F.variables) (after : List (Target.Clause F.variables))
    (hsplit : F.clauses = prior ++ clause :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    (advance (TM2.step program))^[lookupSteps F prior clause]
      (some ⟨some .copyOut, ((), register), base⟩) =
      some ⟨none, ((), none),
        outputTapes base clause indexSuffix (encodeWords (after.flatMap clauseWords))⟩ := by
  have hbits : formulaBits F = encodeWords [F.variables, F.clauses.length] ++
      (encodeWords (prior.flatMap clauseWords) ++
        (encodeWords (clauseWords clause) ++ encodeWords (after.flatMap clauseWords))) := by
    simp only [formulaBits, formulaWords, encodeWords_append]
    rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons, encodeWords_append]
  have hc := MachineCopy.copyTrace .formula .work .scratch (by decide) (by decide)
    (by decide) false .copyOut .copyBack (some .headerFirst) program rfl rfl
    base hscratch () register
  have htapes : Function.update base .work (base .formula ++ base .work) =
      scanTapes base prior.length indexSuffix (formulaBits F) := by
    funext p
    cases p <;> simp [scanTapes, MachineUnaryCounter.counterTapes, hformula, hindex, hwork]
  rw [htapes, hformula] at hc
  rw [lookupSteps, Nat.add_comm, Function.iterate_add_apply, hc, hbits]
  exact scanReadTrace base F.variables F.clauses.length prior clause indexSuffix
    (encodeWords (after.flatMap clauseWords))

/-- The preserved input copy is exactly the original serialized formula. -/
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

/-- A polynomial bound on the actual complete copy/skip/read execution. -/
def lookupWithSplitInTime (F : Target.Formula) (prior : List (Target.Clause F.variables))
    (clause : Target.Clause F.variables) (after : List (Target.Clause F.variables))
    (hsplit : F.clauses = prior ++ clause :: after)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord prior.length ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none),
        outputTapes base clause indexSuffix (encodeWords (after.flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) where
  steps := lookupSteps F prior clause
  evals_in_steps := lookupWithSplitTrace F prior clause after hsplit base indexSuffix
    hformula hindex hwork hscratch register
  steps_le_m := by
    rw [timePolynomial_eval]
    exact lookupSteps_le_input F prior clause after hsplit

/-- Lookup at a valid numbered clause, starting with its ordinary unary index.
The output fields are those of `F.clauses[i]`, with the rest of the work copy
and the original formula retained exactly as stated by the frame lemmas. -/
def lookupInTime (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape → List Bool) (indexSuffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord i.val ++ indexSuffix)
    (hwork : base .work = []) (hscratch : base .scratch = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, ((), register), base⟩
      (some ⟨none, ((), none), outputTapes base F.clauses[i.val] indexSuffix
        (encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords))⟩)
      (timePolynomial.eval (formulaBits F).length) := by
  have hp : (F.clauses.take i.val).length = i.val := by
    rw [List.length_take, Nat.min_eq_left i.isLt.le]
  have hs : F.clauses = F.clauses.take i.val ++ F.clauses[i.val] :: F.clauses.drop (i.val + 1) := by
    rw [List.getElem_cons_drop i.isLt, List.take_append_drop]
  apply lookupWithSplitInTime F (F.clauses.take i.val) F.clauses[i.val]
    (F.clauses.drop (i.val + 1)) hs base indexSuffix hformula
    (by simpa only [hp] using hindex) hwork hscratch register

end UniqueGamesTheorem.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextLoad
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! A shared-arena context loader. Its finite program copies each selected
clause index, executes the checked lookup, and clears consumed scratch tapes.
Tuple digits and arbitrary extra tapes are protected throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def lookupOutput (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool) : Tape u Extra → List Bool :=
  fill j base (SourceClauseLookup.outputTapes (base ∘ place j) F.clauses[i.val] suffix
    (encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords)))

noncomputable def placedLookupInTime (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hindex : base .index = encodeWord i.val ++ suffix)
    (hwork : base .work = []) (hscratch : base .scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.lookup j .copyOut), ((), register), base⟩
      (some ⟨some (.clearWork j), ((), none), lookupOutput j F i base suffix⟩)
      (4 * (formulaBits F).length + 10) := by
  have h := SourceClauseLookup.lookupInTime F i (base ∘ place j) suffix
    hformula hindex hwork hscratch register
  have lifted := liftExecutionInTime (TM2.step SourceClauseLookup.program) (TM2.step program)
    (placedConfiguration j base) (placed_step j base) h
  simpa only [placedConfiguration, placedLabel, fill_self,
    SourceClauseLookup.timePolynomial_eval, lookupOutput] using lifted

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

noncomputable def coordinateInTime (j : Fin u) (F : Target.Formula) (i : Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : base (.current j) = encodeWord i.val ++ suffix)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.copyOut j), ((), register), base⟩
      (some ⟨some (nextLabel j), ((), none), coordinateOutput j F.clauses[i.val] base⟩)
      (6 * (formulaBits F).length + 4 * (base (.current j)).length + 20) := by
  let copied := copiedTapes j base
  let loaded := lookupOutput j F i copied suffix
  have copyRun := MachineCopy.copyInTime (.current j) .index .copyScratch
    (by simp) (by simp) (by simp) false (.copyOut j) (.copyBack j)
    (some (.lookup j .copyOut)) program rfl rfl base hcopy () register
  have copied_eq : Function.update base .index (base (.current j) ++ base .index) = copied := by
    simp [copied, copiedTapes, hindex]
  rw [copied_eq] at copyRun
  have lookupRun := placedLookupInTime j F i copied suffix
    (by simpa [copied, copiedTapes] using hformula)
    (by simpa [copied, copiedTapes] using hcurrent)
    (by simpa [copied, copiedTapes] using hwork)
    (by simpa [copied, copiedTapes] using hscratch) none
  have workRun := MachineDrain.drainInTime .work (.clearWork j) (some (.clearIndex j))
    program rfl loaded () none
  have indexRun := MachineDrain.drainInTime .index (.clearIndex j) (some (nextLabel j))
    program rfl (Function.update loaded .work []) () none
  have hrun := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copyRun lookupRun)
      workRun) indexRun
  have hw : loaded .work = encodeWords ((F.clauses.drop (i.val + 1)).flatMap clauseWords) := by
    simp [loaded, lookupOutput, fill, SourceClauseLookup.output_work]
  have hi : (Function.update loaded .work []) .index = encodeWord 0 ++ suffix := by
    simp [loaded, lookupOutput, fill, SourceClauseLookup.output_index]
  have hc : suffix.length ≤ (base (.current j)).length := by
    rw [hcurrent, List.length_append]
    omega
  refine { steps := hrun.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [loaded, copied, cleanup_lookupOutput] using hrun.evals_in_steps
  · apply Nat.le_trans hrun.steps_le_m
    rw [hw, hi, List.length_append, encodeWord_length]
    have hs := suffix_length_le_input F (i.val + 1)
    omega

noncomputable def prefixInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : Fin u → List Bool) (C : Nat)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.current j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (r : Nat) (hr : r ≤ u) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨some (labelAt r), ((), none), stageTapes F tuple base r⟩)
      (r * (6 * (formulaBits F).length + 4 * C + 20)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < u := by omega
    let j : Fin u := ⟨r, hru⟩
    let before := stageTapes F tuple base r
    have hf (p : Tape u Extra) (hi : p ≠ .index) (hw : p ≠ .work)
        (hh : ∀ j s, p ≠ .field j s) : before p = base p :=
      stageTapes_frame F tuple base r p hi hw hh
    have hd := stageTapes_clean F tuple base r hindex hwork
    have hc : before (.current j) = base (.current j) := hf _ (by simp) (by simp) (by simp)
    have one := coordinateInTime j F (tuple j) before (suffix j)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hformula)
      (by rw [hc]; exact hcurrent j) hd.1 hd.2
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hscratch)
      (by rw [hf _ (by simp) (by simp) (by simp)]; exact hcopy) none
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((), none), stageTapes F tuple base (r + 1)⟩)
        (6 * (formulaBits F).length + 4 * C + 20) := by
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

noncomputable def loadInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (suffix : Fin u → List Bool) (C : Nat)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (tuple j).val ++ suffix j)
    (hsize : ∀ j, (base (.current j)).length ≤ C)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes F tuple base u⟩)
      (u * (6 * (formulaBits F).length + 4 * C + 20) + 1) := by
  have prefixRun := prefixInTime F tuple base suffix C hformula hcurrent hsize
    hindex hwork hscratch hcopy u (Nat.le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt u), ((), none), stageTapes F tuple base u⟩
      (some ⟨none, ((), none), stageTapes F tuple base u⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt u), ((), none), stageTapes F tuple base u⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ prefixRun doneRun

/-- Actual odometer digits have empty suffixes. The resulting complete loader
runs in a polynomial whose coefficients depend only on the fixed repetition u. -/
noncomputable def loadUnaryInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (tuple j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes F tuple base u⟩)
      (u * (10 * (formulaBits F).length + 20) + 1) := by
  have run := loadInTime F tuple base (fun _ => []) (formulaBits F).length hformula
    (by simpa only [List.append_nil] using hcurrent)
    (by
      intro j
      rw [hcurrent j, encodeWord_length]
      have h := (tuple j).isLt
      have hm := clauses_length_le_input F
      omega)
    hindex hwork hscratch hcopy
  have he : 6 * (formulaBits F).length + 4 * (formulaBits F).length + 20 =
      10 * (formulaBits F).length + 20 := by omega
  simpa only [he] using run

end UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceDescriptorEmissionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Emit one fixed descriptor equation from three preserved unary base registers.
The output order is first address, second address, third address, RHS. The actual
stack program emits those fields in reverse order. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

theorem computed_profile_eq (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    reindexProfile u (MachineFieldProfile.equalityProfile (nameWords F c)) =
      contextNameProfile F c := by
  funext p q
  unfold reindexProfile nameWords
  rw [MachineFieldProfile.equalityProfile_encodeWord]
  simp only [names, Equiv.symm_apply_apply, contextNameProfile, Fin.ext_iff]

theorem prepared_signature_eq (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) :
    (⟨fun p => positiveAt (PCP.clauseAt F (c p.1)) p.2,
      reindexProfile u (MachineFieldProfile.equalityProfile (nameWords F c)), s⟩ :
        Signature u) = ofContext F c s := by
  rw [computed_profile_eq]
  rfl

/-- Every isolated unary variable-name field is bounded by the true CNF
input encoding, including formulas with unused declared variable names. -/
theorem nameWords_length_le_input (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (i : Fin (positionEncoding u).size) :
    (nameWords F c i).length ≤ (formulaBits F).length := by
  rw [nameWords, encodeWord_length]
  exact (Nat.succ_le_of_lt
    (occurrenceName F c ((positionEncoding u).code.symm i)).isLt).trans
      (SourceBounds.formulaBits_length_ge_variables F)

end UniqueGamesTheorem.Foundations.Hastad.SourceProfileBridge

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceSignaturePrepareLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open UniqueGamesTheorem.Foundations.Complexity

variable {u : ℕ} {Extra τ : Type}

variable [DecidableEq Extra]

def placedLabel : Option (ProfileLabel u) → Option (Label u)
  | none => some .commit
  | some l => some (.profile l)

def placedConfiguration (base : Arena u Extra → List Bool) (metadata : Signature u × τ)
    (c : TM2.Cfg (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u)) :
    TM2.Cfg (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  ⟨placedLabel c.l, (c.var, metadata), fill base c.stk⟩

def placedStatement :
    TM2.Stmt (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u) →
    TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ)
  | .push k f next => .push (place k) (fun state => f state.1) (placedStatement next)
  | .peek k f next => .peek (place k) (fun state bit => (f state.1 bit, state.2))
      (placedStatement next)
  | .pop k f next => .pop (place k) (fun state bit => (f state.1 bit, state.2))
      (placedStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (placedStatement next)
  | .branch f yes no => .branch (fun state => f state.1)
      (placedStatement yes) (placedStatement no)
  | .goto f => .goto (fun state => .profile (f state.1))
  | .halt => .goto (fun _ => .commit)

theorem placed_stepAux (base : Arena u Extra → List Bool) (metadata : Signature u × τ)
    (q : TM2.Stmt (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u))
    (state : ProfileState u) (localTapes : MachineFieldProfile.Tape (Width u) → List Bool) :
    TM2.stepAux (placedStatement q) (state, metadata) (fill base localTapes) =
      placedConfiguration base metadata (TM2.stepAux q state localTapes) := by
  induction q generalizing state localTapes with
  | push k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih state _
  | peek k f next ih =>
    simpa only [placedStatement, TM2.stepAux, fill_place] using
      ih (f state (localTapes k).head?) localTapes
  | pop k f next ih =>
    simp only [placedStatement, TM2.stepAux, fill_place]
    rw [← fill_update]
    exact ih (f state (localTapes k).head?) _
  | load f next ih =>
    simpa only [placedStatement, TM2.stepAux] using ih (f state) localTapes
  | branch f yes no ihYes ihNo =>
    cases h : f state
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state localTapes
    · simpa only [placedStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state localTapes
  | goto f => rfl
  | halt => rfl

def commitStatement : TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  .load (fun state =>
    (state.1, ({state.2.1 with sameName := reindexProfile u state.1.1}, state.2.2)))
    (MachineControl.statement id (signStateEquiv u τ)
      (SourceSignLoad.statement polarityField none))

def program : Label u → TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ)
  | .profile label => placedStatement
      (MachineFieldProfile.profileProgram (MachineFieldProfile.allPairs (Width u)) label)
  | .commit => commitStatement

theorem placed_step (base : Arena u Extra → List Bool) (metadata : Signature u × τ)
    (a b : TM2.Cfg (fun _ : MachineFieldProfile.Tape (Width u) => Bool)
      (ProfileLabel u) (ProfileState u))
    (h : (MachineFieldProfile.profileMachine (Width u)).step a = some b) :
    TM2.step program (placedConfiguration base metadata a) =
      some (placedConfiguration base metadata b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some label =>
    change some (TM2.stepAux
      (MachineFieldProfile.profileProgram (MachineFieldProfile.allPairs (Width u)) label)
      state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux (placedStatement _) (state, metadata) (fill base tapes)) = _
    rw [placed_stepAux]

theorem stepAux_commit (work : ProfileState u) (initial : Signature u) (ambient : τ)
    (tapes : Arena u Extra → List Bool) :
    TM2.stepAux commitStatement (work, (initial, ambient)) tapes =
      ⟨none, (work, (⟨SourceSignLoad.readSigns polarityField tapes,
        reindexProfile u work.1, initial.selected⟩, ambient)), tapes⟩ := by
  change TM2.stepAux (MachineControl.statement id (signStateEquiv u τ)
    (SourceSignLoad.statement polarityField none))
      ((signStateEquiv u τ)
        ({initial with sameName := reindexProfile u work.1}, (work, ambient))) tapes = _
  rw [MachineControl.stepAux_simulation, SourceSignLoad.stepAux_statement]
  rfl

/-- The actual profile execution, placed in the loaded context arena. -/
def profileInTime (tapes : Arena u Extra → List Bool)
    (hwork : ∀ w : Fin 3, tapes (place (.inr w)) = [])
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (ambient : τ) (L : ℕ)
    (hL : ∀ i, (tapes (place (.inl i))).length ≤ L) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)),
        (MachineFieldProfile.normalState initialProfile, (initial, ambient)), tapes⟩
      (some ⟨some .commit,
        (MachineFieldProfile.normalState
          (MachineFieldProfile.equalityProfile (fun i => tapes (place (.inl i)))),
          (initial, ambient)), tapes⟩)
      (Width u * Width u * (5 * L + 6) + 1) := by
  let run := MachineFieldProfile.profileInTime_bounded (Width u) (tapes ∘ place)
    hwork initialProfile L hL
  have lifted := MachineComposition.liftExecutionInTime _ _
    (placedConfiguration tapes (initial, ambient))
    (placed_step tapes (initial, ambient)) run
  simpa only [placedConfiguration, placedLabel, fill_self, Function.comp_apply] using lifted

def commitInTime (work : ProfileState u) (initial : Signature u) (ambient : τ)
    (tapes : Arena u Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .commit, (work, (initial, ambient)), tapes⟩
      (some ⟨none, (work, (⟨SourceSignLoad.readSigns polarityField tapes,
        reindexProfile u work.1, initial.selected⟩, ambient)), tapes⟩) 1 where
  steps := 1
  evals_in_steps := by
    change TM2.step program ⟨some .commit, (work, (initial, ambient)), tapes⟩ = _
    change some (TM2.stepAux commitStatement (work, (initial, ambient)) tapes) = _
    rw [stepAux_commit]
  steps_le_m := Nat.le_refl _

/-- Actual preparation from isolated name fields and unary sign fields. The
conclusion preserves every tape and arbitrary caller metadata. -/
def prepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (tapes : Arena u Extra → List Bool)
    (hwork : ∀ w : Fin 3, tapes (place (.inr w)) = [])
    (hnames : ∀ i, tapes (place (.inl i)) = nameWords F c i)
    (suffix : Position u → List Bool)
    (hsigns : ∀ p, tapes (polarityField p) =
      encodeWord (if positiveAt (clauseAt F (c p.1)) p.2 then 1 else 0) ++ suffix p)
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)),
        (MachineFieldProfile.normalState initialProfile, (initial, ambient)), tapes⟩
      (some ⟨none,
        (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
          (ofContext F c selected, ambient)), tapes⟩)
      (Width u * Width u * (5 * (formulaBits F).length + 6) + 2) := by
  have hfields : (fun i => tapes (place (.inl i))) = nameWords F c := funext hnames
  have hsign : SourceSignLoad.readSigns polarityField tapes =
      fun p => positiveAt (clauseAt F (c p.1)) p.2 :=
    SourceSignLoad.readSigns_of_unary polarityField tapes _ suffix hsigns
  have hL : ∀ i, (tapes (place (.inl i))).length ≤ (formulaBits F).length := by
    intro i
    rw [hnames]
    exact nameWords_length_le_input F c i
  have first := profileInTime tapes hwork initialProfile initial ambient
    (formulaBits F).length hL
  rw [hfields] at first
  have last := commitInTime
    (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)))
    initial ambient tapes
  dsimp only [MachineFieldProfile.normalState] at last
  rw [hsign, hselected, prepared_signature_eq F c selected] at last
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  omega

omit [DecidableEq Extra] in

theorem loaded_name_field (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool)
    (hbase : ∀ p : Position u, base (variableField p) = [])
    (i : Fin (Width u)) :
    SourceContextLoad.stageTapes F c base u (place (.inl i)) = nameWords F c i := by
  obtain ⟨p, rfl⟩ := (positionEncoding u).code.surjective i
  simp only [place, Equiv.symm_apply_apply]
  have ho := SourceContextLoad.output_variable F c base p.1 (slotEncoding.code p.2)
  change SourceContextLoad.stageTapes F c base u (variableField p) =
    encodeWord (F.clauses[(c p.1).val][(slotEncoding.code p.2).val].variableIndex.val) ++
      base (variableField p) at ho
  rw [ho, hbase p, List.append_nil]
  simp only [nameWords, names, Equiv.symm_apply_apply]
  rcases p with ⟨t, s⟩
  cases s <;> rfl

/-- Exactly the loaded context signature is computed by the concrete finite
program. Scratch is reset and all loaded fields and caller tapes are preserved. -/
def loadedPrepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hindex : base .index = []) (hwork : base .work = []) (hscratch : base .scratch = [])
    (hbase : ∀ p : Position u, base (variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.profile (MachineFieldProfile.labelAt (MachineFieldProfile.allPairs (Width u)) 0 0)),
        (MachineFieldProfile.normalState initialProfile, (initial, ambient)),
        SourceContextLoad.stageTapes F c base u⟩
      (some ⟨none,
        (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
          (ofContext F c selected, ambient)), SourceContextLoad.stageTapes F c base u⟩)
      (Width u * Width u * (5 * (formulaBits F).length + 6) + 2) := by
  apply prepareInTime F c selected (SourceContextLoad.stageTapes F c base u) _
    (loaded_name_field F c base hbase) (fun p => base (polarityField p))
    (loaded_sign_field F c base) initialProfile initial hselected ambient
  intro w
  have hc := SourceContextLoad.stageTapes_clean F c base u hindex hwork
  have hs : SourceContextLoad.stageTapes F c base u .scratch = [] := by
    rw [SourceContextLoad.stageTapes_frame F c base u .scratch
      (by simp) (by simp) (by intros; simp)]
    exact hscratch
  obtain ⟨w, hw⟩ := w
  have h : w = 0 ∨ w = 1 ∨ w = 2 := by omega
  rcases h with rfl | rfl | rfl
  · exact hc.1
  · exact hc.2
  · exact hs

end UniqueGamesTheorem.Foundations.Hastad.SourceSignaturePrepare

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

open Turing UniqueGamesTheorem.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

variable {u : Nat} {Extra τ : Type}

def prepareEntry (u : Nat) : SourceSignaturePrepare.Label u :=
  .profile (MachineFieldProfile.labelAt
    (MachineFieldProfile.allPairs (SourceSignaturePrepare.Width u)) 0 0)

def program : Label u → TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ)
  | .inl l => MachineStateFrame.statement Sum.inl (some (.inr (prepareEntry u)))
      (SourceContextLoad.program l)
  | .inr l => MachineControl.statement id (stateSwap u τ)
      (MachineStateFrame.statement Sum.inr none (SourceSignaturePrepare.program l))

def preparationConfiguration (loaderState : LoadState)
    (c : TM2.Cfg (fun _ : Arena u Extra => Bool) (SourceSignaturePrepare.Label u) (PrepareState u τ)) :
    TM2.Cfg (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  MachineControl.configuration id (stateSwap u τ)
    (MachineStateFrame.configuration Sum.inr none loaderState c)

variable [DecidableEq Extra]

theorem preparation_step (loaderState : LoadState)
    (a b : TM2.Cfg (fun _ : Arena u Extra => Bool)
      (SourceSignaturePrepare.Label u) (PrepareState u τ))
    (h : TM2.step SourceSignaturePrepare.program a = some b) :
    TM2.step program (preparationConfiguration loaderState a) =
      some (preparationConfiguration loaderState b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (SourceSignaturePrepare.program l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux
      (MachineControl.statement id (stateSwap u τ)
        (MachineStateFrame.statement Sum.inr none (SourceSignaturePrepare.program l)))
      ((stateSwap u τ) (state, loaderState)) tapes) = _
    rw [MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
    rfl

noncomputable def loadInTime (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl (SourceContextLoad.labelAt 0)), initialState initialProfile initial ambient, base⟩
      (some ⟨some (.inr (prepareEntry u)), initialState initialProfile initial ambient,
        SourceContextLoad.stageTapes F c base u⟩)
      (u * (10 * (formulaBits F).length + 20) + 1) := by
  have run := SourceContextLoad.loadUnaryInTime F c base hformula hcurrent
    hindex hwork hscratch hcopy
  have lifted := MachineStateFrame.execution Sum.inl (some (.inr (prepareEntry u)))
    (MachineFieldProfile.normalState initialProfile, (initial, ambient))
    SourceContextLoad.program program (fun _ => rfl) run
  simpa only [MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, initialState] using lifted

def signatureInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hindex : base .index = []) (hwork : base .work = []) (hscratch : base .scratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr (prepareEntry u)), initialState initialProfile initial ambient,
        SourceContextLoad.stageTapes F c base u⟩
      (some ⟨none, finalState F c selected ambient, SourceContextLoad.stageTapes F c base u⟩)
      (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
        (5 * (formulaBits F).length + 6) + 2) := by
  have run := SourceSignaturePrepare.loadedPrepareInTime F c selected base
    hindex hwork hscratch hfields initialProfile initial hselected ambient
  have lifted := MachineComposition.liftExecutionInTime
    (TM2.step SourceSignaturePrepare.program) (TM2.step program)
    (preparationConfiguration ((), none)) (preparation_step ((), none)) run
  simpa only [preparationConfiguration, MachineControl.configuration, MachineStateFrame.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.configuration,
    MachineSubroutine.label, Option.map_some, Option.map_none, id_eq, stateSwap,
    Equiv.prodComm_apply, Prod.swap, initialState, finalState, prepareEntry] using lifted

noncomputable def prepareInTime (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = [])
    (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (hselected : initial.selected = selected) (ambient : τ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl (SourceContextLoad.labelAt 0)), initialState initialProfile initial ambient, base⟩
      (some ⟨none, finalState F c selected ambient, SourceContextLoad.stageTapes F c base u⟩)
      ((u * (10 * (formulaBits F).length + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
          (5 * (formulaBits F).length + 6) + 2)) := by
  have firstRun := loadInTime F c base hformula hcurrent hindex hwork hscratch hcopy
    initialProfile initial ambient
  have secondRun := signatureInTime F c selected base hindex hwork hscratch hfields
    initialProfile initial hselected ambient
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ firstRun secondRun

end UniqueGamesTheorem.Foundations.Hastad.SourceContextPrepare

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit SourceTestEmit

variable {K Λ : Type} [DecidableEq K]

def statement (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ) :
    Label u D → TM2.Stmt (fun _ : K => Bool) Λ (State u D)
  | .test (.inl _) => .goto (fun state => bodyLabel u D labels state.1 .seed)
  | .test (.inr (state, label)) =>
      SourceEquationEmit.statement layout.sources layout.temporary layout.scratch
        (localEquation u D state) (bodyLabel u D labels state) (some (labels .append)) label
  | .append => Reduction.MachineTransfer.loopAt layout.temporary layout.accumulator id false
      (labels .append) exit

/-- Placement-aware finite selection plus actual equation emission. -/
theorem emitTrace (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[
      SourceEquationEmit.steps values (localEquation u D state) + 1]
      (some ⟨some (labels (.test (.inl ()))), (state, register), base⟩) =
      some ⟨some (labels .append), (state, none),
        prefixTapes layout.temporary base (words values (localEquation u D state))⟩ := by
  have select : TM2.step p
      ⟨some (labels (.test (.inl ()))), (state, register), base⟩ =
      some ⟨some (bodyLabel u D labels state .seed), (state, register), base⟩ := by
    change some (TM2.stepAux (p (labels (.test (.inl ())))) (state, register) base) = _
    rw [atLabels]
    rfl
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[
    SourceEquationEmit.steps values (localEquation u D state)]
      (TM2.step p ⟨some (labels (.test (.inl ()))), (state, register), base⟩) = _
  rw [select]
  exact SourceEquationEmit.equationTrace layout.sources layout.temporary layout.scratch
    layout.sourceTemporary layout.sourceScratch layout.temporaryScratch (localEquation u D state)
    (bodyLabel u D labels state) (some (labels .append)) p
    (fun label => atLabels (.test (SourceTestEmit.bodyLabel u D state label)))
    base values sourceWords scratchEmpty state register

/-- Exact one-record append trace in an arbitrary caller program. -/
theorem appendTrace (u D : Nat) (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (state : LocalInput u D) (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps u D values state]
      (some ⟨some (labels (.test (.inl ()))), (state, register), base⟩) =
      some ⟨exit, (state, none), resultTapes layout base (equationBits u D values state)⟩ := by
  let emitted := prefixTapes layout.temporary base (words values (localEquation u D state))
  have hemit := emitTrace u D layout labels exit p atLabels state base values sourceWords
    scratchEmpty register
  have htemp : emitted layout.temporary = equationBits u D values state := by
    simp [emitted, prefixTapes, equationBits, temporaryEmpty]
  have hacc : emitted layout.accumulator = base layout.accumulator :=
    prefixTapes_other _ _ _ _ (Ne.symm layout.temporaryAccumulator)
  have hfinal : Reduction.MachineTransfer.tapesAt layout.temporary layout.accumulator emitted []
      ((equationBits u D values state).reverse ++ base layout.accumulator) =
      resultTapes layout base (equationBits u D values state) := by
    funext k
    by_cases hka : k = layout.accumulator
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, resultTapes]
    · by_cases hkt : k = layout.temporary
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, resultTapes, layout.temporaryAccumulator,
          temporaryEmpty]
      · simp [Reduction.MachineTransfer.tapesAt, resultTapes, emitted, prefixTapes, hka, hkt]
  have transferred := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := LocalInput u D)
    layout.temporary layout.accumulator layout.temporaryAccumulator id false (labels .append)
    exit p (by simpa only [statement] using atLabels .append) emitted state none
  change (MachineComposition.advance (TM2.step p))^[(emitted layout.temporary).length + 1]
    (some ⟨some (labels .append), (state, none), emitted⟩) = _ at transferred
  rw [htemp, hacc] at transferred
  simp only [List.map_id] at transferred
  rw [hfinal] at transferred
  rw [show steps u D values state = ((equationBits u D values state).length + 1) +
      (SourceEquationEmit.steps values (localEquation u D state) + 1) by unfold steps; omega,
    Function.iterate_add_apply, hemit]
  exact transferred

def sourceAppendInTime (F : Formula) (u D : Nat) (occurrence : SourceIndex F u D)
    (layout : Layout K) (labels : Label u D → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ label, p (labels label) = statement u D layout labels exit label)
    (base : K → List Bool)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord
      (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2) side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.test (.inl ()))),
        ((ofContext F occurrence.1.1 occurrence.1.2, occurrence.2), register), base⟩
      (some ⟨exit, ((ofContext F occurrence.1.1 occurrence.1.2, occurrence.2), none),
        resultTapes layout base (encodeWords
          (UniqueGamesTheorem.Reduction.SourceEncoding.equationWords (sourceEquation F u D occurrence)))⟩)
      (9 * nBits F u + 20) where
  steps := steps u D
    (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2))
    (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2)
  evals_in_steps := by
    rw [sourceEquation_words]
    exact appendTrace u D layout labels exit p atLabels
      (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2) base
      (baseValue F u occurrence.1.1 (sampledVariables F occurrence.1.1 occurrence.1.2))
      sourceWords scratchEmpty temporaryEmpty register
  steps_le_m := by
    have he := equation_emit_steps_le F u occurrence.1.1
      (sampledVariables F occurrence.1.1 occurrence.1.2)
      (localEquation u D (ofContext F occurrence.1.1 occurrence.1.2, occurrence.2))
    have hl := UniqueGamesTheorem.Reduction.SourceEncoding.equationBits_length_le
      (sourceEquation F u D occurrence)
    rw [sourceEquation_words] at hl
    unfold steps SourceEquationEmit.steps equationBits
    dsimp only [localEquation] at he hl ⊢
    omega

end UniqueGamesTheorem.Foundations.Hastad.SourceTestAppend

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryLoopLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual fixed finite traversal of all query/noise tapes. The finite
control contains one branch for each prescribed tape. The input-dependent
signature and the three address bases remain in registers throughout. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

variable {K Λ : Type} [DecidableEq K]

def finish (u D : Nat) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State u D) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def statement (u D n : Nat) (queries : Nat → Query u D)
    (layout : SourceTestAppend.Layout K) (labels : Label u D n → Λ) (exit : Option Λ) :
    Label u D n → TM2.Stmt (fun _ : K => Bool) Λ (State u D)
  | .load index =>
    if h : index.val < n then
      .load (fun state => ((state.1.1, queries index.val), none))
        (.goto fun _ => labels (.emit ⟨index.val, h⟩ (.test (.inl ()))))
    else finish u D exit
  | .emit index label =>
    SourceTestAppend.statement u D layout (fun l => labels (.emit index l))
      (some (labels (.load ⟨index.val + 1, by omega⟩))) label

theorem prefixTrace (u D n : Nat) (queries : Nat → Query u D)
    (layout : SourceTestAppend.Layout K) (labels : Label u D n → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ l, p (labels l) = statement u D n queries layout labels exit l)
    (signature : Signature u) (initialQuery : Query u D)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (r : Nat) (hr : r ≤ n) :
    ∃ lastQuery : Query u D,
      (MachineComposition.advance (TM2.step p))^[prefixSteps u D queries values signature r]
        (some ⟨some (labels (.load ⟨0, by omega⟩)), ((signature, initialQuery), none), base⟩) =
        some ⟨some (labels (.load ⟨r, by omega⟩)), ((signature, lastQuery), none),
          SourceTestAppend.resultTapes layout base (prefixBits u D queries values signature r)⟩ := by
  induction r with
  | zero =>
    refine ⟨initialQuery, ?_⟩
    simp [prefixSteps, prefixBits, SourceTestAppend.resultTapes]
  | succ r ih =>
    obtain ⟨lastQuery, hprevious⟩ := ih (by omega)
    have hlt : r < n := by omega
    let current := SourceTestAppend.resultTapes layout base
      (prefixBits u D queries values signature r)
    have hselect : TM2.step p
        ⟨some (labels (.load ⟨r, by omega⟩)), ((signature, lastQuery), none), current⟩ =
        some ⟨some (labels (.emit ⟨r, hlt⟩ (.test (.inl ())))),
          ((signature, queries r), none), current⟩ := by
      change some (TM2.stepAux (p (labels (.load ⟨r, by omega⟩))) _ _) = _
      rw [atLabels]
      simp only [statement, hlt, ↓reduceDIte, TM2.stepAux]
    have hbody := SourceTestAppend.appendTrace u D layout
      (fun l => labels (.emit ⟨r, hlt⟩ l))
      (some (labels (.load ⟨r + 1, by omega⟩))) p
      (fun l => atLabels (.emit ⟨r, hlt⟩ l)) (signature, queries r) current values
      (fun side => (SourceTestAppend.resultTapes_source layout base _ side).trans
        (sourceWords side))
      ((SourceTestAppend.resultTapes_scratch layout base _).trans scratchEmpty)
      ((SourceTestAppend.resultTapes_temporary layout base _).trans temporaryEmpty) none
    refine ⟨queries r, ?_⟩
    rw [show prefixSteps u D queries values signature (r + 1) =
      (SourceTestAppend.steps u D values (signature, queries r) + 1) +
        prefixSteps u D queries values signature r by rw [prefixSteps]; omega,
      Function.iterate_add_apply, hprevious, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step p))^[
      SourceTestAppend.steps u D values (signature, queries r)]
      (TM2.step p ⟨some (labels (.load ⟨r, by omega⟩)),
        ((signature, lastQuery), none), current⟩) = _
    rw [hselect, hbody]
    rw [show current = SourceTestAppend.resultTapes layout base
      (prefixBits u D queries values signature r) from rfl, resultTapes_append]
    rfl

/-- The complete finite traversal, including its final exit transition. -/
theorem loopInTime (u D n B : Nat) (queries : Nat → Query u D)
    (layout : SourceTestAppend.Layout K) (labels : Label u D n → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State u D))
    (atLabels : ∀ l, p (labels l) = statement u D n queries layout labels exit l)
    (signature : Signature u) (initialQuery : Query u D)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (layout.sources side) = encodeWord (values side))
    (scratchEmpty : base layout.scratch = []) (temporaryEmpty : base layout.temporary = [])
    (hbound : ∀ i, i < n → SourceTestAppend.steps u D values (signature, queries i) ≤ B) :
    ∃ lastQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step p)
        ⟨some (labels (.load ⟨0, by omega⟩)), ((signature, initialQuery), none), base⟩
        (some ⟨exit, ((signature, lastQuery), none),
          SourceTestAppend.resultTapes layout base (prefixBits u D queries values signature n)⟩)
        (n * (B + 1) + 1)) := by
  obtain ⟨lastQuery, hprefix⟩ := prefixTrace u D n queries layout labels exit p atLabels
    signature initialQuery base values sourceWords scratchEmpty temporaryEmpty n (Nat.le_refl n)
  refine ⟨lastQuery, ⟨{
    steps := prefixSteps u D queries values signature n + 1
    evals_in_steps := ?_
    steps_le_m := ?_ }⟩⟩
  · change (MachineComposition.advance (TM2.step p))^[
      prefixSteps u D queries values signature n + 1] _ = _
    rw [Function.iterate_succ_apply', hprefix]
    rw [MachineComposition.advance_some]
    change some (TM2.stepAux (p (labels (.load ⟨n, by omega⟩))) _ _) = _
    rw [atLabels]
    simp only [statement, Nat.lt_irrefl, ↓reduceDIte]
    cases exit <;> rfl
  · exact Nat.add_le_add_right (prefixSteps_le u D n B queries values signature hbound) 1

end UniqueGamesTheorem.Foundations.Hastad.SourceQueryLoop

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceContextClear
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

open Turing Complexity MachineComposition

variable {u : Nat} {Extra : Type}

theorem fieldAt_injective : Function.Injective (fieldAt (u := u) (Extra := Extra)) := by
  intro i j h
  have hpair := SourceContextLoad.Tape.field.inj h
  have hp : finProdFinEquiv.symm i = finProdFinEquiv.symm j :=
    Prod.ext hpair.1 hpair.2
  exact finProdFinEquiv.symm.injective hp

theorem fields_nodup : (fields (u := u) (Extra := Extra)).Nodup := by
  exact List.nodup_ofFn.mpr fieldAt_injective

theorem field_mem (j : Fin u) (s : Fin 6) :
    (SourceContextLoad.Tape.field j s : Tape u Extra) ∈ fields := by
  apply List.mem_ofFn.mpr
  exact ⟨finProdFinEquiv (j, s), by simp [fieldAt]⟩

theorem mem_fields_iff (p : Tape u Extra) : p ∈ fields ↔ ∃ j s, p = .field j s := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact ⟨(finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2, hi.symm⟩
  · rintro ⟨j, s, rfl⟩
    exact field_mem j s

abbrev Label (u : Nat) (Extra : Type) :=
  MachineDrainMany.Label (fields (u := u) (Extra := Extra)) ⊕ Unit

def main : Label u Extra := entryLabel fields

variable [DecidableEq Extra]

def program : Label u Extra → TM2.Stmt (fun _ : Tape u Extra => Bool)
    (Label u Extra) (Unit × Option Bool)
  | .inl l => MachineDrainMany.instruction fields Sum.inl (some (.inr ())) l
  | .inr _ => .load (fun _ => ((), none)) .halt

omit [DecidableEq Extra] in
theorem entry_eq :
    MachineDrainMany.entry (fields (u := u) (Extra := Extra)) Sum.inl (some (.inr ())) =
      some (main (u := u) (Extra := Extra)) := entryLabel_eq fields

theorem finalTapes_eq (base : Tape u Extra → List Bool) :
    MachineDrainMany.finalTapes fields base = outputTapes base := by
  funext p
  rw [MachineDrainMany.finalTapes_apply]
  cases p <;> simp [mem_fields_iff, outputTapes]

theorem clearTrace (base : Tape u Extra → List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[MachineDrainMany.lengthSum fields base + 6 * u + 1]
      (some ⟨some main, ((), register), base⟩) =
      some ⟨none, ((), none), outputTapes base⟩ := by
  have drain := MachineDrainMany.trace fields Sum.inl (some (.inr ()))
    program (fun _ => rfl) base () register
  rw [entry_eq, finalTapes_eq, steps_eq_of_nodup fields fields_nodup, fields_length] at drain
  have last : (advance (TM2.step program))^[1]
      (some ⟨some (.inr ()), ((), MachineDrainMany.finalRegister (fields (u := u) (Extra := Extra)) register), outputTapes base⟩) =
      some ⟨none, ((), none), outputTapes base⟩ := rfl
  exact trace_trans _ drain last

theorem lengthSum_le_selected {K : Type} (chosen : List K)
    (base : K → List Bool) (B : Nat) (h : ∀ k ∈ chosen, (base k).length ≤ B) :
    MachineDrainMany.lengthSum chosen base ≤ chosen.length * B := by
  induction chosen with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons source chosen ih =>
      have hs := h source (by simp)
      have ht := ih (by intro k hk; exact h k (by simp [hk]))
      simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
        List.length_cons, Nat.add_mul, Nat.one_mul] at ht ⊢
      omega

theorem clauseField_length_le {n : Nat} (clause : Target.Clause n) (s : Fin 6) :
    (encodeWord ((clauseWords clause)[s.val]'(by simp))).length ≤ n + 2 := by
  have h0 := clause[0].variableIndex.isLt
  have h1 := clause[1].variableIndex.isLt
  have h2 := clause[2].variableIndex.isLt
  fin_cases s <;> simp [clauseWords, literalWords, encodeWord_length]
  all_goals first | omega | (split <;> omega)

omit [DecidableEq Extra] in
theorem loaded_field_length_le (F : Target.Formula)
    (tuple : Fin u → Fin F.clauses.length) (base : Tape u Extra → List Bool)
    (hfields : ∀ j s, base (.field j s) = []) (j : Fin u) (s : Fin 6) :
    (SourceContextLoad.stageTapes F tuple base u (.field j s)).length ≤
      (formulaBits F).length := by
  rw [SourceContextLoad.stageTapes_field, ite_eq_left j.isLt, hfields, List.append_nil]
  exact (clauseField_length_le _ s).trans (variables_add_two_le_input F)

omit [DecidableEq Extra] in
theorem loaded_cost_le (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = []) :
    MachineDrainMany.lengthSum fields (SourceContextLoad.stageTapes F tuple base u) + 6 * u + 1 ≤
      6 * u * ((formulaBits F).length + 1) + 1 := by
  have h := lengthSum_le_selected fields (SourceContextLoad.stageTapes F tuple base u)
    (formulaBits F).length (by
      intro p hp
      obtain ⟨j, s, rfl⟩ := (mem_fields_iff p).mp hp
      exact loaded_field_length_le F tuple base hfields j s)
  rw [fields_length] at h
  rw [Nat.mul_add, Nat.mul_one]
  omega

def clearLoadedInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some main, ((), register), SourceContextLoad.stageTapes F tuple base u⟩
      (some ⟨none, ((), none), outputTapes (SourceContextLoad.stageTapes F tuple base u)⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) where
  steps := MachineDrainMany.lengthSum fields (SourceContextLoad.stageTapes F tuple base u) + 6 * u + 1
  evals_in_steps := clearTrace _ register
  steps_le_m := loaded_cost_le F tuple base hfields

omit [DecidableEq Extra] in
theorem output_loaded_eq_base (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = [])
    (hindex : base .index = []) (hwork : base .work = []) :
    outputTapes (SourceContextLoad.stageTapes F tuple base u) = base := by
  funext p
  cases p with
  | field j s => exact (hfields j s).symm
  | index => exact (SourceContextLoad.stageTapes_clean F tuple base u hindex hwork).1.trans hindex.symm
  | work => exact (SourceContextLoad.stageTapes_clean F tuple base u hindex hwork).2.trans hwork.symm
  | _ => exact SourceContextLoad.stageTapes_frame F tuple base u _ (by simp) (by simp) (by simp)

/-- With initially clean fields and lookup work tapes, loading followed by this
cleanup restores the caller's original frame exactly. -/
def clearLoadedToBaseInTime (F : Target.Formula) (tuple : Fin u → Fin F.clauses.length)
    (base : Tape u Extra → List Bool) (hfields : ∀ j s, base (.field j s) = [])
    (hindex : base .index = []) (hwork : base .work = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some main, ((), register), SourceContextLoad.stageTapes F tuple base u⟩
      (some ⟨none, ((), none), base⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
  simpa only [output_loaded_eq_base F tuple base hfields hindex hwork] using
    clearLoadedInTime F tuple base hfields register

end UniqueGamesTheorem.Foundations.Hastad.SourceContextClear

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceQueryOrderLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Hastad.SourceQueryOrder

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceAddressDescriptors SourceLoopOrder


theorem equationBits_eq (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (t : SourceQueryLoop.Query u D) :
    SourceTestAppend.equationBits u D (baseValue F u c (sampledVariables F c s))
      (ofContext F c s, t) = occurrenceBits F u D ((c, s), t) := by
  rw [occurrenceBits, sourceEquation_words]
  rfl

theorem prefixBits_eq_slotBits (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (fallback : SourceQueryLoop.Query u D) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback)
      (baseValue F u c (sampledVariables F c s)) (ofContext F c s)
      (testTapeEncoding u D).size = slotBits F u D c s := by
  rw [query_prefixBits_eq_enumerate]
  unfold slotBits
  congr 1
  funext t
  exact equationBits_eq F u D c s t

variable {K Λ : Type} [DecidableEq K]

theorem sourceLoopInTime (F : Formula) (u D : Nat) (c : ClauseContext F u)
    (s : SlotContext u) (fallback initialQuery : SourceQueryLoop.Query u D)
    (layout : SourceTestAppend.Layout K)
    (labels : SourceQueryLoop.Label u D (testTapeEncoding u D).size → Λ)
    (exit : Option Λ)
    (p : Λ → TM2.Stmt (fun _ : K => Bool) Λ (SourceQueryLoop.State u D))
    (atLabels : ∀ l, p (labels l) = SourceQueryLoop.statement u D
      (testTapeEncoding u D).size (rankedQuery u D fallback) layout labels exit l)
    (base : K → List Bool)
    (sourceWords : ∀ side, base (layout.sources side) =
      encodeWord (baseValue F u c (sampledVariables F c s) side))
    (scratchEmpty : base layout.scratch = [])
    (temporaryEmpty : base layout.temporary = []) :
    ∃ lastQuery : SourceQueryLoop.Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step p)
        ⟨some (labels (.load ⟨0, Nat.zero_lt_succ _⟩)),
          ((ofContext F c s, initialQuery), none), base⟩
        (some ⟨exit, ((ofContext F c s, lastQuery), none),
          SourceTestAppend.resultTapes layout base (slotBits F u D c s)⟩)
        ((testTapeEncoding u D).size * (9 * nBits F u + 21) + 1)) := by
  have hbound : ∀ i, i < (testTapeEncoding u D).size →
      SourceTestAppend.steps u D (baseValue F u c (sampledVariables F c s))
        (ofContext F c s, rankedQuery u D fallback i) ≤ 9 * nBits F u + 20 := by
    intro i hi
    let run := SourceTestAppend.sourceAppendInTime F u D
      ((c, s), rankedQuery u D fallback i) layout
      (fun l => labels (.emit ⟨i, hi⟩ l))
      (some (labels (.load ⟨i + 1, by omega⟩))) p
      (fun l => atLabels (.emit ⟨i, hi⟩ l)) base sourceWords
      scratchEmpty temporaryEmpty none
    exact run.steps_le_m
  have h := SourceQueryLoop.loopInTime u D (testTapeEncoding u D).size
    (9 * nBits F u + 20) (rankedQuery u D fallback) layout labels exit p atLabels
    (ofContext F c s) initialQuery base (baseValue F u c (sampledVariables F c s))
    sourceWords scratchEmpty temporaryEmpty hbound
  rw [prefixBits_eq_slotBits] at h
  exact h

end UniqueGamesTheorem.Foundations.Hastad.SourceQueryOrder



namespace UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge


variable {u D : Nat} {Extra : Type}

def clauseRankSlots : MachineHorner.Layout u ↪ Arena u Extra :=
  SourceRankPhase.clauseSlots (rankControls .clauseCount)

def variableRankSlots (selected : SlotContext u) : MachineHorner.Layout u ↪ Arena u Extra :=
  SourceRankPhase.variableSlots (rankControls .variableCount) selected

/-- Both address-base phases use the same clean arithmetic work tapes. The
right side adds the retained left block; the left side adds a seeded zero. -/
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

end UniqueGamesTheorem.Foundations.Hastad.SourceRuntimeModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel

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

/-- An explicit tape enumeration, fixed before the input is supplied. It uses
constructor lists and increasing finite coefficient indices. -/
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

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorModel



namespace UniqueGamesTheorem.Foundations.Hastad.SourceStartup

open Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition


noncomputable section

variable {u D : Nat}

abbrev State (u D : Nat) := SourceRuntimeModel.State u D

attribute [local instance] OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.instDecidableEqExtra
def headerLayout (u D : Nat) : SourceHeaderAccumulate.Layout (Tape u D) where
  bits := workTape .bitCount
  count := workTape .occurrenceCount
  accumulator := workTape .accumulator
  bits_count := by simp [workTape]
  bits_accumulator := by simp [workTape]
  count_accumulator := by simp [workTape]

def arithmeticProgram : ArithmeticLabel u D →
    TM2.Stmt (fun _ : Tape u D => Bool) (ArithmeticLabel u D) ArithmeticState
  | .inl l => SourceHeaderCounts.statement (headerSlots u D) Sum.inl (some (.inr false)) l
  | .inr l => SourceHeaderAccumulate.statement (headerLayout u D) Sum.inr none l

def program : Label u D → TM2.Stmt (fun _ : Tape u D => Bool) (Label u D) (State u D)
  | .inl l => MachineStateFrame.statement Sum.inl (some (.inr (arithmeticEntry u D)))
      (SourceLoopInit.program l)
  | .inr l => MachineControl.statement id (arithmeticStateEquiv u D)
      (MachineStateFrame.statement Sum.inr none (arithmeticProgram l))

def countedTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceHeaderCounts.resultTapes (headerSlots u D) (initializedTapes F)
    F.variables F.clauses.length

def outputTapes (F : Target.Formula) : Tape u D → List Bool :=
  SourceHeaderAccumulate.resultTapes (headerLayout u D) (countedTapes F)
    (SourceHeaderCounts.bitValue u F.variables F.clauses.length)
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

def initialArithmeticMetadata (u D : Nat) (hD : 0 < D) : ArithmeticMetadata u D :=
  ((arithmeticStateEquiv u D).symm (SourceGeneratorModel.initialState u D hD)).2

theorem initial_arithmetic (hD : 0 < D) :
    arithmeticStateEquiv u D ((((), ()), none), initialArithmeticMetadata u D hD) =
      SourceGeneratorModel.initialState u D hD := rfl

theorem initial_loader (hD : 0 < D) :
    (((), none), (SourceGeneratorModel.initialState u D hD).2) =
      SourceGeneratorModel.initialState u D hD := rfl

def initializeInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨some (.inr (arithmeticEntry u D)), SourceGeneratorModel.initialState u D hD,
        initializedTapes F⟩)
      ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) := by
  have run := SourceLoopInit.initializeInTime F hm (initialTapes (u := u) (D := D) F)
    (by simp [initialTapes]) (by simp [initialTapes]) (by simp [initialTapes])
    (by simp [initialTapes]) (by simp [initialTapes, SourceLoopInit.clauseHeader])
    (by intro j; simp [initialTapes]) (by intro j; simp [initialTapes])
  have lifted := MachineStateFrame.execution Sum.inl (some (.inr (arithmeticEntry u D)))
    (SourceGeneratorModel.initialState u D hD).2 SourceLoopInit.program program (fun _ => rfl) run
  simpa only [MachineStateFrame.configuration, MachineSubroutine.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.label, initial_loader,
    initializedTapes] using lifted

def arithmeticInTime (F : Target.Formula) :
    StateTransition.EvalsToInTime (TM2.step arithmeticProgram)
      ⟨some (arithmeticEntry u D), (((), ()), none), initializedTapes F⟩
      (some ⟨none, (((), ()), none), outputTapes F⟩)
      (SourceHeaderCounts.steps u D F.variables F.clauses.length +
        SourceHeaderCounts.bitValue u F.variables F.clauses.length +
        SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4) := by
  have countRun := SourceHeaderCounts.inTime (headerSlots u D) Sum.inl (some (.inr false))
    arithmeticProgram (fun _ => rfl) (initializedTapes F) F.variables F.clauses.length
    (initialized_variableHeader F) (initialized_clauseHeader F) (initialized_clean F) () none
  have appendRun := SourceHeaderAccumulate.inTime (headerLayout u D) Sum.inr none
    arithmeticProgram (fun _ => rfl) (countedTapes F)
    (SourceHeaderCounts.bitValue u F.variables F.clauses.length)
    (SourceHeaderCounts.occurrenceValue u D F.clauses.length)
    (SourceHeaderCounts.result_bits (headerSlots u D) (initializedTapes F) _ _)
    (SourceHeaderCounts.result_occurrences (headerSlots u D) (initializedTapes F) _ _) ((), ()) none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step arithmeticProgram) _ _ _ _ _
    countRun appendRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  have ht := joined.steps_le_m
  omega

def arithmeticConfiguration (metadata : ArithmeticMetadata u D)
    (c : TM2.Cfg (fun _ : Tape u D => Bool) (ArithmeticLabel u D) ArithmeticState) :
    TM2.Cfg (fun _ : Tape u D => Bool) (Label u D) (State u D) :=
  MachineControl.configuration id (arithmeticStateEquiv u D)
    (MachineStateFrame.configuration Sum.inr none metadata c)

theorem arithmetic_step (metadata : ArithmeticMetadata u D)
    (a b : TM2.Cfg (fun _ : Tape u D => Bool) (ArithmeticLabel u D) ArithmeticState)
    (h : TM2.step arithmeticProgram a = some b) :
    TM2.step program (arithmeticConfiguration metadata a) =
      some (arithmeticConfiguration metadata b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (arithmeticProgram l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux
      (MachineControl.statement id (arithmeticStateEquiv u D)
        (MachineStateFrame.statement Sum.inr none (arithmeticProgram l)))
      ((arithmeticStateEquiv u D) (state, metadata)) tapes) = _
    rw [MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
    rfl

def arithmeticPlacedInTime (F : Target.Formula) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr (arithmeticEntry u D)), SourceGeneratorModel.initialState u D hD, initializedTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, outputTapes F⟩)
      (SourceHeaderCounts.steps u D F.variables F.clauses.length +
        SourceHeaderCounts.bitValue u F.variables F.clauses.length +
        SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4) := by
  have lifted := liftExecutionInTime (TM2.step arithmeticProgram) (TM2.step program)
    (arithmeticConfiguration (initialArithmeticMetadata u D hD))
    (arithmetic_step (initialArithmeticMetadata u D hD)) (arithmeticInTime F)
  simpa only [arithmeticConfiguration, MachineControl.configuration,
    MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, Option.map_some, Option.map_none,
    id_eq, initial_arithmetic] using lifted

def phaseBound (F : Target.Formula) (u D : Nat) : Nat :=
  ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) +
    (SourceHeaderCounts.steps u D F.variables F.clauses.length +
      SourceHeaderCounts.bitValue u F.variables F.clauses.length +
      SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4)

def phasesInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, outputTapes F⟩)
      (phaseBound F u D) := by
  have run := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (initializeInTime (u := u) F hm hD) (arithmeticPlacedInTime (u := u) F hD)
  simpa only [phaseBound, Nat.add_comm] using run

theorem output_eq_ready (F : Target.Formula) (hm : 0 < F.clauses.length) :
    outputTapes (u := u) (D := D) F = readyTapes F := by
  funext k
  cases k <;> try simp [outputTapes, SourceHeaderAccumulate.resultTapes, headerLayout,
    countedTapes, SourceHeaderCounts.resultTapes, SourceHeaderCounts.control,
    headerSlots, headerControl, workTape, readyTapes]
  rename_i e
  cases e with
  | inl h =>
    cases h <;> simp
  | inr role =>
    cases role <;> simp [SourceHeaderCounts.bitValue_eq_nBits,
      SourceHeaderCounts.occurrenceValue_eq_length F u D hm]
    change Function.update (_ : Tape u D → List Bool) (.extra (.inr .bitCount)) _
      (.extra (.inr .accumulator)) = []
    simp

theorem ready_work_blank (F : Target.Formula) (role : BodyWork (SourceGeneratorModel.Extra u D))
    (hl : role ≠ .leftBlock) (hd : role ≠ .dummy) (ha : role ≠ .accumulator) :
    readyTapes F (workTape role) = [] := by
  cases role <;> try contradiction
  all_goals exact initialized_work F _

theorem ready_sharedFrame (F : Target.Formula) (k : Tape u D)
    (hk : k = .index ∨ k = .scratch ∨ k = .copyScratch) : readyTapes F k = [] := by
  rcases hk with rfl | rfl | rfl <;>
    simp only [readyTapes, initializedTapes]
  all_goals
    rw [SourceLoopInit.output_frame F (initialTapes F) _
      (by simp) (by simp [SourceLoopInit.variableHeader]) (by simp [SourceLoopInit.clauseHeader])
      (by simp) (by simp)]
    simp [initialTapes]

def startupInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, readyTapes F⟩)
      (phaseBound F u D) := by
  have run := phasesInTime (u := u) F hm hD
  simpa only [output_eq_ready F hm] using run

theorem phaseBound_le_polynomial (F : Target.Formula) (u D : Nat) :
    phaseBound F u D ≤ (timePolynomial u D).eval (formulaBits F).length := by
  have hn := SourceBounds.formulaBits_length_ge_variables F
  have hm := SourceBounds.formulaBits_length_ge_clauses F
  have hc := SourceHeaderCounts.steps_le_timePolynomial u D F.variables F.clauses.length
    (formulaBits F).length hn hm
  have hl : SourceHeaderCounts.leftValue u F.variables ≤
      SourceHeaderCounts.leftValue u (formulaBits F).length :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn u)
  have hr : SourceHeaderCounts.rightValue u F.clauses.length ≤
      SourceHeaderCounts.rightValue u (formulaBits F).length :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm u)
  have ho : SourceHeaderCounts.occurrenceValue u D F.clauses.length ≤
      SourceHeaderCounts.occurrenceValue u D (formulaBits F).length :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm u)
  simp only [phaseBound, timePolynomial, Polynomial.eval_add, Polynomial.eval_C,
    SourceLoopInit.timePolynomial_eval, SourceHeaderCounts.polynomial_left_eval,
    SourceHeaderCounts.polynomial_right_eval, SourceHeaderCounts.polynomial_occurrences_eval,
    SourceHeaderCounts.bitValue, SourceHeaderCounts.dummyValue]
  omega

def startupInPolynomialTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, readyTapes F⟩)
      ((timePolynomial u D).eval (formulaBits F).length) := by
  have run := startupInTime (u := u) F hm hD
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  exact Nat.le_trans run.steps_le_m (phaseBound_le_polynomial F u D)

end

end UniqueGamesTheorem.Foundations.Hastad.SourceStartup



namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleTape

open Turing Complexity SourceContexts SourceRuntimeModel


variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

theorem update_rank (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .rank) value = tapes base {s with rank := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_rightBase (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .rightBase) value = tapes base {s with rightBase := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_leftBase (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .leftBase) value = tapes base {s with leftBase := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_zero (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .zero) value = tapes base {s with zero := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem update_emitted (base : Arena u Extra → List Bool) (s : Snapshot) (value : List Bool) :
    Function.update (tapes base s) (workTape .accumulator)
      (value.reverse ++ base (workTape .accumulator)) = tapes base {s with emitted := value} := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role => cases role <;> simp [tapes, workTape]

theorem query_result (base : Arena u Extra → List Bool) (s : Snapshot) (bits : List Bool) :
    SourceTestAppend.resultTapes queryLayout (tapes base s) bits =
      tapes base {s with emitted := s.emitted ++ bits} := by
  change Function.update (tapes base s) (workTape .accumulator)
    (bits.reverse ++ tapes base s (workTape .accumulator)) = _
  rw [tapes_accumulator]
  have h := update_emitted base s (s.emitted ++ bits)
  simpa only [List.reverse_append, List.append_assoc] using h

theorem horner_clause_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes clauseRankSlots (tapes base s) value =
      tapes base {s with rank := encodeWord value ++ s.rank} := by
  change Function.update (tapes base s) (workTape .rank)
    (encodeWord value ++ tapes base s (workTape .rank)) = _
  rw [tapes_rank, update_rank]

theorem horner_variable_result (base : Arena u Extra → List Bool) (s : Snapshot)
    (selected : SlotContext u) (value : Nat) :
    MachineHorner.resultTapes (variableRankSlots selected) (tapes base s) value =
      tapes base {s with rank := encodeWord value ++ s.rank} := by
  change Function.update (tapes base s) (workTape .rank)
    (encodeWord value ++ tapes base s (workTape .rank)) = _
  rw [tapes_rank, update_rank]

theorem horner_right_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes (baseSlots true) (tapes base s) value =
      tapes base {s with rightBase := encodeWord value ++ s.rightBase} := by
  change Function.update (tapes base s) (workTape .rightBase)
    (encodeWord value ++ tapes base s (workTape .rightBase)) = _
  rw [tapes_rightBase, update_rightBase]

theorem horner_left_result (base : Arena u Extra → List Bool) (s : Snapshot) (value : Nat) :
    MachineHorner.resultTapes (baseSlots false) (tapes base s) value =
      tapes base {s with leftBase := encodeWord value ++ s.leftBase} := by
  change Function.update (tapes base s) (workTape .leftBase)
    (encodeWord value ++ tapes base s (workTape .leftBase)) = _
  rw [tapes_leftBase, update_leftBase]

structure WorkClean (base : Arena u Extra → List Bool) : Prop where
  accA : base (workTape .accA) = []
  accB : base (workTape .accB) = []
  counter : base (workTape .counter) = []
  scratch : base (workTape .arithScratch) = []

omit [DecidableEq Extra] in
theorem clean_clause (base : Arena u Extra → List Bool) (s : Snapshot) (clean : WorkClean base) :
    MachineHorner.Clean clauseRankSlots (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem clean_variable (base : Arena u Extra → List Bool) (s : Snapshot) (selected : SlotContext u)
    (clean : WorkClean base) : MachineHorner.Clean (variableRankSlots selected) (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem clean_base (base : Arena u Extra → List Bool) (s : Snapshot) (right : Bool)
    (clean : WorkClean base) : MachineHorner.Clean (baseSlots right) (tapes base s) where
  accA := clean.accA
  accB := clean.accB
  counter := clean.counter
  scratch := clean.scratch

omit [DecidableEq Extra] in
theorem tapes_coordinateOutput {n : Nat} (j : Fin u) (clause : Target.Clause n)
    (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes (SourceContextLoad.coordinateOutput j clause base) s =
      SourceContextLoad.coordinateOutput j clause (tapes base s) := by
  funext k
  cases k <;> simp [tapes, SourceContextLoad.coordinateOutput, workTape]
  rename_i extra
  cases extra with
  | inl header => rfl
  | inr role => cases role <;> rfl

omit [DecidableEq Extra] in

theorem tapes_stageTapes (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot) (r : Nat) :
    tapes (SourceContextLoad.stageTapes F c base r) s =
      SourceContextLoad.stageTapes F c (tapes base s) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [SourceContextLoad.stageTapes]
    split
    · rw [tapes_coordinateOutput, ih]
    · exact ih

theorem final_tapes (base : Arena u Extra → List Bool) (emitted : List Bool)
    (hrank : base (workTape .rank) = []) (hright : base (workTape .rightBase) = [])
    (hleft : base (workTape .leftBase) = []) (hzero : base (workTape .zero) = []) :
    tapes base {emitted := emitted} =
      Function.update base (workTape .accumulator) (emitted.reverse ++ base (workTape .accumulator)) := by
  funext k
  cases k <;> try rfl
  rename_i extra
  cases extra with
  | inl header => simp [tapes, workTape]
  | inr role =>
    cases role <;> simp_all [tapes, workTape]

theorem empty_tapes (base : Arena u Extra → List Bool)
    (hrank : base (workTape .rank) = []) (hright : base (workTape .rightBase) = [])
    (hleft : base (workTape .leftBase) = []) (hzero : base (workTape .zero) = []) :
    tapes base {} = base := by
  simpa using final_tapes base [] hrank hright hleft hzero

/-- Apply the checked actual field cleanup directly to an overlaid loaded context. -/
def clearLoadedSnapshotInTime (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (s : Snapshot)
    (hfields : ∀ j k, base (.field j k) = []) (hindex : base .index = []) (hwork : base .work = [])
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step SourceContextClear.program)
      ⟨some SourceContextClear.main, ((), register), tapes (SourceContextLoad.stageTapes F c base u) s⟩
      (some ⟨none, ((), none), tapes base s⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
  rw [tapes_stageTapes]
  exact SourceContextClear.clearLoadedToBaseInTime F c (tapes base s) hfields hindex hwork register

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleTape

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceTupleBody
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One actual clause-tuple body. Its fixed finite control loads the context,
computes the shared right address base, traverses every selected-slot tuple and
query tape in their declared encoding order, and physically clears its work.
-/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature
open SourceRuntimeModel SourceTupleTape


inductive Label (u D : Nat) (Extra : Type)
  | prepare (label : SourceContextPrepare.Label u)
  | seedZero
  | clauseRank (label : MachineHorner.Label u)
  | rightBase (label : SourceBasePhase.Label)
  | clearClauseRank
  | select (index : Fin (SlotCount u + 1))
  | variableRank (index : Fin (SlotCount u)) (label : MachineHorner.Label u)
  | leftBase (index : Fin (SlotCount u)) (label : SourceBasePhase.Label)
  | query (index : Fin (SlotCount u)) (label : SourceQueryLoop.Label u D (QueryCount u D))
  | clearSlotRank (index : Fin (SlotCount u))
  | clearLeft (index : Fin (SlotCount u))
  | clearRight | clearZero
  | clearContext (label : SourceContextClear.Label u (BodyExtra Extra))
  | reset
  deriving DecidableEq, Fintype

variable {u D : Nat} {Extra : Type}

def main : Label u D Extra := .prepare (.inl (SourceContextLoad.labelAt 0))

variable [DecidableEq Extra]

def finish (exit : Option (Label u D Extra)) :
    TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u D Extra) (State u D) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def drainProgram (source : Arena u Extra) :
    Unit → TM2.Stmt (fun _ : Arena u Extra => Bool) Unit SourceContextPrepare.LoadState :=
  fun _ => MachineDrain.drain source () none

def drainStatement (source : Arena u Extra) (label : Label u D Extra)
    (exit : Option (Label u D Extra)) :
    TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u D Extra) (State u D) :=
  MachineStateFrame.statement (fun _ : Unit => label) exit (drainProgram source ())

def program (initialQuery : Query u D) (exit : Option (Label u D Extra)) :
    Label u D Extra → TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u D Extra) (State u D)
  | .prepare label => MachineSubroutine.statement .prepare (some .seedZero)
      (SourceContextPrepare.program label)
  | .seedZero => .push (workTape .zero) (fun _ => false) (.goto fun _ => .clauseRank .start)
  | .clauseRank label => framed (arithmeticStateEquiv u D) .clauseRank
      (some (.rightBase .seed)) (SourceRankPhase.program clauseRankSlots label)
  | .rightBase label => framed (arithmeticStateEquiv u D) .rightBase
      (some .clearClauseRank) (SourceBasePhase.program (baseSlots true) (2 ^ (8 ^ u)) label)
  | .clearClauseRank => drainStatement (workTape .rank) .clearClauseRank
      (some (.select ⟨0, by omega⟩))
  | .select index =>
    if h : index.val < SlotCount u then
      .load (selectState initialQuery ⟨index.val, h⟩)
        (.goto fun _ => .variableRank ⟨index.val, h⟩ .start)
    else .goto fun _ => .clearRight
  | .variableRank index label => framed (arithmeticStateEquiv u D) (.variableRank index)
      (some (.leftBase index .seed))
      (SourceRankPhase.program (variableRankSlots (selected index)) label)
  | .leftBase index label => framed (arithmeticStateEquiv u D) (.leftBase index)
      (some (.query index (.load ⟨0, by omega⟩)))
      (SourceBasePhase.program (baseSlots false) (2 ^ (2 ^ u)) label)
  | .query index label => framed (queryStateEquiv u D) (.query index)
      (some (.clearSlotRank index))
      (SourceQueryLoop.statement u D (QueryCount u D)
        (SourceLoopOrder.rankedQuery u D initialQuery) queryLayout id none label)
  | .clearSlotRank index => drainStatement (workTape .rank) (.clearSlotRank index)
      (some (.clearLeft index))
  | .clearLeft index => drainStatement (workTape .leftBase) (.clearLeft index)
      (some (.select ⟨index.val + 1, by omega⟩))
  | .clearRight => drainStatement (workTape .rightBase) .clearRight (some .clearZero)
  | .clearZero => drainStatement (workTape .zero) .clearZero
      (some (.clearContext SourceContextClear.main))
  | .clearContext label => MachineStateFrame.statement .clearContext (some .reset)
      (SourceContextClear.program label)
  | .reset => .load (fun _ => canonicalState initialQuery) (finish exit)

/-- All finite internal state is reset before the caller continuation. -/
theorem reset_step (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (state : State u D) (tapes : Arena u Extra → List Bool) :
    TM2.step (program initialQuery exit) ⟨some .reset, state, tapes⟩ =
      some ⟨exit, canonicalState initialQuery, tapes⟩ := by
  cases exit <;> rfl

def resetInTime (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (state : State u D) (tapes : Arena u Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .reset, state, tapes⟩ (some ⟨exit, canonicalState initialQuery, tapes⟩) 1 where
  steps := 1
  evals_in_steps := reset_step initialQuery exit state tapes
  steps_le_m := Nat.le_refl _

/-- The complete representation needed at one odometer leaf. Remaining-digit
stacks, output history, and retained unused headers are arbitrary. -/
structure Ready (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) : Prop where
  formula : base .formula = formulaBits F
  current : ∀ j, base (.current j) = encodeWord (c j).val
  index : base .index = []
  work : base .work = []
  scratch : base .scratch = []
  copyScratch : base .copyScratch = []
  fields : ∀ j s, base (.field j s) = []
  variableCount : base variableHeader = encodeWord F.variables
  clauseCount : base clauseHeader = encodeWord F.clauses.length
  leftBlock : base (workTape .leftBlock) = encodeWord (2 ^ (2 ^ u) * F.variables ^ u)
  dummy : base (workTape .dummy) =
    encodeWord (F.variables ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u))
  rank : base (workTape .rank) = []
  rightBase : base (workTape .rightBase) = []
  leftBase : base (workTape .leftBase) = []
  zero : base (workTape .zero) = []
  accA : base (workTape .accA) = []
  accB : base (workTape .accB) = []
  counter : base (workTape .counter) = []
  arithScratch : base (workTape .arithScratch) = []
  coefficient : base (workTape .coefficient) = []
  queryTemporary : base (workTape .queryTemporary) = []
  queryScratch : base (workTape .queryScratch) = []

def rightValue (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  SourceAddressDescriptors.baseValue F u c (sampledVariables F c (fun _ => .first)) 1

def variableRank (F : Target.Formula) (c : ClauseContext F u) (index : Fin (SlotCount u)) : Nat :=
  ((variableEncoding F u).code (sampledVariables F c (selected index))).val

def leftValue (F : Target.Formula) (c : ClauseContext F u) (index : Fin (SlotCount u)) : Nat :=
  SourceAddressDescriptors.baseValue F u c (sampledVariables F c (selected index)) 0

noncomputable def slotBudget (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) : Nat :=
  1 + (MachineHorner.timePolynomial u).eval F.variables +
    (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
      (SourceBasePhase.operandLength (variableRank F c index) 0) +
    (QueryCount u D * (9 * nBits F u + 21) + 1) +
    (variableRank F c index + 2) + (leftValue F c index + 2)

/-- Concrete context-loader/signature phase in the tuple-body program. -/
noncomputable def preparePhase (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hformula : base .formula = formulaBits F)
    (hcurrent : ∀ j, base (.current j) = encodeWord (c j).val)
    (hindex : base .index = []) (hwork : base .work = [])
    (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hfields : ∀ p : Position u, base (SourceSignaturePrepare.variableField p) = []) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some main, canonicalState initialQuery, base⟩
      (some ⟨some .seedZero,
        SourceContextPrepare.finalState F c (fun _ => .first)
          ((((canonicalSignature u, initialQuery), none), (((), ()), none))),
        SourceContextLoad.stageTapes F c base u⟩)
      ((u * (10 * (formulaBits F).length + 20) + 1) +
        (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
          (5 * (formulaBits F).length + 6) + 2)) := by
  let run := SourceContextPrepare.prepareInTime (τ := QueryState u D × ArithmeticState) F c (fun _ => .first) base hformula hcurrent
    hindex hwork hscratch hcopy hfields (fun _ _ => false) (canonicalSignature u) rfl
    ((((canonicalSignature u, initialQuery), none), (((), ()), none)))
  exact MachineSubroutine.execution .prepare (some .seedZero) SourceContextPrepare.program
    (program initialQuery exit) (fun _ => rfl) run

def seedZeroPhase (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (state : State u D) (base : Arena u Extra → List Bool) (hzero : base (workTape .zero) = []) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .seedZero, state, base⟩
      (some ⟨some (.clauseRank .start), state,
        Function.update base (workTape .zero) (encodeWord 0)⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program initialQuery exit .seedZero) state base) = _
    simp only [program, TM2.stepAux, hzero]
    rfl
  steps_le_m := Nat.le_refl _

/-- The caller only supplies a local code equality; the physical drain and
its entire runtime are obtained from the checked drain machine. -/
def drainPhase (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (source : Arena u Extra) (entry : Label u D Extra) (next : Option (Label u D Extra))
    (atEntry : program initialQuery exit entry = drainStatement source entry next)
    (base : Arena u Extra → List Bool)
    (metadata : SourceSignaturePrepare.State u (QueryState u D × ArithmeticState))
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some entry, (((), register), metadata), base⟩
      (some ⟨next, (((), none), metadata), Function.update base source []⟩)
      ((base source).length + 1) := by
  let run := MachineDrain.drainInTime source () none (drainProgram source) rfl base () register
  exact MachineStateFrame.execution (fun _ : Unit => entry) next metadata (drainProgram source)
    (program initialQuery exit) (fun _ => atEntry) run

noncomputable def clauseRankPhase (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hradix : base (clauseRankSlots (.inl 0)) = encodeWord F.clauses.length)
    (hdigits : ∀ i, base (clauseRankSlots (.inr i)) = encodeWord (c i).val)
    (hclean : MachineHorner.Clean clauseRankSlots base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clauseRank .start), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.rightBase .seed), arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes clauseRankSlots base (((clauseEncoding F u).code c).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
  let run := SourceRankPhase.clauseRankInTime F u c clauseRankSlots id none
    (SourceRankPhase.program clauseRankSlots) (fun _ => rfl) base hradix hdigits hclean () none
  exact framedExecution (arithmeticStateEquiv u D) .clauseRank (some (.rightBase .seed))
    metadata (SourceRankPhase.program clauseRankSlots) (program initialQuery exit)
    (fun _ => rfl) run

noncomputable def variableRankPhase (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hradix : base (variableRankSlots (selected index) (.inl 0)) = encodeWord F.variables)
    (hdigits : ∀ i, base (variableRankSlots (selected index) (.inr i)) =
      encodeWord (sampledVariables F c (selected index) i).val)
    (hclean : MachineHorner.Clean (variableRankSlots (selected index)) base)
    (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.variableRank index .start), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.leftBase index .seed), arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (variableRankSlots (selected index)) base
          (((variableEncoding F u).code (sampledVariables F c (selected index))).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.variables) := by
  let slots := variableRankSlots (u := u) (Extra := Extra) (selected index)
  let run := SourceRankPhase.variableRankInTime F u (sampledVariables F c (selected index))
    slots id none (SourceRankPhase.program slots) (fun _ => rfl) base hradix hdigits hclean () none
  exact framedExecution (arithmeticStateEquiv u D) (.variableRank index)
    (some (.leftBase index .seed)) metadata (SourceRankPhase.program slots)
    (program initialQuery exit) (fun _ => rfl) run

noncomputable def rightBasePhase (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hrank : base (baseSlots true (.inl 0)) = encodeWord (((clauseEncoding F u).code c).val))
    (hleftBlock : base (baseSlots true (.inr 1)) = encodeWord (2 ^ (2 ^ u) * F.variables ^ u))
    (hcoefficient : base (baseSlots true (.inr 0)) = [])
    (hclean : MachineHorner.Clean (baseSlots true) base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.rightBase .seed), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some .clearClauseRank, arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (baseSlots true) base
          (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (fun _ => .first)) 1)⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
        (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
          (2 ^ (2 ^ u) * F.variables ^ u))) := by
  let run := SourceBasePhase.rightBaseInTime F u c (sampledVariables F c (fun _ => .first))
    (baseSlots true) id none (SourceBasePhase.program (baseSlots true) (2 ^ (8 ^ u)))
    (fun _ => rfl) base hrank hleftBlock hcoefficient hclean () none
  exact framedExecution (arithmeticStateEquiv u D) .rightBase (some .clearClauseRank) metadata
    (SourceBasePhase.program (baseSlots true) (2 ^ (8 ^ u)))
    (program initialQuery exit) (fun _ => rfl) run

noncomputable def leftBasePhase (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool)
    (hrank : base (baseSlots false (.inl 0)) =
      encodeWord (((variableEncoding F u).code (sampledVariables F c (selected index))).val))
    (hzero : base (baseSlots false (.inr 1)) = encodeWord 0)
    (hcoefficient : base (baseSlots false (.inr 0)) = [])
    (hclean : MachineHorner.Clean (baseSlots false) base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.leftBase index .seed), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.query index (.load ⟨0, by omega⟩)),
        arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (baseSlots false) base
          (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (selected index)) 0)⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
        (SourceBasePhase.operandLength
          (((variableEncoding F u).code (sampledVariables F c (selected index))).val) 0)) := by
  let run := SourceBasePhase.leftBaseInTime F u c (sampledVariables F c (selected index))
    (baseSlots false) id none (SourceBasePhase.program (baseSlots false) (2 ^ (2 ^ u)))
    (fun _ => rfl) base hrank hzero hcoefficient hclean () none
  exact framedExecution (arithmeticStateEquiv u D) (.leftBase index)
    (some (.query index (.load ⟨0, by omega⟩))) metadata
    (SourceBasePhase.program (baseSlots false) (2 ^ (2 ^ u)))
    (program initialQuery exit) (fun _ => rfl) run

theorem queryPhase (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery beforeQuery : Query u D)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool)
    (metadata : QueryMetadata u)
    (hsource : ∀ side, base (queryLayout.sources side) = encodeWord
      (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (selected index)) side))
    (hscratch : base queryLayout.scratch = []) (htemporary : base queryLayout.temporary = []) :
    ∃ afterQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
        ⟨some (.query index (.load ⟨0, by omega⟩)),
          queryStateEquiv u D (((ofContext F c (selected index), beforeQuery), none), metadata), base⟩
        (some ⟨some (.clearSlotRank index),
          queryStateEquiv u D (((ofContext F c (selected index), afterQuery), none), metadata),
          SourceTestAppend.resultTapes queryLayout base
            (SourceQueryOrder.slotBits F u D c (selected index))⟩)
        (QueryCount u D * (9 * nBits F u + 21) + 1)) := by
  let localProgram := SourceQueryLoop.statement u D (QueryCount u D)
    (SourceLoopOrder.rankedQuery u D initialQuery) (queryLayout (u := u) (Extra := Extra)) id none
  obtain ⟨lastQuery, ⟨run⟩⟩ := SourceQueryOrder.sourceLoopInTime F u D c (selected index)
    initialQuery beforeQuery queryLayout id none localProgram (fun _ => rfl) base
    hsource hscratch htemporary
  refine ⟨lastQuery, ⟨?_⟩⟩
  exact framedExecution (queryStateEquiv u D) (.query index) (some (.clearSlotRank index))
    metadata localProgram (program initialQuery exit) (fun _ => rfl) run

/-- The fixed selected-slot tuple is loaded in one actual transition. -/
def selectPhase (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (index : Fin (SlotCount u)) (state : State u D) (base : Arena u Extra → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.select index.castSucc), state, base⟩
      (some ⟨some (.variableRank index .start), selectState initialQuery index state, base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program initialQuery exit (.select index.castSucc)) state base) = _
    simp only [program, Fin.val_castSucc, index.isLt, ↓reduceDIte, TM2.stepAux]
  steps_le_m := Nat.le_refl _

omit [DecidableEq Extra] in
theorem Ready.loadedClean {F : Target.Formula} {c : ClauseContext F u}
    {base : Arena u Extra → List Bool} (h : Ready F c base) :
    WorkClean (SourceContextLoad.stageTapes F c base u) where
  accA := (loaded_extra F c base _).trans h.accA
  accB := (loaded_extra F c base _).trans h.accB
  counter := (loaded_extra F c base _).trans h.counter
  scratch := (loaded_extra F c base _).trans h.arithScratch

def loopSnapshot (F : Target.Formula) (c : ClauseContext F u) (bits : List Bool) : Snapshot :=
  { rightBase := encodeWord (rightValue F c), zero := encodeWord 0, emitted := bits }

def rankSnapshot (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (bits : List Bool) : Snapshot :=
  { loopSnapshot F c bits with rank := encodeWord (variableRank F c index) }

def baseSnapshot (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (bits : List Bool) : Snapshot :=
  { rankSnapshot F c index bits with leftBase := encodeWord (leftValue F c index) }

/-- One selected-slot tuple: actual rank, base construction, complete query
stream, and physical cleanup, in the one fixed caller program. -/
theorem slotInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery beforeQuery : Query u D) (beforeSignature : Signature u)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool) (h : Ready F c base)
    (index : Fin (SlotCount u)) (bits : List Bool) :
    ∃ afterQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
        ⟨some (.select index.castSucc), workingState F c beforeSignature beforeQuery,
          tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c bits)⟩
        (some ⟨some (.select ⟨index.val + 1, by omega⟩),
          workingState F c (ofContext F c (selected index)) afterQuery,
          tapes (SourceContextLoad.stageTapes F c base u)
            (loopSnapshot F c (bits ++ SourceQueryOrder.slotBits F u D c (selected index)))⟩)
        (slotBudget (D := D) F c index)) := by
  let loaded := SourceContextLoad.stageTapes F c base u
  let sig := ofContext F c (selected index)
  let startTapes := tapes loaded (loopSnapshot F c bits)
  let rankedTapes := tapes loaded (rankSnapshot F c index bits)
  let basedTapes := tapes loaded (baseSnapshot F c index bits)
  have hs := selectPhase initialQuery exit index (workingState F c beforeSignature beforeQuery) startTapes
  rw [select_workingState] at hs
  have hr := variableRankPhase F c index initialQuery exit startTapes
    (by change loaded variableHeader = encodeWord F.variables
        exact (loaded_extra F c base _).trans h.variableCount)
    (by intro i
        exact SourceRankPhase.selectedDigits_loaded F c (selected index)
          (rankControls .variableCount) base (fun j => h.fields j _) i)
    (clean_variable loaded (loopSnapshot F c bits) (selected index) h.loadedClean)
    (arithmeticMetadata F c sig initialQuery)
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.variableRank index .start), workingState F c sig initialQuery, startTapes⟩
      (some ⟨some (.leftBase index .seed), workingState F c sig initialQuery, rankedTapes⟩)
      ((MachineHorner.timePolynomial u).eval F.variables) := by
    simpa only [arithmeticState_working, startTapes, rankedTapes, rankSnapshot,
      horner_variable_result, loopSnapshot, List.append_nil, variableRank] using hr
  have hb := leftBasePhase F c index initialQuery exit rankedTapes
    (by rfl) (by rfl)
    (by change loaded (workTape .coefficient) = []
        exact (loaded_extra F c base _).trans h.coefficient)
    (clean_base loaded (rankSnapshot F c index bits) false h.loadedClean)
    (arithmeticMetadata F c sig initialQuery)
  have hb' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.leftBase index .seed), workingState F c sig initialQuery, rankedTapes⟩
      (some ⟨some (.query index (.load ⟨0, by omega⟩)), workingState F c sig initialQuery, basedTapes⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
        (SourceBasePhase.operandLength (variableRank F c index) 0)) := by
    simpa only [arithmeticState_working, rankedTapes, basedTapes, baseSnapshot,
      horner_left_result, rankSnapshot, loopSnapshot, List.append_nil, leftValue, variableRank] using hb
  obtain ⟨lastQuery, ⟨hq⟩⟩ := queryPhase F c index initialQuery initialQuery exit basedTapes
    (queryMetadata F c)
    (by intro side
        fin_cases side
        · rfl
        · rfl
        · change loaded (workTape .dummy) = _
          exact (loaded_extra F c base _).trans h.dummy)
    (by change loaded (workTape .queryScratch) = []
        exact (loaded_extra F c base _).trans h.queryScratch)
    (by change loaded (workTape .queryTemporary) = []
        exact (loaded_extra F c base _).trans h.queryTemporary)
  let emitted := bits ++ SourceQueryOrder.slotBits F u D c (selected index)
  let emittedSnapshot := {baseSnapshot F c index bits with emitted := emitted}
  let emittedTapes := tapes loaded emittedSnapshot
  have hq' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.query index (.load ⟨0, by omega⟩)), workingState F c sig initialQuery, basedTapes⟩
      (some ⟨some (.clearSlotRank index), workingState F c sig lastQuery, emittedTapes⟩)
      (QueryCount u D * (9 * nBits F u + 21) + 1) := by
    simpa only [queryState_working, basedTapes, emittedTapes, emittedSnapshot, query_result,
      baseSnapshot, rankSnapshot, loopSnapshot, emitted, sig] using hq
  let afterRank := tapes loaded {emittedSnapshot with rank := []}
  have hdRank := drainPhase initialQuery exit (workTape .rank) (.clearSlotRank index)
    (some (.clearLeft index)) rfl emittedTapes (workingState F c sig lastQuery).2 none
  have hdRank' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clearSlotRank index), workingState F c sig lastQuery, emittedTapes⟩
      (some ⟨some (.clearLeft index), workingState F c sig lastQuery, afterRank⟩)
      (variableRank F c index + 2) := by
    simpa only [workingState_loader, emittedTapes, afterRank, update_rank, tapes_rank, emittedSnapshot,
      baseSnapshot, rankSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hdRank
  have hdLeft := drainPhase initialQuery exit (workTape .leftBase) (.clearLeft index)
    (some (.select ⟨index.val + 1, by omega⟩)) rfl afterRank
    (workingState F c sig lastQuery).2 none
  have hdLeft' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clearLeft index), workingState F c sig lastQuery, afterRank⟩
      (some ⟨some (.select ⟨index.val + 1, by omega⟩), workingState F c sig lastQuery,
        tapes loaded (loopSnapshot F c emitted)⟩)
      (leftValue F c index + 2) := by
    simpa only [workingState_loader, afterRank, update_leftBase, tapes_leftBase, emittedSnapshot,
      baseSnapshot, rankSnapshot, loopSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hdLeft
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
        (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
          (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hs hr') hb') hq') hdRank') hdLeft'
  refine ⟨lastQuery, ⟨{ toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }⟩⟩
  have hj := joined.steps_le_m
  dsimp only [slotBudget]
  omega

def slotAt (u : Nat) (i : Nat) : SlotContext u :=
  if h : i < SlotCount u then selected ⟨i, h⟩ else fun _ => .first

def prefixBits (F : Target.Formula) (c : ClauseContext F u) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixBits F c r ++ SourceQueryOrder.slotBits F u D c (slotAt u r)

noncomputable def prefixBudget (F : Target.Formula) (c : ClauseContext F u) : Nat → Nat
  | 0 => 0
  | r + 1 => prefixBudget F c r + if h : r < SlotCount u then slotBudget (D := D) F c ⟨r, h⟩ else 0

/-- The explicit finite loop runs in ascending slot-encoding order. -/
theorem prefixInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery beforeQuery : Query u D) (beforeSignature : Signature u)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool) (h : Ready F c base)
    (r : Nat) (hr : r ≤ SlotCount u) :
    ∃ afterSignature : Signature u, ∃ afterQuery : Query u D,
      Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
        ⟨some (.select ⟨0, by omega⟩), workingState F c beforeSignature beforeQuery,
          tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c [])⟩
        (some ⟨some (.select ⟨r, by omega⟩), workingState F c afterSignature afterQuery,
          tapes (SourceContextLoad.stageTapes F c base u)
            (loopSnapshot F c (prefixBits (D := D) F c r))⟩)
        (prefixBudget (D := D) F c r)) := by
  induction r with
  | zero =>
    refine ⟨beforeSignature, beforeQuery, ⟨{
      steps := 0
      evals_in_steps := rfl
      steps_le_m := Nat.le_refl _ }⟩⟩
  | succ r ih =>
    obtain ⟨previousSignature, previousQuery, ⟨previous⟩⟩ := ih (by omega)
    have hlt : r < SlotCount u := by omega
    let index : Fin (SlotCount u) := ⟨r, hlt⟩
    obtain ⟨lastQuery, ⟨one⟩⟩ := slotInTime F c initialQuery previousQuery previousSignature
      exit base h index (prefixBits (D := D) F c r)
    let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ previous one
    refine ⟨ofContext F c (selected index), lastQuery,
      ⟨{ steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }⟩⟩
    · simpa only [prefixBits, slotAt, dite_eq_left hlt, index] using joined.evals_in_steps
    · have hj := joined.steps_le_m
      simp only [prefixBudget, dite_eq_left hlt]
      dsimp only [index] at hj
      omega

theorem prefixBits_eq_ofFn (F : Target.Formula) (c : ClauseContext F u) (n : Nat) :
    prefixBits (D := D) F c n =
      (List.ofFn (fun i : Fin n => slotAt u i.val)).flatMap (SourceQueryOrder.slotBits F u D c) := by
  induction n with
  | zero => simp [prefixBits]
  | succ n ih =>
    rw [prefixBits, List.ofFn_succ', List.concat_eq_append, List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Fin.val_castSucc, Fin.val_last] using congrArg
        (fun bits => bits ++ SourceQueryOrder.slotBits F u D c (slotAt u n)) ih

theorem prefixBits_eq_tupleBits (F : Target.Formula) (c : ClauseContext F u) :
    prefixBits (D := D) F c (SlotCount u) = SourceQueryOrder.tupleBits F u D c := by
  rw [prefixBits_eq_ofFn]
  have hlist : List.ofFn (fun i : Fin (SlotCount u) => slotAt u i.val) =
      (slotContextEncoding u).enumerate := by
    apply congrArg List.ofFn
    funext i
    simp only [slotAt, i.isLt, ↓reduceDIte, selected]
  rw [hlist]
  rfl

noncomputable def setupBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  ((u * (10 * (formulaBits F).length + 20) + 1) +
    (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u *
      (5 * (formulaBits F).length + 6) + 2)) + 1 +
    (MachineHorner.timePolynomial u).eval F.clauses.length +
    (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
      (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
        (2 ^ (2 ^ u) * F.variables ^ u)) +
    (((clauseEncoding F u).code c).val + 2)

def finishBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  1 + (rightValue F c + 2) + 2 + (6 * u * ((formulaBits F).length + 1) + 1) + 1

noncomputable def bodyBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  setupBudget F c + prefixBudget (D := D) F c (SlotCount u) + finishBudget F c

/-- Actual context preparation and the shared right base are computed once. -/
noncomputable def setupInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool) (h : Ready F c base) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some main, canonicalState initialQuery, base⟩
      (some ⟨some (.select ⟨0, by omega⟩),
        workingState F c (canonicalSignature u) initialQuery,
        tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c [])⟩)
      (setupBudget F c) := by
  let loaded := SourceContextLoad.stageTapes F c base u
  let state := workingState F c (canonicalSignature u) initialQuery
  let s0 : Snapshot := {zero := encodeWord 0}
  let s1 : Snapshot := {s0 with rank := encodeWord (((clauseEncoding F u).code c).val)}
  let s2 : Snapshot := {s1 with rightBase := encodeWord (rightValue F c)}
  have hp := preparePhase F c initialQuery exit base h.formula h.current h.index h.work
    h.scratch h.copyScratch (fun p => h.fields p.1 _)
  have he : tapes loaded {} = loaded := empty_tapes loaded
    ((loaded_extra F c base _).trans h.rank) ((loaded_extra F c base _).trans h.rightBase)
    ((loaded_extra F c base _).trans h.leftBase) ((loaded_extra F c base _).trans h.zero)
  have hz := seedZeroPhase initialQuery exit state loaded ((loaded_extra F c base _).trans h.zero)
  have hupdate := update_zero loaded {} (encodeWord 0)
  rw [he] at hupdate
  rw [hupdate] at hz
  have hr := clauseRankPhase F c initialQuery exit (tapes loaded s0)
    (by change loaded clauseHeader = encodeWord F.clauses.length
        exact (loaded_extra F c base _).trans h.clauseCount)
    (by intro i
        change loaded (.current i) = encodeWord (c i).val
        exact (SourceContextLoad.stageTapes_frame F c base u (.current i)
          (by simp) (by simp) (by simp)).trans (h.current i))
    (clean_clause loaded s0 h.loadedClean)
    (arithmeticMetadata F c (canonicalSignature u) initialQuery)
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clauseRank .start), state, tapes loaded s0⟩
      (some ⟨some (.rightBase .seed), state, tapes loaded s1⟩)
      ((MachineHorner.timePolynomial u).eval F.clauses.length) := by
    simpa only [arithmeticState_working, horner_clause_result, state, s1, s0, List.append_nil] using hr
  have hb := rightBasePhase F c initialQuery exit (tapes loaded s1) (by rfl)
    (by change loaded (workTape .leftBlock) = encodeWord (2 ^ (2 ^ u) * F.variables ^ u)
        exact (loaded_extra F c base _).trans h.leftBlock)
    (by change loaded (workTape .coefficient) = []
        exact (loaded_extra F c base _).trans h.coefficient)
    (clean_base loaded s1 true h.loadedClean)
    (arithmeticMetadata F c (canonicalSignature u) initialQuery)
  have hb' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.rightBase .seed), state, tapes loaded s1⟩
      (some ⟨some .clearClauseRank, state, tapes loaded s2⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
        (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
          (2 ^ (2 ^ u) * F.variables ^ u))) := by
    simpa only [arithmeticState_working, horner_right_result, state, s2, s1, s0,
      List.append_nil, rightValue] using hb
  have hd := drainPhase initialQuery exit (workTape .rank) .clearClauseRank
    (some (.select ⟨0, by omega⟩)) rfl (tapes loaded s2) state.2 none
  have hd' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .clearClauseRank, state, tapes loaded s2⟩
      (some ⟨some (.select ⟨0, by omega⟩), state, tapes loaded (loopSnapshot F c [])⟩)
      (((clauseEncoding F u).code c).val + 2) := by
    simpa only [state, workingState_loader, update_rank, tapes_rank, s2, s1, s0,
      loopSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hd
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
        (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hp hz) hr') hb') hd'
  refine { toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }
  have hj := joined.steps_le_m
  dsimp only [setupBudget]
  omega

/-- Physical cleanup and canonical finite-state reset complete the body. -/
def finishInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery query : Query u D) (signature : Signature u)
    (exit : Option (Label u D Extra)) (base : Arena u Extra → List Bool) (h : Ready F c base)
    (bits : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.select ⟨SlotCount u, by omega⟩), workingState F c signature query,
        tapes (SourceContextLoad.stageTapes F c base u) (loopSnapshot F c bits)⟩
      (some ⟨exit, canonicalState initialQuery, SourceTestAppend.resultTapes queryLayout base bits⟩)
      (finishBudget F c) := by
  let loaded := SourceContextLoad.stageTapes F c base u
  let state := workingState F c signature query
  let s0 := loopSnapshot F c bits
  let s1 : Snapshot := {s0 with rightBase := []}
  let s2 : Snapshot := {emitted := bits}
  have hd : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.select ⟨SlotCount u, by omega⟩), state, tapes loaded s0⟩
      (some ⟨some .clearRight, state, tapes loaded s0⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program initialQuery exit (.select ⟨SlotCount u, by omega⟩))
        state (tapes loaded s0)) = _
      simp only [program, Nat.lt_irrefl, ↓reduceDIte, TM2.stepAux]
    steps_le_m := Nat.le_refl _ }
  have hr := drainPhase initialQuery exit (workTape .rightBase) .clearRight (some .clearZero)
    rfl (tapes loaded s0) state.2 none
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .clearRight, state, tapes loaded s0⟩
      (some ⟨some .clearZero, state, tapes loaded s1⟩) (rightValue F c + 2) := by
    simpa only [state, workingState_loader, update_rightBase, tapes_rightBase, s1, s0,
      loopSnapshot, encodeWord_length, Nat.add_assoc, show (1 : Nat) + 1 = 2 from rfl] using hr
  have hz := drainPhase initialQuery exit (workTape .zero) .clearZero
    (some (.clearContext SourceContextClear.main)) rfl (tapes loaded s1) state.2 none
  have hz' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some .clearZero, state, tapes loaded s1⟩
      (some ⟨some (.clearContext SourceContextClear.main), state, tapes loaded s2⟩) 2 := by
    simpa only [state, workingState_loader, update_zero, tapes_zero, s2, s1, s0,
      loopSnapshot, encodeWord_length, Nat.zero_add, show (1 : Nat) + 1 = 2 from rfl] using hz
  have cleanup := clearLoadedSnapshotInTime F c base s2 h.fields h.index h.work none
  have hc := MachineStateFrame.execution .clearContext (some .reset) state.2
    SourceContextClear.program (program initialQuery exit) (fun _ => rfl) cleanup
  have hc' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.clearContext SourceContextClear.main), state, tapes loaded s2⟩
      (some ⟨some .reset, state, tapes base s2⟩)
      (6 * u * ((formulaBits F).length + 1) + 1) := by
    simpa only [MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
      MachineSubroutine.configuration, MachineSubroutine.label, state, workingState_loader] using hc
  have reset := resetInTime initialQuery exit state (tapes base s2)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
      (StateTransition.EvalsToInTime.trans _ _ _ _ _ _
        (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ hd hr') hz') hc') reset
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · have hend : tapes base s2 = SourceTestAppend.resultTapes queryLayout base bits :=
      final_tapes base bits h.rank h.rightBase h.leftBase h.zero
    simpa only [hend] using joined.evals_in_steps
  · have hj := joined.steps_le_m
    dsimp only [finishBudget]
    omega

/-- One complete actual clause-tuple execution. The only changed tape is the
reversed-output accumulator; every internal finite register is reset. -/
theorem bodyInTime (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : Arena u Extra → List Bool) (h : Ready F c base) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some main, canonicalState initialQuery, base⟩
      (some ⟨exit, canonicalState initialQuery,
        SourceTestAppend.resultTapes queryLayout base (SourceQueryOrder.tupleBits F u D c)⟩)
      (bodyBudget (D := D) F c)) := by
  have setup := setupInTime F c initialQuery exit base h
  obtain ⟨signature, lastQuery, ⟨loopRun⟩⟩ := prefixInTime F c initialQuery initialQuery
    (canonicalSignature u) exit base h (SlotCount u) (Nat.le_refl _)
  rw [prefixBits_eq_tupleBits] at loopRun
  have finishRun := finishInTime F c initialQuery lastQuery signature exit base h
    (SourceQueryOrder.tupleBits F u D c)
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ setup loopRun) finishRun
  refine ⟨{ toEvalsTo := joined.toEvalsTo, steps_le_m := ?_ }⟩
  have hj := joined.steps_le_m
  dsimp only [bodyBudget]
  omega

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleBody

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceTupleBound
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Uniform polynomial bounds for the actual tuple-body phase budgets.
The budget being bounded is the one used by the checked machine traces. -/

namespace UniqueGamesTheorem.Foundations.Hastad.SourceTupleBound

open Complexity SourceContexts SourceOccurrences SourceTupleBody
open Complexity.MachineComposition

variable {u D : Nat}

theorem clauseRank_le_power (F : Target.Formula) (c : ClauseContext F u) :
    ((clauseEncoding F u).code c).val ≤ (formulaBits F).length ^ u := by
  have hr := ((clauseEncoding F u).code c).isLt
  change _ < F.clauses.length ^ u at hr
  exact hr.le.trans (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_clauses F) u)

theorem variableRank_le_power (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    variableRank F c index ≤ (formulaBits F).length ^ u := by
  have hr := ((variableEncoding F u).code (sampledVariables F c (selected index))).isLt
  change variableRank F c index < F.variables ^ u at hr
  exact hr.le.trans (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_variables F) u)

theorem leftValue_le_numberBound (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    leftValue F c index ≤ SourceBounds.bitCoefficient u * (formulaBits F).length ^ u :=
  (SourceAddressDescriptors.baseValue_lt F u c (sampledVariables F c (selected index)) 0).le.trans
    (SourceBounds.nBits_le_input F u)

theorem rightValue_le_numberBound (F : Target.Formula) (c : ClauseContext F u) :
    rightValue F c ≤ SourceBounds.bitCoefficient u * (formulaBits F).length ^ u :=
  (SourceAddressDescriptors.baseValue_lt F u c (sampledVariables F c (fun _ => .first)) 1).le.trans
    (SourceBounds.nBits_le_input F u)

theorem leftBlock_le_numberBound (F : Target.Formula) :
    2 ^ (2 ^ u) * F.variables ^ u ≤
      SourceBounds.bitCoefficient u * (formulaBits F).length ^ u := by
  apply Nat.le_trans (m := nBits F u)
  · rw [Nat.mul_comm (2 ^ (2 ^ u)) (F.variables ^ u), nBits_eq]
    omega
  · exact SourceBounds.nBits_le_input F u

theorem slotBudget_le (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) :
    slotBudget (D := D) F c index ≤ (slotPolynomial u D).eval (formulaBits F).length := by
  have hr := variableRank_le_power F c index
  have hl := leftValue_le_numberBound F c index
  have hb := SourceBounds.nBits_le_input F u
  have hn := natPolynomial_eval_mono (MachineHorner.timePolynomial u)
    (SourceBounds.formulaBits_length_ge_variables F)
  have ho : SourceBasePhase.operandLength (variableRank F c index) 0 ≤
      (formulaBits F).length ^ u + 2 := by
    simp only [SourceBasePhase.operandLength, encodeWord_length]
    omega
  have ha := natPolynomial_eval_mono (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))) ho
  have hq := Nat.mul_le_mul_left (QueryCount u D)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 9 hb) 21)
  rw [slotPolynomial_eval]
  unfold slotBudget
  omega

theorem prefixBudget_le (F : Target.Formula) (c : ClauseContext F u) (r : Nat) :
    prefixBudget (D := D) F c r ≤ r * (slotPolynomial u D).eval (formulaBits F).length := by
  induction r with
  | zero => simp [prefixBudget]
  | succ r ih =>
    rw [prefixBudget]
    split
    next h =>
      have hs := slotBudget_le (D := D) F c ⟨r, h⟩
      simpa only [Nat.succ_mul] using Nat.add_le_add ih hs
    next _ =>
      simpa only [Nat.add_zero] using ih.trans
        (Nat.mul_le_mul_right ((slotPolynomial u D).eval (formulaBits F).length) (Nat.le_succ r))

noncomputable def bodyPolynomial (u D : Nat) : Polynomial Nat :=
  setupPolynomial u + Polynomial.C (SlotCount u) * slotPolynomial u D + finishPolynomial u

theorem setupBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    setupBudget F c ≤ (setupPolynomial u).eval (formulaBits F).length := by
  have hr := clauseRank_le_power F c
  have hl := leftBlock_le_numberBound (u := u) F
  have hm := natPolynomial_eval_mono (MachineHorner.timePolynomial u)
    (SourceBounds.formulaBits_length_ge_clauses F)
  have ho : SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
      (2 ^ (2 ^ u) * F.variables ^ u) ≤
      (formulaBits F).length ^ u +
        SourceBounds.bitCoefficient u * (formulaBits F).length ^ u + 2 := by
    simp only [SourceBasePhase.operandLength, encodeWord_length]
    omega
  have ha := natPolynomial_eval_mono (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))) ho
  rw [setupPolynomial_eval, preparePolynomial_eval]
  unfold setupBudget
  omega

theorem finishBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    finishBudget F c ≤ (finishPolynomial u).eval (formulaBits F).length := by
  have hr := rightValue_le_numberBound F c
  rw [finishPolynomial_eval]
  unfold finishBudget
  omega

/-- One fixed polynomial bounds the actual tuple-body budget for every tuple. -/
theorem bodyBudget_le (F : Target.Formula) (c : ClauseContext F u) :
    bodyBudget (D := D) F c ≤ (bodyPolynomial u D).eval (formulaBits F).length := by
  have hs := setupBudget_le F c
  have hp := prefixBudget_le (D := D) F c (SlotCount u)
  have hf := finishBudget_le F c
  simp only [bodyPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  unfold bodyBudget
  omega

/-- The actual body execution with the same fixed polynomial for every tuple. -/
theorem bodyInPolynomialTime {Extra : Type} [DecidableEq Extra]
    (F : Target.Formula) (c : ClauseContext F u)
    (initialQuery : Query u D) (exit : Option (Label u D Extra))
    (base : SourceRuntimeModel.Arena u Extra → List Bool) (h : Ready F c base) :
    Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step (program initialQuery exit))
      ⟨some main, SourceRuntimeModel.canonicalState initialQuery, base⟩
      (some ⟨exit, SourceRuntimeModel.canonicalState initialQuery,
        SourceTestAppend.resultTapes SourceRuntimeModel.queryLayout base
          (SourceQueryOrder.tupleBits F u D c)⟩)
      ((bodyPolynomial u D).eval (formulaBits F).length)) := by
  obtain ⟨run⟩ := bodyInTime F c initialQuery exit base h
  exact ⟨{
    toEvalsTo := run.toEvalsTo
    steps_le_m := run.steps_le_m.trans (bodyBudget_le F c)
  }⟩

end UniqueGamesTheorem.Foundations.Hastad.SourceTupleBound

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceGapLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.Foundations.Hastad.SourceGap

section Repetition

open Target SourceContexts SourceOccurrences SourceGame
open UniqueGamesTheorem.Integration.SourceParameters
open UniqueGamesTheorem.Reduction

/-- A clause gap includes nonemptiness: a cross-multiplied inequality alone
would hold vacuously for a formula with no clauses. -/
def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.variables → Bool,
    (η : ℝ) * F.clauses.length ≤
      (PCP.failureCount F assignment (PCP.allIndices F) : ℝ)

theorem repeated_game_bound (F : Formula) (η ξ : ℚ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) (D : ℕ) (hD : 0 < D)
    (hgap : ClauseGap F η) :
    ((baseGame F hgap.1).repetition
      (repetitionCount η ξ hη hη1 hξ D hD)).value ≤
        4 * (D : ℝ)⁻¹ * (ξ : ℝ)^2 := by
  have hb : (baseGame F hgap.1).value ≤ 1 - ((η / 3 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      base_value_le_of_clause_gap F hgap.1 (η : ℝ) hgap.2
  have hc : Fintype.card Bool * Fintype.card PCP.ClauseAnswer = 16 := by
    simp
  exact (game_repetition_rate (baseGame F hgap.1) (third_pos hη)
    (third_le_one hη1) hc hb _).trans
      (repetitionLength_real_bound (η / 3) ξ (third_pos hη)
        (third_le_one hη1) hξ D hD)

/-- The actual nonempty, numbered occurrence list at the fixed parameters. -/
def source (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (F : Formula) : SourceEncoding.Input :=
  sourceInput F (repetitionCount η ξ hη hη1 hξ D hD) D hD

theorem source_complete (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (hnoise : (D : ℚ)⁻¹ ≤ ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits : Fin (source η ξ hη hη1 hξ D hD F).variables → Bool,
      1 - ξ ≤ (((source η ξ hη hη1 hξ D hD F).equations.countP
        (fun e => CloneGap.satisfied e bits) : ℚ) /
          (source η ξ hη hη1 hξ D hD F).equations.length) := by
  obtain ⟨assignment, hs⟩ := hF
  refine ⟨SourceHonest.honestBits F _ assignment, ?_⟩
  have h := SourceHonest.sourceList_honest_acceptance_rat F
    (repetitionCount η ξ hη hη1 hξ D hD) D hD assignment hs
  exact (sub_le_sub_left hnoise 1).trans h

theorem source_sound (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (hDtwo : 2 ≤ D)
    (F : Formula) (hgap : ClauseGap F η)
    (bits : Fin (source η ξ hη hη1 hξ D hD F).variables → Bool) :
    ((source η ξ hη hη1 hξ D hD F).equations.countP
      (fun e => CloneGap.satisfied e bits) : ℚ) /
        (source η ξ hη hη1 hξ D hD F).equations.length ≤ (1 + ξ) / 2 :=
  SourceSoundness.sourceList_sound_rat F hgap.1
    (repetitionCount η ξ hη hη1 hξ D hD) D hD hDtwo ξ hξ.le
      (repeated_game_bound F η ξ hη hη1 hξ D hD hgap) bits

end Repetition

open Target SourceNoiseParameter UniqueGamesTheorem.Reduction

def forError (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    Formula → SourceEncoding.Input :=
  source η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)

theorem forError_complete (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits : Fin (forError η ξ hη hη1 hξ F).variables → Bool,
      1 - ξ ≤ ((forError η ξ hη hη1 hξ F).equations.countP
        (fun e => CloneGap.satisfied e bits) : ℚ) /
          (forError η ξ hη hη1 hξ F).equations.length :=
  source_complete η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)
    (noiseDenominator_inv_le hξ) F hF

theorem forError_sound (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : Formula) (hgap : ClauseGap F η)
    (bits : Fin (forError η ξ hη hη1 hξ F).variables → Bool) :
    ((forError η ξ hη hη1 hξ F).equations.countP
      (fun e => CloneGap.satisfied e bits) : ℚ) /
        (forError η ξ hη hη1 hξ F).equations.length ≤ (1 + ξ) / 2 :=
  source_sound η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)
    (noiseDenominator_ge_two ξ) F hgap bits

end UniqueGamesTheorem.Foundations.Hastad.SourceGap



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorContract

open Target Complexity

abbrev NonemptyFormula := { F : Formula // F.clauses ≠ [] }

def inputEncoding (F : NonemptyFormula) : List Bool := formulaBits F.val

def sourceMap (u D : Nat) (hD : 0 < D) (F : NonemptyFormula) :
    UniqueGamesTheorem.Reduction.SourceEncoding.Input :=
  SourceOccurrences.sourceInput F.val u D hD

def errorMap (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : NonemptyFormula) : UniqueGamesTheorem.Reduction.SourceEncoding.Input :=
  SourceGap.forError η ξ hη hη1 hξ F.val

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorContract



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorProgram

open Turing Complexity SourceGeneratorModel

noncomputable section


abbrev Tape (u D : Nat) := SourceGeneratorModel.Tape u D

local instance instDecidableEqExtra (u D : Nat) : DecidableEq (Extra u D) := Classical.decEq _

inductive Label (u D : Nat)
  | startup (label : SourceStartup.Label u D)
  | body (label : SourceTupleBody.Label u D (Extra u D))
  | check (coordinate : Fin u)
  | reset (coordinate : Fin u)
  | finishEnter
  | finish (label : SourceRuntimeFinish.Label (clearKeys u D))
  deriving DecidableEq, Fintype

def bodyEntry (u D : Nat) : Label u D := .body SourceTupleBody.main

def next (u D : Nat) (i : Nat) : Label u D :=
  if h : i < u then .check ⟨i, h⟩ else .finishEnter

def program (u D : Nat) (hD : 0 < D) :
    Label u D → TM2.Stmt (fun _ : Tape u D => Bool) (Label u D) (State u D)
  | .startup l => SourceTupleBody.framed (sourceStateEquiv u D) Label.startup
      (some (bodyEntry u D)) (SourceStartup.program l)
  | .body l => SourceTupleBody.framed (sourceStateEquiv u D) Label.body
      (some (next u D 0))
      (SourceTupleBody.program (initialQuery u D hD) none l)
  | .check i => MachineTupleOdometer.increment
      (.current i) (.remaining i) (bodyEntry u D) (.reset i)
  | .reset i => MachineTupleOdometer.reset
      (.current i) (.remaining i) (.reset i) (next u D (i.val + 1))
  | .finishEnter => Reduction.MachineTransfer.exitAt (accumulatorTape u D)
      (SourceRuntimeFinish.entry (clearKeys u D) Label.finish)
  | .finish l => SourceRuntimeFinish.statement (clearKeys u D)
      (accumulatorTape u D) (outputTape u D) (initialAmbient u D hD)
      Label.finish none l

def main (u D : Nat) : Label u D := .startup (.inl .inputCopyOut)

def machine (u D : Nat) (hD : 0 < D) : FinTM2 where
  K := Tape u D
  k₀ := .formula
  k₁ := outputTape u D
  Γ _ := Bool
  Λ := Label u D
  main := main u D
  σ := State u D
  initialState := (initialAmbient u D hD, none)
  m := program u D hD

end

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorProgram



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGenerator
open Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram SourceGeneratorContract
noncomputable section
variable {u D : Nat}
local instance instDecidableEqExtra : DecidableEq (Extra u D) := Classical.decEq _

theorem source_initial (u D : Nat) (hD : 0 < D) :
    sourceStateEquiv u D (SourceGeneratorModel.initialState u D hD, ()) =
      (initialAmbient u D hD, none) := rfl

theorem initial_configuration (F : Formula) (hD : 0 < D) :
    initList (SourceGeneratorProgram.machine u D hD) (formulaBits F) =
      (⟨some (SourceGeneratorProgram.main u D), (initialAmbient u D hD, none),
        SourceStartup.initialTapes F⟩ : (SourceGeneratorProgram.machine u D hD).Cfg) := by
  simp only [initList, SourceGeneratorProgram.machine]
  congr 1
  funext k
  by_cases hk : k = SourceContextLoad.Tape.formula
  · subst k
    simp [SourceStartup.initialTapes]
    rfl
  · simp [SourceStartup.initialTapes, hk]

def startupInTime (F : Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      (initList (SourceGeneratorProgram.machine u D hD) (formulaBits F))
      (some ⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩)
      ((SourceStartup.timePolynomial u D).eval (formulaBits F).length) := by
  have run := SourceTupleBody.framedExecution (sourceStateEquiv u D)
    SourceGeneratorProgram.Label.startup (some (bodyEntry u D)) ()
    SourceStartup.program (SourceGeneratorProgram.program u D hD) (fun _ => rfl)
    (SourceStartup.startupInPolynomialTime (u := u) F hm hD)
  rw [initial_configuration F hD]
  simpa only [SourceTupleBody.framedConfiguration, MachineStateFrame.configuration,
    MachineControl.configuration, MachineSubroutine.configuration,
    MachineStateFrame.frameConfiguration, MachineSubroutine.label, source_initial,
    Option.map_some, Option.map_none, id_eq, SourceGeneratorProgram.main,
    FinTM2.step, FinTM2.Cfg, SourceGeneratorProgram.machine] using! run

end
end UniqueGamesTheorem.Foundations.Hastad.SourceGenerator



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorTraversal

open Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceGeneratorProgram SourceOdometerSchedule


noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorTraversal.instDecidableEqExtra
theorem leaf_work_blank (F : Target.Formula) (c : ClauseContext F u) (output : List Bool)
    (role : BodyWork (SourceGeneratorModel.Extra u D))
    (hl : role ≠ .leftBlock) (hd : role ≠ .dummy) (ha : role ≠ .accumulator) :
    leafTapes F c output (workTape role) = [] := by
  change (Function.update (SourceStartup.readyTapes F) (accumulatorTape u D) output)
    (workTape role) = []
  rw [Function.update_of_ne (by simpa [workTape, accumulatorTape] using ha)]
  exact SourceStartup.ready_work_blank F role hl hd ha

/-- Every concrete tuple and arbitrary accumulated prefix satisfies the actual
body's representation invariant after startup. -/
theorem leaf_ready (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    SourceTupleBody.Ready F c (leafTapes (D := D) F c output) := by
  constructor
  · simp [leafTapes, setDigits, setAcc, accumulatorRole]
  · intro i
    simp [leafTapes, setDigits]
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .index = []
    exact SourceStartup.ready_sharedFrame F _ (Or.inl rfl)
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .work = []
    exact SourceStartup.ready_sharedWork F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .scratch = []
    exact SourceStartup.ready_sharedFrame F _ (Or.inr (Or.inl rfl))
  · change (SourceStartup.readyTapes (u := u) (D := D) F) .copyScratch = []
    exact SourceStartup.ready_sharedFrame F _ (Or.inr (Or.inr rfl))
  · intro i s
    simp [leafTapes, setDigits, setAcc, accumulatorRole]
  · change (SourceStartup.readyTapes (u := u) (D := D) F) variableHeader = encodeWord F.variables
    exact SourceStartup.ready_variableHeader F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) clauseHeader = encodeWord F.clauses.length
    exact SourceStartup.ready_clauseHeader F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) (workTape .leftBlock) = _
    exact SourceStartup.ready_leftBlock F
  · change (SourceStartup.readyTapes (u := u) (D := D) F) (workTape .dummy) = _
    simpa only [SourceHeaderCounts.dummyValue, SourceHeaderCounts.leftValue,
      SourceHeaderCounts.rightValue, Nat.mul_comm] using SourceStartup.ready_dummy (u := u) (D := D) F
  all_goals apply leaf_work_blank F c output _ <;> simp

/-- The actual body's accumulator update has exactly the endpoint expected by
the nested odometer schedule. -/
theorem body_result_leaf (F : Target.Formula) (c : ClauseContext F u)
    (output bits : List Bool) :
    SourceTestAppend.resultTapes queryLayout (leafTapes (D := D) F c output) bits =
      leafTapes F c (bits.reverse ++ output) := by
  change setAcc (accumulatorRole u D) (leafTapes F c output)
    (bits.reverse ++ leafTapes F c output (accumulatorTape u D)) = _
  rw [leaf_accumulator]
  unfold leafTapes
  rw [setDigits_setAcc, setAcc_setAcc, ← setDigits_setAcc]

/-- The body-run premise of the odometer is discharged by the checked body
machine and its fixed polynomial bound, in this same final generator program. -/
theorem actual_bodies (F : Target.Formula) (hD : 0 < D) :
    BodyTrace (SourceGeneratorProgram.program u D hD) (bodyEntry u D) (next u D 0)
      (initialAmbient u D hD) (accumulatorRole u D) (SourceStartup.readyTapes F)
      (SourceQueryOrder.tupleBits F u D)
      ((SourceTupleBound.bodyPolynomial u D).eval (formulaBits F).length) := by
  intro c output
  obtain ⟨run⟩ := SourceTupleBound.bodyInPolynomialTime F c (initialQuery u D hD) none
    (leafTapes (D := D) F c output) (leaf_ready F c output)
  have lifted := SourceTupleBody.framedExecution (sourceStateEquiv u D)
    SourceGeneratorProgram.Label.body (some (next u D 0)) ()
    (SourceTupleBody.program (initialQuery u D hD) none)
    (SourceGeneratorProgram.program u D hD) (fun _ => rfl) run
  refine ⟨lifted.steps, lifted.steps_le_m, ?_⟩
  have ht := lifted.evals_in_steps
  change (MachineComposition.advance (TM2.step (SourceGeneratorProgram.program u D hD)))^[lifted.steps]
    _ = _ at ht
  simp only [body_result_leaf] at ht
  simpa only [SourceTupleBody.framedConfiguration, MachineControl.configuration,
    MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, Option.map_some,
    Option.map_none, id_eq, source_initial, configuration,
    bodyEntry, leafTapes] using ht

/-- Startup already supplies exactly the reset odometer digits. -/
theorem resetDigits_ready (F : Target.Formula) :
    setDigits F.clauses.length (fun _ : Fin u => 0)
      (SourceStartup.readyTapes (u := u) (D := D) F) = SourceStartup.readyTapes F := by
  funext k
  cases k <;> simp [setDigits]

theorem allBits_eq_records (F : Target.Formula) (hne : F.clauses ≠ []) :
    allBits (SourceQueryOrder.tupleBits F u D) =
      (sourceList F u D).flatMap (fun e =>
        encodeWords (UniqueGamesTheorem.Reduction.SourceEncoding.equationWords e)) := by
  rw [sourceList_nonempty F u D hne]
  unfold allBits SourceQueryOrder.tupleBits SourceQueryOrder.slotBits
    SourceQueryOrder.occurrenceBits
  simp only [rawSourceList, occurrenceList,
    sourceIndexEncoding, Encoding.enumerate_prod, List.flatMap_map, List.flatMap_assoc,
    clauseEncoding, Encoding.enumerate_fin_function]

/-- Include the exact reversed header already emitted by startup. -/
theorem accumulated_eq_input (F : Target.Formula) (hD : 0 < D) (hne : F.clauses ≠ []) :
    (allBits (SourceQueryOrder.tupleBits F u D)).reverse ++
        SourceStartup.readyTapes F (accumulatorTape u D) =
      (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  rw [allBits_eq_records F hne, SourceStartup.ready_accumulator]
  have hi := SourceLoopOrder.inputBits_eq_header_records (sourceInput F u D hD)
  change UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceInput F u D hD) =
    encodeWords [nBits F u, (sourceList F u D).length] ++
      (sourceList F u D).flatMap (fun e =>
        encodeWords (UniqueGamesTheorem.Reduction.SourceEncoding.equationWords e)) at hi
  rw [hi, List.reverse_append]

theorem traversalOutput_frame (F : Target.Formula) (hD : 0 < D)
    (k : SourceGeneratorModel.Tape u D) (hk : k ≠ accumulatorTape u D) :
    traversalOutput F hD k = SourceStartup.readyTapes F k := by
  simp [traversalOutput, hk]

def resetLabel (u D : Nat) (i : Nat) : SourceGeneratorProgram.Label u D :=
  if h : i < u then .reset ⟨i, h⟩ else .finishEnter

/-- Actual traversal of every clause tuple, with each digit physically reset.
All nonaccumulator tapes have exactly their startup-ready contents. -/
theorem traversalInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (SourceGeneratorProgram.program u D hD))
      ⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩
      (some ⟨some .finishEnter, (initialAmbient u D hD, none), traversalOutput F hD⟩)
      (((SourceTupleBound.bodyPolynomial u D).eval (formulaBits F).length + 2 * u) *
        F.clauses.length ^ u)) := by
  have hne : F.clauses ≠ [] := List.length_pos_iff.mp hm
  obtain ⟨run⟩ := SourceOdometerSchedule.traversalInTime
    (SourceGeneratorProgram.program u D hD) (bodyEntry u D) (next u D) (resetLabel u D)
    (initialAmbient u D hD) (accumulatorRole u D) hm
    ((SourceTupleBound.bodyPolynomial u D).eval (formulaBits F).length)
    (SourceStartup.readyTapes F) (SourceQueryOrder.tupleBits F u D)
    (by intro i hi
        simp only [next, resetLabel, currentAt, remainingAt, hi, ↓reduceDIte]
        rfl)
    (by intro i hi
        simp only [resetLabel, currentAt, remainingAt, hi, ↓reduceDIte]
        rfl)
    (actual_bodies F hD)
  refine ⟨?_⟩
  have hs : initialConfiguration (m := F.clauses.length) u (bodyEntry u D)
      (initialAmbient u D hD) (SourceStartup.readyTapes F) =
      (⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩ :
        TM2.Cfg (fun _ : SourceGeneratorModel.Tape u D => Bool)
          (SourceGeneratorProgram.Label u D) (SourceGeneratorProgram.State u D)) := by
    rw [initialConfiguration, configuration, resetDigits_ready]
  have hf : finalConfiguration (next u D u) (initialAmbient u D hD) (accumulatorRole u D)
      (SourceStartup.readyTapes F) (SourceQueryOrder.tupleBits F u D) =
      (⟨some .finishEnter, (initialAmbient u D hD, none), traversalOutput F hD⟩ :
        TM2.Cfg (fun _ : SourceGeneratorModel.Tape u D => Bool)
          (SourceGeneratorProgram.Label u D) (SourceGeneratorProgram.State u D)) := by
    unfold finalConfiguration configuration
    rw [setDigits_setAcc, resetDigits_ready]
    change (⟨some (next u D u), (initialAmbient u D hD, none),
      setAcc (accumulatorRole u D) (SourceStartup.readyTapes F)
        ((allBits (SourceQueryOrder.tupleBits F u D)).reverse ++
          SourceStartup.readyTapes F (accumulatorTape u D))⟩ :
        TM2.Cfg (fun _ : SourceGeneratorModel.Tape u D => Bool)
          (SourceGeneratorProgram.Label u D) (SourceGeneratorProgram.State u D)) = _
    rw [accumulated_eq_input F hD hne]
    simp only [next, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [hs, hf] using run

def timePolynomial (u D : Nat) : Polynomial Nat :=
  (SourceTupleBound.bodyPolynomial u D + Polynomial.C (2 * u)) * Polynomial.X ^ u

theorem traversalInPolynomialTime (F : Target.Formula)
    (hm : 0 < F.clauses.length) (hD : 0 < D) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step (SourceGeneratorProgram.program u D hD))
      ⟨some (bodyEntry u D), (initialAmbient u D hD, none), SourceStartup.readyTapes F⟩
      (some ⟨some .finishEnter, (initialAmbient u D hD, none), traversalOutput F hD⟩)
      ((timePolynomial u D).eval (formulaBits F).length)) := by
  obtain ⟨run⟩ := traversalInTime F hm hD
  refine ⟨{ toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }⟩
  apply run.steps_le_m.trans
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  exact Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (SourceBounds.formulaBits_length_ge_clauses F) u)

end

end UniqueGamesTheorem.Foundations.Hastad.SourceGeneratorTraversal



namespace UniqueGamesTheorem.Foundations.Hastad.SourceGenerator

open Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram SourceGeneratorContract

noncomputable section


variable {u D : Nat}
local instance instDecidableEqExtra_1 : DecidableEq (Extra u D) := Classical.decEq _

def prefixPolynomial (u D : Nat) : Polynomial Nat :=
  SourceStartup.timePolynomial u D + SourceGeneratorTraversal.timePolynomial u D + 1

def timePolynomial (u D : Nat) (hD : 0 < D) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (SourceGeneratorProgram.machine u D hD)
    (clearKeys u D).length (prefixPolynomial u D)

def beforeFinish (F : Formula) (hD : 0 < D) : (SourceGeneratorProgram.machine u D hD).Cfg :=
  ⟨SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish,
    (initialAmbient u D hD, none), SourceGeneratorTraversal.traversalOutput F hD⟩

def enterFinishInTime (F : Formula) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      ⟨some .finishEnter, (initialAmbient u D hD, none),
        SourceGeneratorTraversal.traversalOutput F hD⟩
      (some (beforeFinish F hD)) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux
      (Reduction.MachineTransfer.exitAt (accumulatorTape u D)
        (SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish))
      _ _) = _
    cases h : SourceRuntimeFinish.entry (clearKeys u D) SourceGeneratorProgram.Label.finish <;>
      simp only [Reduction.MachineTransfer.exitAt, beforeFinish, TM2.stepAux] <;>
      erw [h] <;> rfl
  steps_le_m := Nat.le_refl _

def prefixInTime (F : Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (SourceGeneratorProgram.machine u D hD).step
      (initList (SourceGeneratorProgram.machine u D hD) (formulaBits F))
      (some (beforeFinish F hD)) ((prefixPolynomial u D).eval (formulaBits F).length) := by
  have start := startupInTime (u := u) F hm hD
  let traversal := Classical.choice (SourceGeneratorTraversal.traversalInPolynomialTime
    (u := u) F hm hD)
  have first := StateTransition.EvalsToInTime.trans
    (SourceGeneratorProgram.machine u D hD).step _ _ _ _ _ start traversal
  have joined := StateTransition.EvalsToInTime.trans
    (SourceGeneratorProgram.machine u D hD).step _ _ _ _ _ first (enterFinishInTime F hD)
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply joined.steps_le_m.trans
  simp only [prefixPolynomial, Polynomial.eval_add, Polynomial.eval_one]
  omega

theorem output_empty (F : Formula) (hD : 0 < D) :
    SourceGeneratorTraversal.traversalOutput F hD (outputTape u D) = [] := by
  rw [SourceGeneratorTraversal.traversalOutput_frame F hD _
    (Ne.symm (accumulator_ne_output u D))]
  exact SourceStartup.ready_work_blank F (.extra (.inr ()))
    (by simp) (by simp) (by simp)

theorem halted_configuration (F : Formula) (hD : 0 < D) :
    (⟨none, (initialAmbient u D hD, none),
      SourceRuntimeFinish.canonicalTapes (outputTape u D)
        (SourceGeneratorTraversal.traversalOutput F hD (accumulatorTape u D)).reverse⟩ :
      (SourceGeneratorProgram.machine u D hD).Cfg) =
      haltList (SourceGeneratorProgram.machine u D hD)
        (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (SourceOccurrences.sourceInput F u D hD)) := by
  rw [SourceGeneratorTraversal.traversalOutput_accumulator, List.reverse_reverse]
  simp only [haltList, SourceGeneratorProgram.machine]
  congr 1
  funext k
  by_cases hk : k = outputTape u D
  · subst k
    simp [SourceRuntimeFinish.canonicalTapes]
    erw [Function.update_self]
    rfl
  · simp [SourceRuntimeFinish.canonicalTapes, hk]
    erw [Function.update_of_ne hk]

def outputInTime (F : NonemptyFormula) (hD : 0 < D) :
    TM2OutputsInTime (SourceGeneratorProgram.machine u D hD) (inputEncoding F)
      (some (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)))
      ((timePolynomial u D hD).eval (inputEncoding F).length) := by
  have hm : 0 < F.val.clauses.length := List.length_pos_iff.mpr F.property
  have prefixRun := prefixInTime (u := u) F.val hm hD
  have keepAcc : accumulatorTape u D ∉ clearKeys u D := by
    simp [mem_clearKeys]
  have keepOut : outputTape u D ∉ clearKeys u D := by
    simp [mem_clearKeys]
  have covers : ∀ k, k ≠ accumulatorTape u D → k ≠ outputTape u D → k ∈ clearKeys u D :=
    fun k ha ho => (mem_clearKeys u D k).mpr ⟨ha, ho⟩
  have finish := SourceRuntimeFinish.finishInTime (clearKeys u D)
    (accumulatorTape u D) (outputTape u D) (accumulator_ne_output u D)
    keepAcc keepOut covers (initialAmbient u D hD) SourceGeneratorProgram.Label.finish none
    (SourceGeneratorProgram.program u D hD) (fun _ => rfl)
    (SourceGeneratorTraversal.traversalOutput F.val hD) (output_empty F.val hD)
    (initialAmbient u D hD) none
  erw [halted_configuration F.val hD] at finish
  have joined := SourceRuntimeSpace.prefixAndFinishInTime
    (SourceGeneratorProgram.machine u D hD) (formulaBits F.val) (prefixPolynomial u D)
    prefixRun (clearKeys u D) (accumulatorTape u D) (outputTape u D)
    keepAcc keepOut covers (SourceGeneratorTraversal.traversalOutput F.val hD)
    (output_empty F.val hD) (fun _ => rfl) finish
  exact joined

def computableInPolyTime (u D : Nat) (hD : 0 < D) :
    TM2ComputableInPolyTime inputEncoding UniqueGamesTheorem.Reduction.SourceEncoding.inputBits
      (sourceMap u D hD) where
  tm := SourceGeneratorProgram.machine u D hD
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial u D hD
  outputsFun F := by
    change TM2OutputsInTime (machine u D hD) ((inputEncoding F).map id)
      (some ((UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)).map id)) _
    have input_eq : @List.map ((machine u D hD).Γ (machine u D hD).k₀)
        ((machine u D hD).Γ (machine u D hD).k₀) id (inputEncoding F) =
        inputEncoding F := List.map_id _
    have output_eq : @List.map ((machine u D hD).Γ (machine u D hD).k₁)
        ((machine u D hD).Γ (machine u D hD).k₁) id
        (UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)) =
        UniqueGamesTheorem.Reduction.SourceEncoding.inputBits (sourceMap u D hD F) := List.map_id _
    simpa only [input_eq, output_eq] using outputInTime (u := u) F hD

def forErrorComputableInPolyTime (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    TM2ComputableInPolyTime inputEncoding UniqueGamesTheorem.Reduction.SourceEncoding.inputBits
      (errorMap η ξ hη hη1 hξ) := by
  let D := SourceNoiseParameter.noiseDenominator ξ
  let hD := SourceNoiseParameter.noiseDenominator_pos ξ
  let u := SourceGap.repetitionCount η ξ hη hη1 hξ D hD
  exact computableInPolyTime u D hD

theorem forError_finite_work_alphabets (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (k : (forErrorComputableInPolyTime η ξ hη hη1 hξ).tm.K) :
    Finite ((forErrorComputableInPolyTime η ξ hη hη1 hξ).tm.Γ k) := by
  change Finite Bool
  infer_instance

end

end UniqueGamesTheorem.Foundations.Hastad.SourceGenerator



namespace UniqueGamesTheorem.Foundations.Hastad.SourceNonempty

open Target PCP

/-- Convert an actual natural-number clause-count inequality to the real
inequality used by the clause-variable game. -/
theorem real_clause_gap_of_count (F : Formula) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.variables → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment)
    (assignment : Fin F.variables → Bool) :
    (a : ℝ) / (b : ℝ) * F.clauses.length ≤
      (failureCount F assignment (allIndices F) : ℝ) := by
  rw [NameCompaction.verifier_failureCount]
  have hreal : (a : ℝ) * F.clauses.length ≤
      (b : ℝ) * (NameCompaction.failedCount F assignment : ℝ) := by
    exact_mod_cast hgap assignment
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hb)).mpr
  simpa only [mul_comm] using hreal

theorem clauseGap_of_count (F : Formula) (a b : ℕ) (hne : F.clauses ≠ [])
    (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.variables → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment) :
    SourceGap.ClauseGap F ((a : ℚ) / (b : ℚ)) := by
  refine ⟨hne, fun assignment => ?_⟩
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    real_clause_gap_of_count F a b hb hgap assignment

variable {V E : Type*} {n m : ℕ}

/-- The actual final graph bundle carries a nonempty dart type, so its
explicitly numbered Boolean CNF is nonempty even before using any gap. -/
theorem cnf_nonempty_of_nonempty_darts [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (FinalBooleanVerifier.cnf G vertices edges).clauses ≠ [] := by
  have hcard : Fintype.card E = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr edges
  have hm : 0 < m := hcard ▸ Fintype.card_pos
  exact FinalBooleanVerifier.cnf_nonempty G vertices edges hm

/-- The checked final Boolean-verifier count bound produces exactly the
nonempty clause-gap premise of SourceGap, with denominator `40960 * b`. -/
theorem cnf_clauseGap [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      a * Fintype.card E ≤ b * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      ((a : ℚ) / ((b : ℚ) * 40960)) := by
  have h := clauseGap_of_count (FinalBooleanVerifier.cnf G vertices edges) a (b * 40960)
    (cnf_nonempty_of_nonempty_darts G vertices edges)
    (Nat.mul_pos hb (by decide)) (FinalBooleanVerifier.cnf_gap G vertices edges a b hgap)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- The unit-numerator gap supplied by the final powering stage has the
fixed rational clause gap `1 / (40960 * walkLength)`. -/
theorem cnf_clauseGap_unit [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (walkLength : ℕ)
    (hwalk : 0 < walkLength)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      Fintype.card E ≤ walkLength * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      (1 / (40960 * (walkLength : ℚ))) := by
  have h := cnf_clauseGap G vertices edges 1 walkLength hwalk
    (by simpa only [one_mul] using hgap)
  simpa only [Nat.cast_one, mul_comm] using h

end UniqueGamesTheorem.Foundations.Hastad.SourceNonempty


section

/-!
The actual finite graph iteration used by the mathematical PCP construction.
One fixed, explicitly supplied complete address list is shared by every round.
Each round constructs a new constraint graph. The scalar gap and size are the
actual minimum rejection fraction and actual finite cardinalities of that graph.

The final Boolean formula uses supplied vertex and dart numberings. These
theorems establish the finite objects and their size/gap properties, not a
machine running-time theorem or an independently encoded NP-hardness theorem.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.PCPIteration

theorem finalClauseGap_positive : 0 < finalClauseGap := by
  apply one_div_pos.mpr
  exact mul_pos (by norm_num) (by exact_mod_cast FinalConstants.walkLength_positive)

end UniqueGamesTheorem.Foundations.PCP.PCPIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_FinalTableFormula
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

open Target Complexity

theorem satisfiable_iff (table : GraphTables.Table) :
    (output table).Satisfiable ↔ (GraphTables.semantics table).Satisfiable :=
  (FinalBooleanVerifier.cnf_satisfiable_iff (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _)).trans
      ((GraphTables.semantics table).satisfiable_reindex (Equiv.refl _) (Equiv.refl _)
        FinalCNFPattern.labelEquiv.symm)

theorem nonempty (table : GraphTables.Table) (hd : 0 < table.darts) :
    (output table).clauses ≠ [] :=
  FinalBooleanVerifier.cnf_nonempty _ (Equiv.refl _) (Equiv.refl _) hd

/-- Boolean labels and numeric labels have exactly the same rejected darts. -/
theorem tableGraph_rejectionCount (table : GraphTables.Table)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    (FinalCNFPattern.tableGraph table).rejectionCount labeling =
      (GraphTables.semantics table).rejectionCount
        (fun v => FinalCNFPattern.labelEquiv (labeling v)) := by
  have h := (GraphTables.semantics table).reindex_rejectionCount
    (Equiv.refl _) (Equiv.refl _) FinalCNFPattern.labelEquiv.symm
    (fun v => FinalCNFPattern.labelEquiv (labeling v))
  simpa [FinalCNFPattern.tableGraph, ConstraintGraph.labelingEquiv] using h

/-- A uniform numeric-label count bound transfers to the machine's Boolean-label graph. -/
theorem tableGraph_count_lower (table : GraphTables.Table) (walkLength : Nat)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ walkLength * (GraphTables.semantics table).rejectionCount labeling)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    Fintype.card (Fin table.darts) ≤
      walkLength * (FinalCNFPattern.tableGraph table).rejectionCount labeling := by
  rw [Fintype.card_fin, tableGraph_rejectionCount]
  exact hgap _

theorem clauseGap (table : GraphTables.Table) (hd : 0 < table.darts)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ FinalConstants.walkLength *
        (GraphTables.semantics table).rejectionCount labeling) :
    Hastad.SourceGap.ClauseGap (output table) PCPIteration.finalClauseGap := by
  let : Nonempty (Fin table.darts) := ⟨⟨0, hd⟩⟩
  exact Hastad.SourceNonempty.cnf_clauseGap_unit (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _) FinalConstants.walkLength
    FinalConstants.walkLength_positive (tableGraph_count_lower table _ hgap)

end UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_RawInitialTablesLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace UniqueGamesTheorem.Foundations.PCP.RoundTables

theorem initial_satisfiable_iff (F : Target.Formula) : Satisfiable (initial F) ↔ F.Satisfiable :=
  RawInitialTables.table_satisfiable_iff F

end UniqueGamesTheorem.Foundations.PCP.RoundTables

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_TableIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def output (H : BaseTable) (F : Formula) : Input := run H (iterationCount F) (initial F)

theorem output_val (H : BaseTable) (F : Formula) : (output H F).val = outputTable H F :=
  run_val H (iterationCount F) (initial F)

theorem output_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    Satisfiable (output H F) :=
  run_completeness H _ _ ((initial_satisfiable_iff F).mpr sat)

theorem gapMap_completeness (H : BaseTable) (F : Formula) (sat : F.Satisfiable) :
    (gapMap H F).Satisfiable := by
  apply (FinalTableFormula.satisfiable_iff (outputTable H F)).mpr
  rw [← output_val]
  exact output_completeness H F sat

theorem output_darts_positive (H : BaseTable) (F : Formula) : 0 < (outputTable H F).darts := by
  rw [← output_val]
  exact (output H F).property

theorem gapMap_nonempty (H : BaseTable) (F : Formula) : (gapMap H F).clauses ≠ [] :=
  FinalTableFormula.nonempty (outputTable H F) (output_darts_positive H F)

end UniqueGamesTheorem.Foundations.PCP.TableIteration

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_LoopInitializationLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
The concrete tapes produced by initialization satisfy the row-zero loop
invariant. Execution of initialization is proved separately by
`Initialization.initializeInTime`; this bridge identifies its resulting tapes.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopInitialization

open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel LoopState

/-- The actual initial loop tapes contain the complete unread input rows and
exactly the two output headers in reverse order on the accumulation tape. -/
theorem initialization_ready {q : Nat} (input : GenericGraphTables.Table q) :
    Ready input 0 (Initialization.loopTapes input) where
  le_darts := Nat.zero_le _
  original := rfl
  cursor := by
    change Initialization.rowsBits input = cursorBits input 0
    rw [cursorBits_zero]
    rfl
  vertices := rfl
  darts := rfl
  counter := by simp [Initialization.loopTapes]
  edge := rfl
  tail := rfl
  reverseIndex := rfl
  head := rfl
  scratch := rfl
  compareLeft := rfl
  compareRight := rfl
  output := rfl
  reversed := by
    change (Initialization.headerBits input).reverse = (prefixBits input 0).reverse
    rw [prefixBits_zero]
    rfl

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.LoopInitialization



namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Loop


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

/-- The zero guard preserves all tapes, resets its temporary register, and
enters the actual driver's output-reversal phase in one transition. -/
def zeroGuardInTime (input : GenericGraphTables.Table q) (base : Tape → List Bool)
    (ready : LoopState.Ready input input.darts base)
    (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal relation flag, base⟩
      (some ⟨some .reverseOutput, normal relation flag, base⟩) 1 := by
  have counterSelf : MachineUnaryCounter.counterTapes Tape.counter base 0 [] = base := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil,
      ← ready.counter_at_end, Function.update_eq_self]
  have run := MachineUnaryCounter.guardInTime_zero Tape.counter
    (Driver.Label.guard : Driver.Label q) .tailStart .reverseOutput
    (Driver.program q) (Driver.program_guard q) base [] (normal relation flag).1 none
  simpa only [counterSelf, normal] using run

def runRemaining (input : GenericGraphTables.Table q) :
    (remaining e : Nat) → e + remaining = input.darts →
    (base : Tape → List Bool) → LoopState.Ready input e base →
    (oldRelation : GenericGraphTables.RelationTable q) → (oldFlag : Bool) →
      LoopResult input e remaining base oldRelation oldFlag
  | 0, e, finished, base, ready, oldRelation, oldFlag => by
    have atEnd : e = input.darts := by omega
    subst e
    exact {
      tapes := base
      relation := oldRelation
      flag := oldFlag
      ready := ready
      run := by
        simpa only [Nat.zero_mul, Nat.zero_add] using
          zeroGuardInTime input base ready oldRelation oldFlag }
  | remaining + 1, e, finished, base, ready, oldRelation, oldFlag => by
    have beforeEnd : e < input.darts := by omega
    let edge : Fin input.darts := ⟨e, beforeEnd⟩
    let one := Body.rowStep input edge base ready oldRelation oldFlag
    let rest := runRemaining input remaining (e + 1) (by omega) one.tapes one.ready
      input.rows[edge].relation (CompareLoop.rowLoop input edge)
    let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ one.run rest.run
    refine {
      tapes := rest.tapes
      relation := rest.relation
      flag := rest.flag
      ready := rest.ready
      run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
    have budget := composed.steps_le_m
    simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using budget

/-- No initialization or row trace is assumed: both are instantiated at this
actual finite driver and this input, then composed. -/
def runPrefix (input : GenericGraphTables.Table q) : PrefixResult input := by
  let rows := runRemaining input input.darts 0 (by simp)
    (Initialization.loopTapes input) (LoopInitialization.initialization_ready input)
    (Vector.replicate (q * q) false) false
  let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (Initialization.initializeInTime input) rows.run
  refine {
    tapes := rows.tapes
    relation := rows.relation
    flag := rows.flag
    ready := rows.ready
    run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
  have budget := composed.steps_le_m
  change composed.steps ≤
    input.darts * Body.bodyTime q (LoopState.inputBits input).length + 1 +
      Initialization.time (LoopState.inputBits input).length at budget
  have rowCount : input.darts ≤ (LoopState.inputBits input).length :=
    GenericGraphTables.darts_le_tableBits_length input
  have rowBudget := Nat.mul_le_mul_right (Body.bodyTime q (LoopState.inputBits input).length)
    rowCount
  unfold prefixTime
  omega

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Loop



namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open RuntimeModel


/-- The concrete driver outputs exactly the checked table encoding. -/
noncomputable def tableOutputsInTime {q : Nat} (input : GenericGraphTables.Table q) :
    TM2OutputsInTime (Driver.machine q) (GenericGraphTables.tableBits input)
      (some (GraphTables.tableBits (Table.build input)))
      ((time q).eval (GenericGraphTables.tableBits input).length) := by
  let prefixRun := Loop.runPrefix input
  have hrun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some .reverseOutput, normal prefixRun.relation prefixRun.flag, prefixRun.tapes⟩)
      ((prefixPolynomial q).eval (GenericGraphTables.tableBits input).length) := by
    rw [prefixPolynomial_eval]
    exact prefixRun.run
  exact Finish.finishAfterPolynomialPrefix q (GenericGraphTables.tableBits input)
    prefixRun.tapes (GraphTables.tableBits (Table.build input))
    (normal prefixRun.relation prefixRun.flag) (prefixPolynomial q) hrun
    prefixRun.ready.reversed_at_end prefixRun.ready.output

/-- Fixed q determines one finite machine and one natural polynomial. The
input and output alphabets use the exact shared Bool serialization interfaces. -/
noncomputable def tablePolynomialTime (q : Nat) :
    TM2ComputableInPolyTime (GenericGraphTables.tableBits (q := q))
      GraphTables.tableBits (Table.build (q := q)) where
  tm := Driver.machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time q
  outputsFun input := by
    change TM2OutputsInTime (Driver.machine q)
      ((GenericGraphTables.tableBits input).map id)
      (some ((GraphTables.tableBits (Table.build input)).map id))
      ((time q).eval (GenericGraphTables.tableBits input).length)
    have input_eq :
        @List.map ((Driver.machine q).Γ (Driver.machine q).k₀)
          ((Driver.machine q).Γ (Driver.machine q).k₀) id
          (GenericGraphTables.tableBits input) = GenericGraphTables.tableBits input := List.map_id _
    have output_eq :
        @List.map ((Driver.machine q).Γ (Driver.machine q).k₁)
          ((Driver.machine q).Γ (Driver.machine q).k₁) id
          (GraphTables.tableBits (Table.build input)) =
          GraphTables.tableBits (Table.build input) := List.map_id _
    simpa only [input_eq, output_eq] using tableOutputsInTime input

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Runtime



/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable

open UniqueGamesTheorem.Foundations.Complexity

theorem Runtime.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Runtime.tablePolynomialTime q).tm :=
  Driver.finiteAlphabet q

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable



/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime

open Turing UniqueGamesTheorem.Foundations.Complexity
open PreprocessingRegularTables

/-- Both stages supply complete executions, cleanup, and polynomial bounds;
the sequential composition includes the physical interstage bit transfer. -/
noncomputable def computableInPolyTime (H : PreprocessingTables.BaseTable)
    (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * (d + internalDegree))) (finish H d) := by
  change TM2ComputableInPolyTime _ _
    (fun input => PreprocessingStageMaps.lazy (d + internalDegree)
      (PreprocessingStageMaps.paddedOverlay H d input))
  exact MachineSequential.composeBits (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))

theorem finite_alphabet (H : PreprocessingTables.BaseTable) (d : Nat) (hd : 0 < d) :
    MachineFiniteAlphabet.FiniteAlphabet (computableInPolyTime H d hd).tm :=
  MachineFiniteAlphabet.composeBits
    (MachinePaddedOverlayRuntime.computableInPolyTime H d hd)
    (MachineLazyTableRuntime.computableInPolyTime (d + internalDegree)
      (finish_degree_positive d hd))
    (MachinePaddedOverlayRuntime.finite_alphabet H d hd)
    (MachineLazyTableRuntime.finite_alphabet (d + internalDegree)
      (finish_degree_positive d hd))

end UniqueGamesTheorem.Foundations.PCP.PreprocessingFinishRuntime



/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/
namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingRuntime
open Turing UniqueGamesTheorem.Foundations.Complexity
open PreprocessingRegularTables

noncomputable def tablePolynomialTime (H : PreprocessingTables.BaseTable) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (PortTables.inputBits (ports := PreprocessingTables.degree))
      (PreprocessingTables.output H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := 2 * ((internalDegree + 1) + internalDegree)))
    (fun t => PreprocessingFinishRuntime.finish H (internalDegree + 1)
      (PreprocessingStageMaps.regular H t))
  exact MachineSequential.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

theorem finiteAlphabet (H : PreprocessingTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (tablePolynomialTime H).tm :=
  MachineFiniteAlphabet.composeBits
    (MachineRegularTableRuntime.computableInPolyTime H)
    (PreprocessingFinishRuntime.computableInPolyTime H (internalDegree + 1)
      (Nat.succ_pos internalDegree))
    (MachineRegularTableRuntime.finite_alphabet H)
    (PreprocessingFinishRuntime.finite_alphabet H (internalDegree + 1)
      (Nat.succ_pos internalDegree))

end UniqueGamesTheorem.Foundations.PCP.PreprocessingRuntime



/-!
Actual sequential finite-machine composition for the concrete numbered round.
The initial composition lemma isolates the preprocessing and powering execution
certificates with their shared bit codecs. The final endpoint supplies the
checked powering and alphabet machines, leaving only preprocessing explicit.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RoundComputation

open Turing
open UniqueGamesTheorem.Foundations.Complexity


noncomputable def tablePolynomialTimeOfCertificates (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (fun table => AlphabetTable.Table.build (RoundTables.powered H table))
  exact MachineSequential.composeBits
    (poweredPolynomialTimeOfCertificates H preprocessing powering)
    (AlphabetTable.Runtime.tablePolynomialTime RoundTables.alphabet)

/-- This is a separate work-alphabet fact about the same runtime certificate;
the final alphabet stage has homogeneous Bool tapes. -/
theorem finiteAlphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm)
    (hpowering : MachineFiniteAlphabet.FiniteAlphabet powering.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (tablePolynomialTimeOfCertificates H preprocessing powering).tm :=
  MachineFiniteAlphabet.composeBits
    (poweredPolynomialTimeOfCertificates H preprocessing powering)
    (AlphabetTable.Runtime.tablePolynomialTime RoundTables.alphabet)
    (powered_finiteAlphabet H preprocessing powering hpreprocessing hpowering)
    (AlphabetTable.Runtime.finiteAlphabet RoundTables.alphabet)

/-- Powering and alphabet reduction now use their constructed finite machines.
The only remaining input is an execution certificate for preprocessing. -/
noncomputable def tablePolynomialTime (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) :=
  tablePolynomialTimeOfCertificates H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter)

/-- The same certificate has finite work-tape alphabets whenever the supplied
preprocessing machine does; both later stages supply their own proof. -/
theorem tablePolynomialTime_finite_alphabet (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H)
    (hpreprocessing : MachineFiniteAlphabet.FiniteAlphabet preprocessing.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (tablePolynomialTime H preprocessing).tm :=
  finiteAlphabet H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter) hpreprocessing
    (PoweringMachineRuntime.computableInPolyTime_finite_alphabet
      PreprocessingTables.degree RoundTables.walkParameter)

end UniqueGamesTheorem.Foundations.PCP.RoundComputation

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_TableGapReductionLemmas
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map admits a polynomial-time machine. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem output_gap (F : Formula) (unsat : ¬ F.Satisfiable) :
    FinalConstants.cap ≤ gap (TableIteration.output H F) := by
  have hu : ¬ Satisfiable (initial F) := fun sat => unsat ((initial_satisfiable_iff F).mp sat)
  exact AmplificationIteration.run_reaches_cap (step H) gap FinalConstants.cap
    FinalConstants.cap_positive.le FinalConstants.cap_le_one (RoundTableGap.step_gap H certificate)
    (size (initial F)) (initial F) (gap_nonnegative (initial F))
    (one_le_size_mul_gap (initial F) hu)

theorem output_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : Fin (outputTable H F).vertices → GraphTables.Label) :
    (outputTable H F).darts ≤ FinalConstants.walkLength *
      (GraphTables.semantics (outputTable H F)).rejectionCount labeling := by
  have hp := output_darts_positive H F
  let : Nonempty (Fin (outputTable H F).darts) := ⟨⟨0, hp⟩⟩
  have bound := output_gap H certificate F unsat
  change FinalConstants.cap ≤ (GraphTables.semantics (TableIteration.output H F).val).gap at bound
  rw [output_val] at bound
  have count := ((GraphTables.semantics (outputTable H F)).le_gap_iff FinalConstants.cap).mp bound labeling
  simp only [Fintype.card_fin] at count
  have ht : (0 : ℝ) < FinalConstants.walkLength := Nat.cast_pos.mpr FinalConstants.walkLength_positive
  have divided : ((outputTable H F).darts : ℝ) / FinalConstants.walkLength ≤
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using count
  have multiplied := (div_le_iff₀ ht).mp divided
  exact_mod_cast (show ((outputTable H F).darts : ℝ) ≤ (FinalConstants.walkLength : ℝ) *
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) by
    simpa only [mul_comm] using multiplied)

theorem gapMap_clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (gapMap H F) PCPIteration.finalClauseGap :=
  FinalTableFormula.clauseGap (outputTable H F) (output_darts_positive H F)
    (output_count_gap H certificate F unsat)

end UniqueGamesTheorem.Foundations.PCP.TableGapReduction



namespace UniqueGamesTheorem.Outer.HastadSource

open UniqueGamesTheorem.Foundations Target Complexity PCP
open UniqueGamesTheorem.Reduction ActualSource
open MachineFiniteAlphabet


def success (input : SourceEncoding.Input) (bits : Fin input.variables → Bool) : ℚ :=
  (input.equations.countP (fun e => CloneGap.satisfied e bits) : ℚ) /
    input.equations.length

theorem failure_add_success (input : SourceEncoding.Input)
    (bits : Fin input.variables → Bool) :
    (asSource input).failure bits + success input bits = 1 := by
  have h := SourceProbability.failure_add_satisfaction (asSource input) bits
  rw [show (asSource input).sourceList = input.equations from
    Source.sourceList_ofList input.equations input.nonempty] at h
  exact h

def gapInput (H : RoundTables.BaseTable) (F : Formula) :
    Hastad.SourceGeneratorContract.NonemptyFormula :=
  ⟨TableIteration.gapMap H F, TableIteration.gapMap_nonempty H F⟩

def sourceMap (ξ : ℚ) (hξ : 0 < ξ) :=
  Hastad.SourceGeneratorContract.errorMap PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ

def output (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : SourceEncoding.Input :=
  sourceMap ξ hξ (gapInput H F)

theorem complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits, 1 - ξ ≤ success (output H ξ hξ F) bits := by
  exact Hastad.SourceGap.forError_complete PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ
    (TableIteration.gapMap H F) (TableIteration.gapMap_completeness H F hF)

theorem sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (F : Formula) (hF : ¬ F.Satisfiable)
    (bits : Fin (output H ξ hξ F).variables → Bool) :
    success (output H ξ hξ F) bits ≤ (1 + ξ) / 2 := by
  exact Hastad.SourceGap.forError_sound PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ
    (TableIteration.gapMap H F) (TableGapReduction.gapMap_clauseGap H certificate F hF) bits

noncomputable def roundMachine (H : RoundTables.BaseTable) :=
  RoundComputation.tablePolynomialTime H (PreprocessingRuntime.tablePolynomialTime H)

theorem roundMachine_finite (H : RoundTables.BaseTable) :
    FiniteAlphabet (roundMachine H).tm :=
  RoundComputation.tablePolynomialTime_finite_alphabet H
    (PreprocessingRuntime.tablePolynomialTime H) (PreprocessingRuntime.finiteAlphabet H)

noncomputable def gapMachine (H : RoundTables.BaseTable) :
    Turing.TM2ComputableInPolyTime formulaBits Hastad.SourceGeneratorContract.inputEncoding
      (gapInput H) where
  toTM2ComputableAux :=
    (MachineTableIteration.gapMapCertificate H (roundMachine H)).toTM2ComputableAux
  time := (MachineTableIteration.gapMapCertificate H (roundMachine H)).time
  outputsFun F := (MachineTableIteration.gapMapCertificate H (roundMachine H)).outputsFun F

noncomputable def sourceMachine (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime Hastad.SourceGeneratorContract.inputEncoding
      SourceEncoding.inputBits (sourceMap ξ hξ) :=
  Hastad.SourceGenerator.forErrorComputableInPolyTime PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ

noncomputable def computation (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits (output H ξ hξ) :=
  MachineSequential.composeBits (f := gapInput H) (g := sourceMap ξ hξ)
    (gapMachine H) (sourceMachine ξ hξ)

theorem finiteAlphabet (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (computation H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits (gapMachine H) (sourceMachine ξ hξ)
    (TableIterationFiniteAlphabet.gapMap H (roundMachine H) (roundMachine_finite H))
    (Hastad.SourceGenerator.forError_finite_work_alphabets PCPIteration.finalClauseGap ξ
      PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ)

end UniqueGamesTheorem.Outer.HastadSource

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_SourceIncidence
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Outer.SourceIncidence

open UniqueGamesTheorem.Reduction ActualSource
open UniqueGamesTheorem.Foundations Games Target PCP
open UniqueGamesTheorem.Soundness.IncidenceExtraction
open UniqueGamesTheorem.Clean.IncidenceGap
open scoped BigOperators

noncomputable section

def incidence (S : Source) : Incidence (Fin S.occurrences) (Fin S.variables) where
  name := ActualGame.names S
  rhs i := (S.equation i).rhs

theorem paritySuccess_eq (S : Source) (a : Fin S.variables → Bool) :
    paritySuccess (incidence S) (FiniteDistribution.uniform (Fin S.occurrences)) a =
      (((S.sourceList.countP (fun e => CloneGap.satisfied e a) : ℚ) /
        S.occurrences : ℚ) : ℝ) := by
  unfold paritySuccess
  rw [uniform_probability_eq_expect]
  have hevent (o : Fin S.occurrences) :
      decide (xorTriple (fun i => a ((incidence S).name o i)) = (incidence S).rhs o) =
        S.satisfied a o := by
    have hb : ∀ x y : Bool, decide (x = y) = (x == y) := by decide
    exact hb _ _
  simp_rw [hevent]
  rw [IncidenceProbability.expect_bool_indicator_eq_count_ofFn]
  congr 2
  have hm : List.ofFn (S.satisfied a) =
      S.sourceList.map (fun e => CloneGap.satisfied e a) := by
    simp [Source.sourceList, List.map_ofFn, Function.comp_def]
    rfl
  simp [hm, List.countP_map]

theorem paritySuccess_input (input : SourceEncoding.Input)
    (a : Fin input.variables → Bool) :
    paritySuccess (incidence (HastadSource.asSource input))
      (FiniteDistribution.uniform (Fin (HastadSource.asSource input).occurrences)) a =
      (Clone100.success input.equations a : ℝ) := by
  have h := paritySuccess_eq (HastadSource.asSource input) a
  rw [show (HastadSource.asSource input).sourceList = input.equations from
    Source.sourceList_ofList input.equations input.nonempty] at h
  exact h

def input (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : SourceEncoding.Input :=
  Clone100.clonedInput (HastadSource.output H ξ hξ F)

def source (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : Source := HastadSource.asSource (input H ξ hξ F)

theorem source_distinct (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : (source H ξ hξ F).DistinctNames :=
  Clone100.clonedSource_distinct (HastadSource.output H ξ hξ F)

end
end UniqueGamesTheorem.Outer.SourceIncidence

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_PCP_BinaryParityReduction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.UniqueGamesTheorem.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.UniqueGamesTheorem.Integration.AddressTupleBody.labelFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.UniqueGamesTheorem.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.UniqueGamesTheorem.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Outer.BinaryParityReduction

open UniqueGamesTheorem.Foundations Target Complexity PCP
open UniqueGamesTheorem.Reduction ActualSource
open MachineFiniteAlphabet

noncomputable section

def output (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (word : List Bool) : SourceEncoding.Input :=
  SourceIncidence.input H ξ hξ (BinaryLanguage.totalRename word)

def formulaMachine (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits
      (SourceIncidence.input H ξ hξ) :=
  MachineSequential.composeBits
    (f := HastadSource.output H ξ hξ) (g := Clone100.clonedInput)
    (HastadSource.computation H ξ hξ)
    Explicit.MachineClone100.computation

theorem formulaMachine_finite (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (formulaMachine H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits
    (f := HastadSource.output H ξ hξ) (g := Clone100.clonedInput)
    (HastadSource.computation H ξ hξ)
    Explicit.MachineClone100.computation
    (HastadSource.finiteAlphabet H ξ hξ) Explicit.MachineClone100.finiteAlphabet

def computation (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) SourceEncoding.inputBits
      (output H ξ hξ) :=
  MachineSequential.composeBits
    (f := BinaryLanguage.totalRename) (g := SourceIncidence.input H ξ hξ)
    BinaryInputReduction.computation (formulaMachine H ξ hξ)

theorem computation_finite (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (computation H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits
    (f := BinaryLanguage.totalRename) (g := SourceIncidence.input H ξ hξ)
    BinaryInputReduction.computation (formulaMachine H ξ hξ)
    BinaryInputReduction.computation_finiteAlphabet (formulaMachine_finite H ξ hξ)

theorem complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (word : List Bool) (yes : BinaryLanguage.language word) :
    ∃ a, 1 - ξ ≤ Clone100.success (output H ξ hξ word).equations a := by
  obtain ⟨a, ha⟩ := HastadSource.complete H ξ hξ (BinaryLanguage.totalRename word)
    ((BinaryLanguage.totalRename_satisfiable_iff word).mpr yes)
  refine ⟨Clone100.lift a, ?_⟩
  change 1 - ξ ≤ Clone100.success
    (Clone100.clonedInput (HastadSource.output H ξ hξ (BinaryLanguage.totalRename word))).equations
      (Clone100.lift a)
  rw [Clone100.completeness]
  exact ha

theorem sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (small : ξ < 1 / 100)
    (word : List Bool) (no : ¬ BinaryLanguage.language word)
    (a : Fin (output H ξ hξ word).variables → Bool) :
    Clone100.success (output H ξ hξ word).equations a ≤ 4 / 5 := by
  have hno : ¬ (BinaryLanguage.totalRename word).Satisfiable :=
    fun h => no ((BinaryLanguage.totalRename_satisfiable_iff word).mp h)
  exact Clone100.soundness_four_fifths
    (HastadSource.output H ξ hξ (BinaryLanguage.totalRename word)) ξ small
    (HastadSource.sound H certificate ξ hξ (BinaryLanguage.totalRename word) hno) a

structure Reduction (ξ : ℚ) where
  reduce : List Bool → SourceEncoding.Input
  distinct : ∀ word, (HastadSource.asSource (reduce word)).DistinctNames
  completeness : ∀ word, BinaryLanguage.language word →
    ∃ a, 1 - ξ ≤ Clone100.success (reduce word).equations a
  soundness : ∀ word, ¬ BinaryLanguage.language word →
    ∀ a, Clone100.success (reduce word).equations a ≤ 4 / 5
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    SourceEncoding.inputBits reduce
  finiteAlphabet : FiniteAlphabet computation.tm

theorem exists_reduction (ξ : ℚ) (positive : 0 < ξ) (small : ξ < 1 / 100) :
    Nonempty (Reduction ξ) := by
  obtain ⟨H, certificate⟩ := ExpanderTables.exists_base_table
  exact ⟨⟨output H ξ positive,
    (fun word => SourceIncidence.source_distinct H ξ positive (BinaryLanguage.totalRename word)),
    complete H ξ positive, sound H certificate ξ positive small,
    computation H ξ positive, computation_finite H ξ positive⟩⟩

theorem failure_completeness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (yes : BinaryLanguage.language word) :
    ∃ a, (HastadSource.asSource (R.reduce word)).failure a ≤ ξ := by
  obtain ⟨a, ha⟩ := R.completeness word yes
  refine ⟨a, ?_⟩
  have hsum := HastadSource.failure_add_success (R.reduce word) a
  change _ + Clone100.success (R.reduce word).equations a = 1 at hsum
  linarith

theorem parity_soundness {ξ : ℚ} (R : Reduction ξ) (word : List Bool)
    (no : ¬ BinaryLanguage.language word) :
    UniqueGamesTheorem.Clean.IncidenceGap.parityValue
      (SourceIncidence.incidence (HastadSource.asSource (R.reduce word)))
      (UniqueGamesTheorem.Foundations.Games.FiniteDistribution.uniform
        (Fin (HastadSource.asSource (R.reduce word)).occurrences)) ≤ 4 / 5 := by
  unfold UniqueGamesTheorem.Clean.IncidenceGap.parityValue
  apply Finset.sup'_le
  intro a _
  have hq := R.soundness word no a
  have hreal : (Clone100.success (R.reduce word).equations a : ℝ) ≤ 4 / 5 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).mpr hq)
  exact (SourceIncidence.paritySuccess_input (R.reduce word) a).trans_le hreal

end
end UniqueGamesTheorem.Outer.BinaryParityReduction

end

end OAI
end

section
-- module Solutions.OAIQ086_UG.UniqueGames_Reduction_FromMatrixGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace UniqueGamesTheorem.FromMatrixGap


open UniqueGamesTheorem.Foundations Target
open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Integration
open UniqueGamesTheorem.Reduction
open Explicit

noncomputable section

/-- Choose the parity error only after the matrix tuple length is fixed, then
compose the actual raw-input, matrix-test, and final graph machines. -/
def reduction {ε δ : ℝ} (P : ParameterSelection.OuterParameters ε δ)
    (M : Decoder.MatrixGap.Parameters P.pStar) :
    MachineOutputContract.BinaryGapReduction ε δ := by
  classical
  have hk : 0 < M.k := M.k_pos
  let ξ := Classical.choose (P.exists_parity_error M.k hk)
  have hξspec := Classical.choose_spec (P.exists_parity_error M.k hk)
  have hξ : 0 < ξ := hξspec.1
  have hξsmall : ξ < 1 / 100 := hξspec.2.1
  have hξbudget : ξ < P.epsilon0 / (2 * M.k * P.repetitions) := hξspec.2.2
  let R := Classical.choice (Outer.BinaryParityReduction.exists_reduction ξ hξ hξsmall)
  let matrix := fun input => MachineSingleOrbitBridge.output M.k M.T (R.reduce input)
  let matrixMachine := MachineSequential.composeBits
    (f := R.reduce) (g := MachineSingleOrbitBridge.output M.k M.T)
    R.computation (MachineSingleOrbitBridge.computableInPolyTime M.k M.T)
  have matrixFinite : MachineFiniteAlphabet.FiniteAlphabet matrixMachine.tm :=
    MachineFiniteAlphabet.composeBits
      (f := R.reduce) (g := MachineSingleOrbitBridge.output M.k M.T)
      R.computation (MachineSingleOrbitBridge.computableInPolyTime M.k M.T)
      R.finiteAlphabet (MachineSingleOrbitBridge.workAlphabetFinite M.k M.T)
  have hq : 2 ≤ 2 ^ M.s := Nat.le_self_pow (by have h := M.s_pos; omega) 2
  refine FinishReduction.of_matrix_reduction P hq M.s_pos
    (Encoding.alphabetEquiv M.s).symm matrix ?_ matrixMachine matrixFinite
    ((M.k : ℚ) * ξ + P.pStar / 2)
    (P.matrix_error_budget M.k hk ξ hξbudget.le) ?_ ?_
  · intro input
    exact M.output_translations (Outer.HastadSource.asSource (R.reduce input))
  · intro input yes
    obtain ⟨assignment, hfailure⟩ :=
      Outer.BinaryParityReduction.failure_completeness R input yes
    have h := M.completeness (Outer.HastadSource.asSource (R.reduce input))
      assignment ξ hfailure
    simpa only [matrix, MachineSingleOrbitBridge.output,
      MachineSingleOrbitBridge.SingleAddress.tableOutput, Outer.HastadSource.asSource,
      Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat] using h
  · intro input no
    exact M.sound (Outer.HastadSource.asSource (R.reduce input))
      (R.distinct input) (Outer.BinaryParityReduction.parity_soundness R input no)

end
end UniqueGamesTheorem.FromMatrixGap

end OAI
end


