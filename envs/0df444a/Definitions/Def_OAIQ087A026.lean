-- Prove2me | Definitions.Def_OAIQ087A026
-- name    : OAIQ087A026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:40:01.301695+00:00
-- url     : https://prove2.me/theorems/23b1c327-acc9-4b92-8412-0ba3d023e5d9
-- title:
--   Definitions bundle OAIQ087A026 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 269 declarations of OpenAI's Lean: 111 definitions, 8 inductive types or structures, 1 instance and 149 theorems. The definitions and types are `OAI.MaxCutGames.Foundations.Hastad.SourceBasePhase.program`, `OAI.MaxCutGames.Foundations.Hastad.SourceBasePhase.statement`, `OAI.MaxCutGames.Foundations.Hastad.SourceClauseLookup.lookupInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceClauseLookup.lookupWithSplitInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextClear.Label`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextClear.main`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextClear.program`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextLoad.coordinateInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextLoad.loadInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextLoad.loadUnaryInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextLoad.placedLookupInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextLoad.prefixInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextPrepare.Label`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextPrepare.prepareEntry`, `OAI.MaxCutGames.Foundations.Hastad.SourceGap.ClauseGap`, `OAI.MaxCutGames.Foundations.Hastad.SourceGap.forError`, `OAI.MaxCutGames.Foundations.Hastad.SourceGap.source`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.instDecidableEqExtra`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.instDecidableEqExtra_1`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.prefixPolynomial`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorProgram.Label`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorProgram.bodyEntry`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorProgram.instDecidableEqExtra`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorProgram.main`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorProgram.next`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal.resetLabel`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal.timePolynomial`, `OAI.MaxCutGames.Foundations.Hastad.SourceHeaderCounts.Label`, `OAI.MaxCutGames.Foundations.Hastad.SourceHeaderCounts.afterEval`, `OAI.MaxCutGames.Foundations.Hastad.SourceHeaderCounts.evalStart`, `OAI.MaxCutGames.Foundations.Hastad.SourceHeaderCounts.statement`, `OAI.MaxCutGames.Foundations.Hastad.SourceHeaderCounts.steps`, `OAI.MaxCutGames.Foundations.Hastad.SourceHeaderCounts.timePolynomial`, `OAI.MaxCutGames.Foundations.Hastad.SourceHonest.honestValidJ`, `OAI.MaxCutGames.Foundations.Hastad.SourceLocalEquation.emit`, `OAI.MaxCutGames.Foundations.Hastad.SourceLocalEquation.localInputEncoding`, `OAI.MaxCutGames.Foundations.Hastad.SourceLoopInit.digitInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceLoopInit.digitsInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceLoopInit.headerInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceLoopInit.initializeInTime` and 79 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Games_Parameters`, `MaxCut_Machines_AlphabetBudget`, `MaxCut_PCP_CompletedSampling`, `MaxCut_PCP_ContextClear`, `MaxCut_PCP_ContextLoad`, `MaxCut_PCP_ContextPrepare`, `MaxCut_PCP_DescriptorEmission`, `MaxCut_PCP_EquationEmit`, `MaxCut_PCP_FieldArray`, `MaxCut_PCP_Game`, `MaxCut_PCP_Gap`, `MaxCut_PCP_Generator`, `MaxCut_PCP_HeaderAccumulate`, `MaxCut_PCP_HeaderCounts`, `MaxCut_PCP_LocalEquation`, `MaxCut_PCP_LoopOrder`, `MaxCut_PCP_PoweringOpinionTables`, `MaxCut_PCP_ProfileBridge`, `MaxCut_PCP_SelectedInformation`, `MaxCut_PCP_SelectedJointGame`, `MaxCut_PCP_SelectedProfileBudget`, `MaxCut_PCP_SelectionSequence`, `MaxCut_PCP_TupleBody`.
--
--   **Imports.** It imports the bundles `OAIQ087A014`, `OAIQ087A015`, `OAIQ087A016`, `OAIQ087A017`, `OAIQ087A018` and `OAIQ087A019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A031` and `OAIQ087A032`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A014
import Definitions.Def_OAIQ087A015
import Definitions.Def_OAIQ087A016
import Definitions.Def_OAIQ087A017
import Definitions.Def_OAIQ087A018
import Definitions.Def_OAIQ087A019

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_FieldArray
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceClauseLookup

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition SourceMachine

/-- Read the selected six fields using the already checked scanner. -/
theorem readSixTrace (base : Tape → List Bool) (values : List Nat)
    (hlen : values.length = 6) (suffix : List Bool)
    (hinput : base .work = encodeWords values ++ suffix) :
    (advance (TM2.step program))^[(encodeWords values).length + 7]
      (some ⟨some (readStart 0), ((), none), base⟩) =
      some ⟨none, ((), none),
        SourceFieldArray.sequenceTapes .work fieldDestination base 0 values suffix⟩ := by
  have ht := SourceFieldArray.sequenceTrace .work fieldDestination readStart readLoop none
    program base 0 values suffix (by intro r hr; simp [fieldDestination])
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart r (by omega))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop r (by omega))
    (by simpa [hlen] using atReadDone) hinput () none
  have htime : values.sum + 2 * values.length + 1 = (encodeWords values).length + 7 := by
    rw [encodeWords_length, hlen]
  simpa only [Nat.zero_add, htime] using ht

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
theorem lookupWithSplitTrace (F : Target.Formula) (prior : List (Target.Clause F.«variables»))
    (clause : Target.Clause F.«variables») (after : List (Target.Clause F.«variables»))
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
  have hbits : formulaBits F = encodeWords [F.«variables», F.clauses.length] ++
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
  exact scanReadTrace base F.«variables» F.clauses.length prior clause indexSuffix
    (encodeWords (after.flatMap clauseWords))

/-- A polynomial bound on the actual complete copy/skip/read execution. -/
def lookupWithSplitInTime (F : Target.Formula) (prior : List (Target.Clause F.«variables»))
    (clause : Target.Clause F.«variables») (after : List (Target.Clause F.«variables»))
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

end MaxCutGames.Foundations.Hastad.SourceClauseLookup

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextLoad
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A shared-arena context loader. Its finite program copies each selected
clause index, executes the checked lookup, and clears consumed scratch tapes.
Tuple digits and arbitrary extra tapes are protected throughout. -/

namespace MaxCutGames.Foundations.Hastad.SourceContextLoad

open Turing MaxCutGames.Foundations.Complexity
open MachineComposition

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

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

end MaxCutGames.Foundations.Hastad.SourceContextLoad

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Game
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/
namespace MaxCutGames.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

/-- Exact finite occurrence-list soundness, including arbitrary assignments
to unused padded proof bits and to the dummy bit. -/
theorem sourceList_sound (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℝ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * δ ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => MaxCutGames.Reduction.CloneGap.satisfied e bits) : ℝ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  rw [sourceList_nonempty F u D hne, rawSourceList_acceptance F u D hD]
  have hε : (0 : ℝ) < (D : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hD)
  have hε' : (D : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
    have hd : (2 : ℝ) ≤ D := by exact_mod_cast hDtwo
    simpa only [one_div] using
      (inv_le_inv₀ (Nat.cast_pos.mpr hD) (by norm_num : (0 : ℝ) < 2)).mpr hd
  have h := source_acceptance_le_split F hne u ((D : ℝ)⁻¹) δ
    (fun _ => leftAnchor u) (leftTable F u bits) (rightOracle F u bits)
    hε hε' hδ hvalue
  simpa only [leftTable_answer, rightOracle_answer] using h

/-- The direct uniform reduction consumes rational occurrence fractions. -/
theorem sourceList_sound_rat (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℚ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => MaxCutGames.Reduction.CloneGap.satisfied e bits) : ℚ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  have h := sourceList_sound F hne u D hD hDtwo (δ : ℝ)
    (by exact_mod_cast hδ) hvalue bits
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

end MaxCutGames.Foundations.Hastad.SourceSoundness

end

namespace MaxCutGames.Foundations.Hastad.SourceHonest

open MaxCutGames.Reduction.CloneGap
open MaxCutGames.Reduction.FiniteNoise
open scoped BigOperators

open SourceContexts
open SourceOccurrences

/-- Satisfiability supplies one consistent valid right coordinate in every
clause tuple, including tuples with repeated clauses or variable names. -/
def honestValidJ (F : Target.Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    {j : J u // validJ F c j = true} :=
  ⟨honestJ F c assignment, honestJ_valid F c assignment hs⟩

theorem leftResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) (v : VariableContext F u) :
    leftResponse F u (honestBits F u assignment) v =
      fun f => f (honestI F v assignment) := by
  funext f
  simp only [leftResponse, honestBits_code, honestGlobal, taggedAssignment,
    foldedAnswer_dictator]

theorem rightResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (c : ClauseContext F u) :
    rightResponse F u (honestBits F u assignment) c =
      fun g => g (honestJ F c assignment) := by
  funext g
  cases ha : rightAnchor F c with
  | none =>
    have hf := (rightAnchor_none_iff F c).mp ha (honestJ F c assignment)
    rw [honestJ_valid F c assignment hs] at hf
    cases hf
  | some j₀ =>
    simp only [rightResponse, ha, honestBits_code, honestGlobal, taggedAssignment]
    have ht : (fun h : HalfCube j₀ =>
        extendRestricted (validJ F c) h.val (honestJ F c assignment)) =
        fun h => h.val (honestValidJ F c assignment hs) := by
      funext h
      exact extendRestricted_valid (validJ F c) h.val (honestValidJ F c assignment hs)
    rw [ht]
    exact conditionedFoldedAnswer_dictator (validJ F c) j₀
      (honestValidJ F c assignment hs) g

/-- Every actual occurrence is counted, even when its visible context,
equation, or one of its three addresses repeats. -/
theorem rawSourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((rawSourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (rawSourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  have hc : 0 < F.clauses.length := List.length_pos_iff.mpr hF
  let : Nonempty (Fin F.clauses.length) := ⟨⟨0, hc⟩⟩
  rw [rawSourceList_acceptance F u D hD]
  have heq (c : ClauseContext F u) (s : SlotContext u) :
      testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
        (leftResponse F u (honestBits F u assignment) (sampledVariables F c s))
        (rightResponse F u (honestBits F u assignment) c) = 1 - (D : ℝ)⁻¹ := by
    rw [leftResponse_honest, rightResponse_honest F u assignment hs]
    exact testAcceptance_dictator _ _ _ _ (pi_honest_sampled F c s assignment)
  simp_rw [heq]
  simp only [Fintype.expect_const]

theorem sourceList_honest_acceptance_nonempty (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  rw [sourceList_nonempty F u D hF]
  exact rawSourceList_honest_acceptance F u D hD hF assignment hs

theorem sourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℝ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length := by
  by_cases hF : F.clauses = []
  · rw [sourceList_empty F u D hF]
    simp only [List.countP_cons, List.countP_nil, emptyFormulaEquation_satisfied,
      honestBits_dummy, Bool.not_false, ↓reduceIte,
      Nat.zero_add, Nat.cast_one, List.length_cons, List.length_nil, div_one]
    exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg D))
  · exact (sourceList_honest_acceptance_nonempty F u D hD hF assignment hs).ge

/-- Rational acceptance form used by the finite reduction interface. -/
theorem sourceList_honest_acceptance_rat (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℚ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℚ) /
        (sourceList F u D).length := by
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div] using
    sourceList_honest_acceptance F u D hD assignment hs

end MaxCutGames.Foundations.Hastad.SourceHonest

namespace MaxCutGames.Foundations.Repetition

/-- Induction to the ceiling of the real cutoff repairs the integer-rounding
omission in the printed scalar proof. -/
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

/-- Numerical endpoint of Holenstein's recurrence, with the published constant
6000. This theorem assumes only a concrete scalar recurrence, not any game
value bound. The derivation of that recurrence for games is separate. -/
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

end MaxCutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_SelectedInformation
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete selected-coordinate questions and answer labels for the
side-information inequality. The event is the actual repeated game's selected
success event. -/
namespace MaxCutGames.Foundations.Repetition

/-! The actual full selected-answer and reveal law conditioned on success.
Its factorization is derived from the explicit independent question law. -/
section
open scoped BigOperators
open Games Information

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedJointWeight_nonnegative (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (z) : 0 ≤ selectedJointWeight G strategy selected z := by
  apply div_nonneg
  · exact mul_nonneg
      (mul_nonneg ((selectedInputLaw G selected).nonnegative _)
        ((independentProduct_isProbability _
          (fun i => gameLaw_isProbability (selectedInputProfile G selected z.1.1 i))).1 z.2))
      (selectedLikelihood_nonnegative G strategy selected z.1.1.1 z.1.2 z.2)
  · exact G.selectedSuccess_nonnegative strategy selected

theorem selectedJointWeight_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    IsProbability (selectedJointWeight G strategy selected) := by
  constructor
  · exact selectedJointWeight_nonnegative G strategy selected
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedJointWeight G strategy selected) tv) = 1
    simp_rw [selectedJointWeight_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

def selectedJointLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :=
  toGameLaw (selectedJointWeight G strategy selected)
    (selectedJointWeight_isProbability G strategy selected positive)

end

/-! Exact variation decomposition for the two choices of revealed endpoint.
The support of the actual reveal profiles makes both branch identities valid,
including zero-probability revealed endpoints. -/

/-! Removing one independent reveal from the explicit product law. The
likelihood can be any function of the questions and outside data. -/
section
open scoped BigOperators
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem product_reveal_at (μ : Games.FiniteDistribution (X × Y)) (j : I)
    (r : X ⊕ Y) (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    (∏ i, (revealLaw μ).weight (u i,mergeAt j r rest i)) =
      (if r = Sum.inl (u j).1 then partialRevealWeight μ j rest u / 2 else 0) +
      (if r = Sum.inr (u j).2 then partialRevealWeight μ j rest u / 2 else 0) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [mergeAt_self, mergeAt_other, revealLaw_weight]
  by_cases hl : r = Sum.inl (u j).1 <;> by_cases hr : r = Sum.inr (u j).2 <;>
    simp [hl, hr, partialRevealWeight, revealLaw_weight] <;> ring

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

/-- The variation quantity for the explicit full reveal law equals the
two-branch masked quantity after extracting one reveal coordinate. -/
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

/-! The side-information estimate for the explicit coordinate marginals of
the selected-answer/reveal law, followed by removal of one reveal variable. -/
open scoped BigOperators
open Games Information
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedRawMarginal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (selectedRawMarginal G strategy selected j) := by
  classical
  constructor
  · intro z
    apply Finset.sum_nonneg
    intro u _
    split
    · exact selectedJointWeight_nonnegative G strategy selected (z.1,u)
    · exact le_rfl
  · rw [Fintype.sum_prod_type]
    change (∑ tv, firstMarginal (selectedRawMarginal G strategy selected j) tv) = 1
    simp_rw [selectedRawMarginal_firstMarginal, selectedSideWeight, div_eq_mul_inv]
    rw [← Finset.sum_mul, selectedSideMass_total, mul_inv_cancel₀ positive.ne']

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

end MaxCutGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AlphabetBudget
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.MaxCutGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion of the actual selected-label information bound into the
alphabet budget, followed by finite averaging over unused coordinates. -/

namespace MaxCutGames.Foundations.Repetition

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

omit [DecidableEq Q₁] [DecidableEq Q₂] in
/-- The actual selected-label radius is bounded by the base-two alphabet
budget. The unused-coordinate factor is a real subtraction, as in the scalar
recurrence. -/
theorem selectedInformationRadius_le [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    selectedInformationRadius G strategy selected ≤
      Real.sqrt (((n : ℝ) - selected.card) *
        ((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected))) := by
  have hprob : 1 ≤ 1 / G.selectedSuccess strategy selected := by
    apply (le_div_iff₀ positive).2
    simpa using G.selectedSuccess_le_one strategy selected
  have hbudget := add_le_add (selectedLabels_log_le (A₁ := A₁) (A₂ := A₂) selected ell hell)
    (log_le_logTwo hprob)
  unfold selectedInformationRadius
  rw [← unusedCoordinates_card_real selected]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)

omit [DecidableEq Q₁] [DecidableEq Q₂] in
/-- An actual finite average over all unused coordinates yields the numerical
bound needed by the selected-success recurrence. No sign condition on the
individual errors is required. -/
theorem exists_coordinate_le_information_budget [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell)
    (hselected : selected.card < n)
    (error : {i : Fin n // i ∉ selected} → ℝ)
    (hsum : (∑ j, error j) ≤ 15 * selectedInformationRadius G strategy selected) :
    ∃ j : {i : Fin n // i ∉ selected}, error j ≤ 15 * Real.sqrt
      (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
        ((n : ℝ) - selected.card)) := by
  classical
  have hcard : 0 < Fintype.card {i : Fin n // i ∉ selected} := by
    rw [unusedCoordinates_card]
    exact Nat.sub_pos_of_lt hselected
  let : Nonempty {i : Fin n // i ∉ selected} := Fintype.card_pos_iff.mp hcard
  have hden : 0 < (n : ℝ) - selected.card := by
    rw [← unusedCoordinates_card_real selected]
    exact_mod_cast hcard
  have htotal := hsum.trans (mul_le_mul_of_nonneg_left
    (selectedInformationRadius_le G strategy selected positive ell hell) (by norm_num : (0 : ℝ) ≤ 15))
  rw [sqrt_budget_factor _ _ hden] at htotal
  have havg : (∑ j, error j) ≤ ∑ _j : {i : Fin n // i ∉ selected},
      15 * Real.sqrt
        (((selected.card : ℝ) * ell + logTwo (1 / G.selectedSuccess strategy selected)) /
          ((n : ℝ) - selected.card)) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      unusedCoordinates_card_real, mul_assoc, mul_left_comm] using htotal
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  exact ⟨j, hj⟩

end
end MaxCutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_CompletedSampling
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite local completion after correlated sampling

One independent seed contains the original shared seed and two full response
tables. Its local reads give exactly the mixture of the requested completion
kernels. Applying those kernels contracts total variation. On a diagonal
target the same construction uses one common selected label.
-/

namespace MaxCutGames.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

/-- The completion mixture is derived from actual local table reads. -/
theorem outputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    outputLaw μ γ sL sR L R =
        (μ.product γ).mixture (fun z =>
          (KernelSampling.seedLaw L R).pushforward (fun table =>
            (KernelSampling.readLeft table (z.1.1, sL z.2 z.1.1),
             KernelSampling.readRight table (z.1.2, sR z.2 z.1.2)))) := by
      rw [outputLaw_eq_product_pushforward]
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.readLeft table (q.1, sL seed q.1),
           KernelSampling.readRight table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.read_joint_pushforward L R
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

/-- Completing local outputs incurs no additional total-variation loss. -/
theorem outputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (outputLaw μ γ sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [outputLaw_eq_mixture, ← diagonalLaw_completion_mixture σ L R]
  exact mixture_totalVariation_le _ _ (completionKernel L R)

end Completion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

/-- Supported coordinate repair preserves the exact completion mixture. -/
theorem coordinateOutputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    coordinateOutputLaw μ γ j sL sR L R =
        (μ.product (seedLaw γ L R)).pushforward
          (fun z => (coordinateLeft j sL z.2 z.1.1,
            coordinateRight j sR z.2 z.1.2)) := by
      exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
        (fun z : (X × Y) × Seed Γ X Y S (I → X) (I → Y) =>
          (coordinateLeft j sL z.2 z.1.1, coordinateRight j sR z.2 z.1.2))).symm
    _ = (μ.product γ).mixture (fun z =>
        (KernelSampling.seedLaw L R).pushforward (fun table =>
          (KernelSampling.completedLeft j table (z.1.1, sL z.2 z.1.1),
           KernelSampling.completedRight j table (z.1.2, sR z.2 z.1.2)))) := by
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.completedLeft j table (q.1, sL seed q.1),
           KernelSampling.completedRight j table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.completed_joint_pushforward L R j hL hR
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

theorem coordinateOutputLaw_eq_outputLaw
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R = outputLaw μ γ sL sR L R := by
  rw [coordinateOutputLaw_eq_mixture μ γ j sL sR L R hL hR, outputLaw_eq_mixture]

theorem coordinateOutputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (coordinateOutputLaw μ γ j sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [coordinateOutputLaw_eq_outputLaw μ γ j sL sR L R hL hR]
  exact outputLaw_totalVariation_le μ γ sL sR L R σ

end

end MaxCutGames.Foundations.Repetition.CompletedSampling

/-!
Local embedding to single-game strategy transfer for Holenstein's argument.
The embedding law below is explicitly sampled from a finite shared seed and
the base game's actual joint question law. Its distance from the desired
conditioned law is an explicit total-variation expression. Constructing an
embedding with a sufficiently small distance is a separate proof obligation.
-/

/-! An explicit finite shared sampler followed by supported local completion
gives the coordinate success bound. No embedding-existence premise remains. -/
namespace MaxCutGames.Foundations.Repetition
open scoped BigOperators
open Games CorrelatedSampling
noncomputable section
variable {Q₁ Q₂ A₁ A₂ S : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype S]
  [Nonempty A₁] [Nonempty A₂] [Nonempty S]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq S] {n : Nat}

theorem coordinate_probability_le_value_of_local_completion
    (G : Game Q₁ Q₂ A₁ A₂) (j : Fin n)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (σ : FiniteDistribution ((Q₁ × Q₂) × S))
    (profileL : Q₁ → FiniteDistribution S) (profileR : Q₂ → FiniteDistribution S)
    (completionL : Q₁ × S → FiniteDistribution (Fin n → Q₁))
    (completionR : Q₂ × S → FiniteDistribution (Fin n → Q₂))
    (supportL : ∀ q xs, (completionL q).weight xs ≠ 0 → xs j = q.1)
    (supportR : ∀ q ys, (completionR q).weight ys ≠ 0 → ys j = q.1)
    (fallback : S) :
    (σ.mixture (fun z => (completionL (z.1.1,z.2)).product
      (completionR (z.1.2,z.2)))).probability (G.coordinateWin strategy j) ≤
      G.value +
        (2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
         2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)) := by
  let targetLaw := σ.mixture (fun z => (completionL (z.1.1,z.2)).product (completionR (z.1.2,z.2)))
  let δ := 2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
    2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)
  change targetLaw.probability (G.coordinateWin strategy j) ≤ G.value + δ
  by_contra h
  have gap : 0 < targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ) :=
    sub_pos.mpr (lt_of_not_ge h)
  let η := (targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ)) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨N,hN⟩ := samplerOutputLaw_arbitrarily_close σ G.questions profileL profileR fallback η hη
  let thresholds := sharedProfileThresholds profileL profileR
  let γ := traceSeedLaw (rectangleDistribution (α := S) thresholds) N
  let sL := samplerLocal thresholds profileL fallback N
  let sR := samplerLocal thresholds profileR fallback N
  have hvariation := CompletedSampling.coordinateOutputLaw_totalVariation_le
    G.questions γ j sL sR completionL completionR supportL supportR σ
  have hclose : (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw ≤ δ + η :=
    hvariation.trans hN
  have hsuccess := G.coordinate_probability_le_value_add_embedding_distance j targetLaw
    (CompletedSampling.seedLaw γ completionL completionR)
    (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)
    (CompletedSampling.coordinateLeft_preserves j sL)
    (CompletedSampling.coordinateRight_preserves j sR) strategy
  have hsym : targetLaw.totalVariation
      (G.localEmbeddingLaw (CompletedSampling.seedLaw γ completionL completionR)
        (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)) =
      (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw := by
    unfold FiniteDistribution.totalVariation
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    exact abs_sub_comm _ _
  rw [hsym] at hsuccess
  dsimp [η] at hclose
  linarith

end
end MaxCutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_SelectedJointGame
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Identification of the auxiliary selected-answer/reveal law with the actual
repeated-game question law conditioned on selected-coordinate success.
The proof sums out answer labels and reveal «variables» before merging the
selected and unselected question coordinates.
-/

namespace MaxCutGames.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedJointLaw_question_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedJointLaw G strategy selected positive).probability
      (fun z => event (selectedQuestionTuple selected z.1.1.1 z.2)) =
        ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
          event := by
  classical
  erw [FiniteDistribution.probability_condition]
  change
    (∑ z : (SelectedInput Q₁ Q₂ selected ×
        SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
          ({i : Fin n // i ∉ selected} → Q₁ × Q₂),
      if event (selectedQuestionTuple selected z.1.1.1 z.2)
      then selectedJointWeight G strategy selected z else 0) =
        (G.repetition n).questions.probability
          (fun q => G.selectedWins strategy selected q && event q) /
            G.selectedSuccess strategy selected
  calc
    _ = (∑ tv : SelectedInput Q₁ Q₂ selected ×
          SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
        (selectedInputLaw G selected).weight tv.1 *
          ∑ u, independentProduct
            (fun i => (selectedInputProfile G selected tv.1 i).weight) u *
              selectedLikelihood G strategy selected tv.1.1 tv.2 u *
                (if event (selectedQuestionTuple selected tv.1.1 u) then 1 else 0)) /
        G.selectedSuccess strategy selected := by
      conv_lhs => rw [Fintype.sum_prod_type]
      simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tv _
      apply Finset.sum_congr rfl
      intro u _
      cases he : event (selectedQuestionTuple selected tv.1.1 u) <;>
        simp [selectedJointWeight, div_eq_mul_inv, mul_assoc]
    _ = _ := by rw [selectedJoint_eventMass]

end
end MaxCutGames.Foundations.Repetition

/-! Conditioning bounds for the actual repeated-game question marginals.
The likelihood and its normalizer are derived from the selected-win event.
The final estimate retains only the unselected coordinates. -/

/-! The common data used by the two local simulators is the actual
selected-answer law with only the embedded coordinate's reveal removed. -/
namespace MaxCutGames.Foundations.Repetition
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

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_fullReveal_isProbability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    IsProbability (fullRevealMarginal G.questions j
      (selectedOutsideLikelihood G strategy selected)) := by
  have h := isProbability_comp_equiv
    (selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm
    _ (selectedRawMarginal_isProbability G strategy selected positive j)
  have he : (fun z => selectedRawMarginal G strategy selected j
      ((selectedObservationEquiv (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected).symm z)) =
      fullRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected) := by
    funext z
    exact selectedRawMarginal_fullReveal G strategy selected j z
  rw [he] at h
  exact h

def selectedCommonLaw (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j × (Q₁ × Q₂)) :=
  toGameLaw (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
    (partialRevealMarginal_isProbability G.questions j _
      (selected_fullReveal_isProbability G strategy selected positive j))

end
end MaxCutGames.Foundations.Repetition

/-! Conditional common-data profiles, with their error measured against the
actual endpoint-reveal reference and the actual question marginal. -/

namespace MaxCutGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem swap_question_pushforward_snd (μ : FiniteDistribution (X × Y)) :
    ((μ.transport (Equiv.prodComm X Y)).pushforward Prod.snd) = μ.pushforward Prod.fst := by
  rw [FiniteDistribution.transport_eq_pushforward, FiniteDistribution.pushforward_comp]
  rfl

omit [Fintype S] in
theorem leftRevealModel_swap [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (z : S × (Y × X)) :
    leftRevealModel (μ.transport (Equiv.prodComm X Y))
      (fun z => p (swapQuestionEndpoints z)) z = rightRevealModel μ p (swapQuestionEndpoints z) := by
  rcases z with ⟨s,y,x⟩
  change (∑ x', p (s,(x',y))) *
      (revealProfile (μ.transport (Equiv.prodComm X Y)) (Sum.inl y)).weight (y,x) =
    (∑ x', p (s,(x',y))) * (revealProfile μ (Sum.inr y)).weight (x,y)
  rw [revealProfile_inl_diagonal, revealProfile_inr_diagonal, swap_question_pushforward_snd]

theorem rightCommonProfile_error [DecidableEq X] [DecidableEq Y]
    (p : S × (X × Y) → ℝ) (μ : FiniteDistribution (X × Y)) (fallback : S → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) :
    totalVariation p (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1) ≤
      totalVariation p (rightRevealModel μ p) + totalVariation (secondMarginal p) μ.weight := by
  let e := swapQuestionEndpoints (S := S) (X := X) (Y := Y)
  let p' : S × (Y × X) → ℝ := fun z => p (e z)
  let μ' := μ.transport (Equiv.prodComm X Y)
  have h := leftCommonProfile_error p' μ' fallback (isProbability_comp_equiv e p hp) hf
  have hc : leftRevealModel μ' p' = fun z => rightRevealModel μ p (e z) := by
    funext z
    exact leftRevealModel_swap p μ z
  have hd : (fun z : S × (Y × X) => μ'.weight z.2 * leftCommonProfile p' fallback z.2.1 z.1) =
      fun z => μ.weight (e z).2 * rightCommonProfile p fallback (e z).2.2 (e z).1 := rfl
  rw [hc, hd] at h
  change totalVariation (fun z => p (e z)) _ ≤
    totalVariation (fun z => p (e z)) _ + _ at h
  rw [totalVariation_comp_equiv e p (rightRevealModel μ p)] at h
  rw [totalVariation_comp_equiv e p
    (fun z => μ.weight z.2 * rightCommonProfile p fallback z.2.2 z.1)] at h
  have hm : totalVariation (secondMarginal p') μ'.weight =
      totalVariation (secondMarginal p) μ.weight := by
    change totalVariation (fun yx => secondMarginal p ((Equiv.prodComm Y X) yx))
      (fun yx => μ.weight ((Equiv.prodComm Y X) yx)) = _
    exact totalVariation_comp_equiv (Equiv.prodComm Y X) _ _
  rw [hm] at h
  exact h

end
end MaxCutGames.Foundations.Repetition

/-! The two actual conditional common-data profiles used by the shared
sampler, with explicit normalized default laws on all null inputs. -/
namespace MaxCutGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedProfileFallback (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).pushforward Prod.fst

def selectedLeftProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (x : Q₁) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (leftCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight x)
    (leftCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) x)

def selectedRightProfile (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) (y : Q₂) :
    FiniteDistribution (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  toGameLaw
    (rightCommonProfile (selectedCommonLaw G strategy selected positive j).weight
      (selectedProfileFallback G strategy selected positive j).weight y)
    (rightCommonProfile_isProbability _ _
      (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
      (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j)) y)

def selectedLeftProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

def selectedRightProfileError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  totalVariation (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

theorem selectedLeftProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedLeftProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (leftRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  leftCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

theorem selectedRightProfileError_le (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedRightProfileError G strategy selected positive j ≤
      totalVariation (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))
        (rightRevealModel G.questions
          (partialRevealMarginal G.questions j (selectedOutsideLikelihood G strategy selected))) +
      totalVariation (secondMarginal (selectedCommonLaw G strategy selected positive j).weight)
        G.questions.weight :=
  rightCommonProfile_error _ G.questions _
    (gameLaw_isProbability (selectedCommonLaw G strategy selected positive j))
    (gameLaw_isProbability (selectedProfileFallback G strategy selected positive j))

def selectedSamplingTarget (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Q₁ × Q₂) × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
  (selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)

theorem selectedSamplingTarget_left_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedLeftProfile G strategy selected positive j z.1.1).weight z.2) =
      selectedLeftProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

theorem selectedSamplingTarget_right_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedRightProfile G strategy selected positive j z.1.2).weight z.2) =
      selectedRightProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

end
end MaxCutGames.Foundations.Repetition

/-! The common-data law has exactly the actual selected-event question marginal.
Removing the fair endpoint reveal and regrouping the outside data preserve
the embedded question pair. -/

namespace MaxCutGames.Foundations.Repetition

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

theorem selectedRawMarginal_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedRawMarginal G strategy selected j) =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  classical
  funext q
  calc
    _ = (selectedJointLaw G strategy selected positive).probability
        (fun z => decide (z.2 j = q)) := by
      simp only [secondMarginal, selectedRawMarginal, FiniteDistribution.probability,
        selectedJointLaw, toGameLaw, Fintype.sum_prod_type, decide_eq_true_eq]
    _ = ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q)) := by
      have h := selectedJointLaw_question_probability G strategy selected positive
        (fun questions => decide ((questions.1 j.1,questions.2 j.1) = q))
      simpa [selectedQuestionTuple, mergeCoordinates, j.property] using h
    _ = _ := by
      rw [FiniteDistribution.weight_eq_probability_singleton, selectedQuestionMarginal,
        FiniteDistribution.probability_pushforward]

/-- The exact marginal identification needed to use the conditioned-question
information bound in the two local common-data profile errors. -/
theorem selectedCommonLaw_secondMarginal (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    secondMarginal (selectedCommonLaw G strategy selected positive j).weight =
      (selectedQuestionMarginal G strategy selected positive j.1).weight := by
  change secondMarginal (partialRevealMarginal G.questions j
    (selectedOutsideLikelihood G strategy selected)) = _
  rw [partialRevealMarginal_secondMarginal, selectedFullReveal_secondMarginal]
  exact selectedRawMarginal_secondMarginal G strategy selected positive j

end
end MaxCutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_SelectedProfileBudget
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedEmbeddingError (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) : ℝ :=
  2 * selectedLeftProfileError G strategy selected positive j +
    2 * selectedRightProfileError G strategy selected positive j

theorem selectedLeftProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedLeftProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedLeftProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hleft := selected_leftReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedRightProfileError_sum [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedRightProfileError G strategy selected positive j) ≤
      3 * selectedInformationRadius G strategy selected := by
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset {i : Fin n // i ∉ selected})) =>
      selectedRightProfileError_le G strategy selected positive j)
  simp_rw [selectedCommonLaw_secondMarginal] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have hright := selected_rightReveal_error_sum G strategy selected positive
  have hquestion := selectedQuestionMarginal_error_sum G strategy selected positive
  change (∑ j : {i : Fin n // i ∉ selected},
    Information.totalVariation (selectedQuestionMarginal G strategy selected positive j.1).weight
      G.questions.weight) ≤ _ at hquestion
  linarith

theorem selectedEmbeddingError_sum_le_fifteen [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected) :
    (∑ j : {i : Fin n // i ∉ selected}, selectedEmbeddingError G strategy selected positive j) ≤
      15 * selectedInformationRadius G strategy selected := by
  have hl := selectedLeftProfileError_sum G strategy selected positive
  have hr := selectedRightProfileError_sum G strategy selected positive
  have hn : 0 ≤ selectedInformationRadius G strategy selected := Real.sqrt_nonneg _
  simp only [selectedEmbeddingError, Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith

end
end MaxCutGames.Foundations.Repetition

/-! The selected-success likelihood factors into a fixed verifier check and
two separate tests on the local deterministic answers. -/

/-! The actual sum-tagged reveal law separates into local endpoint factors.
The fair reveal probability is retained in those factors. -/
namespace MaxCutGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

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
end MaxCutGames.Foundations.Repetition

/-!
Actual local completions of the unused questions, conditioned on common data
and the player's own embedded question. The raw row factors are explicit
finite weights. Their normalization reconstructs the actual selected common
law, including zero rows. The fallback independently samples base marginal
questions and then inserts the local input at the embedded coordinate.
-/

namespace MaxCutGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

/-- Pointwise factorization of the actual selected common-data row. -/
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

theorem selectedCommonLaw_completion_row_mass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) :
    (selectedCommonLaw G strategy selected positive j).weight (s,xy) =
      ∑ lr : ({i : Fin n // i ∉ selected} → Q₁) ×
          ({i : Fin n // i ∉ selected} → Q₂),
        selectedCompletionScale G strategy selected j s xy *
          selectedLeftRaw G strategy selected j s xy.1 lr.1 *
          selectedRightRaw G strategy selected j s xy.2 lr.2 := by
  classical
  change (∑ u, if u j = xy then partialRevealWeight G.questions j s.2 u *
    selectedOutsideLikelihood G strategy selected s.1 u else 0) = _
  rw [← (completionTupleEquiv (I := {i : Fin n // i ∉ selected})
    (X := Q₁) (Y := Q₂)).sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  exact (selected_completion_factorization G strategy selected j s xy
    (fun i => (u i).1) (fun i => (u i).2)).symm

/-- Actual common-row mass times the two local completion probabilities is
the selected partial-reveal weight with its actual coordinate indicator. -/
theorem selected_completion_row_recombine (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂)
    (l : {i : Fin n // i ∉ selected} → Q₁)
    (r : {i : Fin n // i ∉ selected} → Q₂) :
    (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
      ((selectedLeftCompletion G strategy selected j s xy.1).product
        (selectedRightCompletion G strategy selected j s xy.2)).weight (l,r) =
      if (l j,r j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (l i,r i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (l i,r i))
      else 0 := by
  rw [selectedCommonLaw_completion_row_mass]
  calc
    _ = selectedCompletionScale G strategy selected j s xy *
        selectedLeftRaw G strategy selected j s xy.1 l *
        selectedRightRaw G strategy selected j s xy.2 r :=
      factorized_completion_row
        (selectedLeftRaw G strategy selected j s xy.1)
        (selectedRightRaw G strategy selected j s xy.2)
        (selectedLeftRaw_nonnegative G strategy selected j s xy.1)
        (selectedRightRaw_nonnegative G strategy selected j s xy.2)
        (updatedTableFallback (G.questions.pushforward Prod.fst) j xy.1)
        (updatedTableFallback (G.questions.pushforward Prod.snd) j xy.2)
        (selectedCompletionScale G strategy selected j s xy) (l,r)
    _ = _ := selected_completion_factorization G strategy selected j s xy l r

end
end MaxCutGames.Foundations.Repetition

/-! The actual local completion mixture reproduces the repeated question law
conditioned on the selected wins. All hidden coordinates and reveal «variables»
are explicitly summed out. -/

namespace MaxCutGames.Foundations.Repetition
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

theorem selected_completion_event_row (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ xy : Q₁ × Q₂, (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
      ((selectedFullLeftCompletion G strategy selected j (xy.1,s)).product
        (selectedFullRightCompletion G strategy selected j (xy.2,s))).probability event) =
    ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
      partialRevealWeight G.questions j s.2 u *
        selectedOutsideLikelihood G strategy selected s.1 u *
          (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
  classical
  have hpoint (xy : Q₁ × Q₂)
      (lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂)) :
      (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
        ((selectedLeftCompletion G strategy selected j s xy.1).product
          (selectedRightCompletion G strategy selected j s xy.2)).weight lr =
      if (lr.1 j,lr.2 j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (lr.1 i,lr.2 i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (lr.1 i,lr.2 i)) else 0 :=
    selected_completion_row_recombine G strategy selected positive j s xy lr.1 lr.2
  simp_rw [selected_full_completion_probability, Finset.mul_sum, ← mul_assoc,
    hpoint]
  have hsum (xy : Q₁ × Q₂) :
      (∑ lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂),
        (if (lr.1 j,lr.2 j) = xy then
          partialRevealWeight G.questions j s.2 (fun i => (lr.1 i,lr.2 i)) *
            selectedOutsideLikelihood G strategy selected s.1 (fun i => (lr.1 i,lr.2 i)) else 0) *
          (if event (selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i))) then 1 else 0)) =
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        (if u j = xy then partialRevealWeight G.questions j s.2 u *
          selectedOutsideLikelihood G strategy selected s.1 u else 0) *
            (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
    exact ((completionTupleEquiv (I := {i : Fin n // i ∉ selected})
      (X := Q₁) (Y := Q₂)).sum_comp _).symm
  simp_rw [hsum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul]
  simp

def selectedFullCompletionMixture (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)) :=
  ((selectedCommonLaw G strategy selected positive j).transport (Equiv.prodComm _ _)).mixture
    (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
      (selectedFullRightCompletion G strategy selected j (z.1.2,z.2)))

theorem selectedFullCompletionMixture_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedFullCompletionMixture G strategy selected positive j).probability event =
      ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability event := by
  erw [FiniteDistribution.probability_condition]
  rw [selectedFullCompletionMixture, FiniteDistribution.probability_mixture]
  simp only [FiniteDistribution.transport]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          partialRevealWeight G.questions j s.2 u *
            selectedOutsideLikelihood G strategy selected s.1 u *
              (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      exact selected_completion_event_row G strategy selected positive j s event
    _ = _ := selected_partial_event_total G strategy selected j event

/-- Exact equality with the actual repeated-game question law conditioned on
the selected wins, derived by summing the local completion rows. -/
theorem selectedFullCompletionMixture_eq_conditionedQuestions (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedFullCompletionMixture G strategy selected positive j =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.weight_eq_probability_singleton]
  exact selectedFullCompletionMixture_probability G strategy selected positive j _

end
end MaxCutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_SelectionSequence
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Repetition.SelectionSequence

/-- Construct the scalar sequence from actual selected-set probabilities. -/
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

open MaxCutGames.Foundations.Games

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
variable [Nonempty A₁] [Nonempty A₂]

/-- Apply the proved scalar estimate to the success of an actual repeated-game
strategy. The conditional-coordinate bound is the sole game-theoretic premise. -/
theorem repetition_success_le_of_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hcoordinate : ConditionalCoordinateBound G n strategy ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  have hpositive : ∀ S : Finset (Fin n), S.card < n →
      0 < G.selectedSuccess strategy S →
      ∃ j, j ∉ S ∧ SetStep (G.selectedSuccess strategy) v ell S j := by
    intro S hcard hp
    obtain ⟨j, hj, hbound⟩ := hcoordinate S hcard hp
    refine ⟨j, hj, ?_⟩
    change G.selectedSuccess strategy (insert j S) ≤ _
    rw [G.selectedSuccess_insert strategy S j hp]
    exact mul_le_mul_of_nonneg_left
      (hbound.trans (add_le_add hvalue (le_refl _))) (le_of_lt hp)
  obtain ⟨p, hp0, hpnonneg, hpmono, hrec, hpn⟩ :=
    exists_scalar_sequence (G.selectedSuccess strategy) v ell
      (G.selectedSuccess_empty strategy) (G.selectedSuccess_nonnegative strategy)
      (G.selectedSuccess_antitone strategy) hpositive
  have hbound := scalar_bound_6000 p n
    (G.value_nonnegative.trans hvalue) hv1 hell hp0 hpnonneg hpmono hrec
  rw [hpn, G.selectedSuccess_univ strategy] at hbound
  exact hbound

end MaxCutGames.Foundations.Repetition.SelectionSequence

/-! Quantitative parallel repetition for actual finite two-player games.
The coordinate bound is derived from the explicitly conditioned question law,
finite reveal «variables», information estimates, shared rejection sampler,
and normalized local completions. The scalar recurrence is then applied to
the actual repeated strategy's success probability. -/
namespace MaxCutGames.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_coordinate_probability_le_value_add_error
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
      (G.coordinateWin strategy j.1) ≤
        G.value + selectedEmbeddingError G strategy selected positive j := by
  classical
  let : Nonempty (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
    finiteDistribution_nonempty (selectedProfileFallback G strategy selected positive j)
  have h := coordinate_probability_le_value_of_local_completion G j.1 strategy
    (selectedSamplingTarget G strategy selected positive j)
    (selectedLeftProfile G strategy selected positive j)
    (selectedRightProfile G strategy selected positive j)
    (selectedFullLeftCompletion G strategy selected j)
    (selectedFullRightCompletion G strategy selected j)
    (selectedFullLeftCompletion_support G strategy selected j)
    (selectedFullRightCompletion_support G strategy selected j)
    (Classical.choice inferInstance)
  have htarget : (selectedSamplingTarget G strategy selected positive j).mixture
      (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
        (selectedFullRightCompletion G strategy selected j (z.1.2,z.2))) =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive :=
    selectedFullCompletionMixture_eq_conditionedQuestions G strategy selected positive j
  rw [htarget, selectedSamplingTarget_left_error, selectedSamplingTarget_right_error] at h
  exact h

theorem holenstein_conditionalCoordinateBound
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (ell : ℝ)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    SelectionSequence.ConditionalCoordinateBound G n strategy ell := by
  intro selected hcard positive
  obtain ⟨j,hj⟩ := exists_coordinate_le_information_budget G strategy selected positive ell
    halphabet hcard (selectedEmbeddingError G strategy selected positive)
    (selectedEmbeddingError_sum_le_fifteen G strategy selected positive)
  exact ⟨j.1,j.property,
    (selected_coordinate_probability_le_value_add_error G strategy selected positive j).trans
      (add_le_add le_rfl hj)⟩

/-- Holenstein's explicit constant-6000 repetition estimate, for the actual
success probability of every finite deterministic repeated strategy. -/
theorem holenstein_repetition_success
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).success strategy ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) :=
  SelectionSequence.repetition_success_le_of_conditionalCoordinateBound G n strategy
    hvalue hv hell (holenstein_conditionalCoordinateBound G n strategy ell halphabet)

/-- Quantitative parallel repetition of the actual maximum game value.
There is no repetition, embedding, information-budget, or independence premise. -/
theorem holenstein_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    {v ell : ℝ} (hvalue : G.value ≤ v) (hv : v < 1) (hell : 1 ≤ ell)
    (halphabet : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    (G.repetition n).value ≤
      (1 - (1 - v)^3 / 6000)^((n : ℝ) / ell) := by
  apply ((G.repetition n).value_le_iff _).2
  intro strategy
  exact holenstein_repetition_success G n strategy hvalue hv hell halphabet

end
end MaxCutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Parameters
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Integration.SourceParameters

theorem logTwo_sixteen : MaxCutGames.Foundations.Repetition.logTwo 16 = 4 := by
  unfold MaxCutGames.Foundations.Repetition.logTwo
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  simp [hlog]

/-- The actual finite game's repetition rate, with its answer cardinality
checked as an ordinary finite count. No repetition estimate is assumed. -/
theorem game_repetition_rate {Q₁ Q₂ A₁ A₂ : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
    [Nonempty A₁] [Nonempty A₂] [DecidableEq Q₁] [DecidableEq Q₂]
    (G : MaxCutGames.Foundations.Games.Game Q₁ Q₂ A₁ A₂)
    {gap : ℚ} (hgap : 0 < gap) (hgap1 : gap ≤ 1)
    (hcards : Fintype.card A₁ * Fintype.card A₂ = 16)
    (hvalue : G.value ≤ 1 - (gap : ℝ)) (n : Nat) :
    (G.repetition n).value ≤ (rate gap : ℝ) ^ n := by
  have hg : (0 : ℝ) < gap := by exact_mod_cast hgap
  have halphabet : MaxCutGames.Foundations.Repetition.logTwo
      ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ 4 := by
    rw [← Nat.cast_mul, hcards]
    exact logTwo_sixteen.le
  have h := MaxCutGames.Foundations.Repetition.holenstein_repetition_value
    G n hvalue (by linarith) (by norm_num : (1 : ℝ) ≤ 4) halphabet
  simp only [sub_sub_cancel] at h
  exact h.trans (four_bit_rate_comparison hgap hgap1 n)

end MaxCutGames.Integration.SourceParameters

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ProfileBridge
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

def reindexProfile (u : ℕ) (profile : MachineFieldProfile.Profile (positionEncoding u).size) :
    NameProfile u :=
  fun p q => profile ((positionEncoding u).code p) ((positionEncoding u).code q)

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

end MaxCutGames.Foundations.Hastad.SourceProfileBridge

namespace MaxCutGames.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open MaxCutGames.Foundations.Complexity

abbrev ProfileLabel (u : ℕ) := MachineFieldProfile.Label (MachineFieldProfile.allPairs (Width u))

inductive Label (u : ℕ)
  | profile (label : ProfileLabel u)
  | commit
  deriving DecidableEq, Fintype

variable {u : ℕ} {Extra τ : Type}

theorem place_injective : Function.Injective (place (u := u) (Extra := Extra)) := by
  intro a b h
  have h' := congrArg unplace h
  simpa only [unplace_place, Option.some.injEq] using h'

variable [DecidableEq Extra]

theorem fill_update (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool)
    (k : MachineFieldProfile.Tape (Width u)) (value : List Bool) :
    fill base (Function.update localTapes k value) =
      Function.update (fill base localTapes) (place k) value := by
  funext a
  cases hu : unplace a with
  | none =>
    have hne : a ≠ place k := by
      intro h
      rw [h, unplace_place] at hu
      contradiction
    simp only [fill, hu, Function.update_of_ne hne]
  | some j =>
    have ha := place_unplace a j hu
    rw [← ha]
    by_cases h : j = k
    · subst j
      simp only [fill_place]
      simp [Function.update]
    · have hne : place (Extra := Extra) j ≠ place k := fun h' => h (place_injective h')
      simp only [fill_place, Function.update_of_ne h, Function.update_of_ne hne]

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

/-- Reassociate finite registers without adding a transition. -/
def signStateEquiv (u : ℕ) (τ : Type) :
    SourceSignLoad.State u (ProfileState u × τ) ≃ State u τ where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

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

omit [DecidableEq Extra] in
/-- Unary sign fields may retain arbitrary old suffixes: only the leading
sign bit is read. -/
theorem loaded_sign_field (F : Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (p : Position u) :
    SourceContextLoad.stageTapes F c base u (polarityField p) =
      encodeWord (if positiveAt (clauseAt F (c p.1)) p.2 then 1 else 0) ++
        base (polarityField p) := by
  have ho := SourceContextLoad.output_polarity F c base p.1 (slotEncoding.code p.2)
  change SourceContextLoad.stageTapes F c base u (polarityField p) =
    encodeWord (if F.clauses[(c p.1).val][(slotEncoding.code p.2).val].positive then 1 else 0) ++
      base (polarityField p) at ho
  rw [ho]
  rcases p with ⟨t, s⟩
  cases s <;> rfl

end MaxCutGames.Foundations.Hastad.SourceSignaturePrepare

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextPrepare
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceContextPrepare

open Turing MaxCutGames.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

abbrev Label (u : Nat) := SourceContextLoad.Label u ⊕ SourceSignaturePrepare.Label u

variable {u : Nat} {Extra τ : Type}

def prepareEntry (u : Nat) : SourceSignaturePrepare.Label u :=
  .profile (MachineFieldProfile.labelAt
    (MachineFieldProfile.allPairs (SourceSignaturePrepare.Width u)) 0 0)

end MaxCutGames.Foundations.Hastad.SourceContextPrepare

namespace MaxCutGames.Foundations.Hastad.SourceLoopInit

open Turing MaxCutGames.Foundations.Complexity
open MachineComposition SourceMachine

variable {u : Nat} {Extra : Type}

variable [DecidableEq Extra]

def headerInTime (F : Target.Formula) (base : Tape u Extra → List Bool)
    (hformula : base .formula = formulaBits F) (hwork : base .work = [])
    (hscratch : base .scratch = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .inputCopyOut, ((), register), base⟩
      (some ⟨some (labelAt 0), ((), none), headerOutput F base⟩)
      (3 * (formulaBits F).length + 6) := by
  have copying := MachineCopy.copyInTime .formula .work .scratch
    (by simp) (by simp) (by simp) false .inputCopyOut .inputCopyBack (some (readStart 0))
    program rfl rfl base hscratch () register
  have hc : Function.update base .work (base .formula ++ base .work) = copiedInput base := by
    simp [copiedInput, hwork]
  rw [hc] at copying
  have reading := SourceFieldArray.sequenceInTime .work headerDestination readStart readLoop
    (some .clearWork) program (copiedInput base) 0 [F.«variables», F.clauses.length]
    (encodeWords (F.clauses.flatMap clauseWords))
    (by intro r hr; simp [headerDestination, variableHeader, clauseHeader]; split <;> simp)
    (by intro r hr; simpa only [Nat.zero_add] using atReadStart (u := u) (Extra := Extra) r (by simpa using hr))
    (by intro r hr; simpa only [Nat.zero_add] using atReadLoop (u := u) (Extra := Extra) r (by simpa using hr))
    (by simpa using (atReadDone (u := u) (Extra := Extra)))
    (by simp [copiedInput, hformula, formulaBits, formulaWords, encodeWords, List.append_assoc]) () none
  have draining := MachineDrain.drainInTime .work .clearWork (some (labelAt 0))
    program rfl (readOutput F base) () none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copying reading) draining
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [clear_readOutput] using joined.evals_in_steps
  · apply Nat.le_trans joined.steps_le_m
    rw [readOutput_work, hformula]
    have he : (formulaBits F).length = F.«variables» + F.clauses.length + 2 +
        (encodeWords (F.clauses.flatMap clauseWords)).length := by
      simp [formulaBits, formulaWords, encodeWords, Nat.add_assoc]
      omega
    simp only [List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
    omega

def digitInTime (j : Fin u) (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : base (.current j) = []) (hremaining : base (.remaining j) = [])
    (hscratch : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.seed j), ((), none), base⟩
      (some ⟨some (labelAt (j.val + 1)), ((), none), digitOutput j m base⟩)
      (2 * m + 6) := by
  let seeded := Function.update base (.current j) (encodeWord 0)
  have seedRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.seed j), ((), none), base⟩
      (some ⟨some (.digitCopyOut j), ((), none), seeded⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (.seed j), ((), none), base⟩ = _
    simp [program, TM2.step, TM2.stepAux, seeded, hcurrent, encodeWord]
  have copying := MachineCopy.copyInTime clauseHeader (.remaining j) .copyScratch
    (by simp [clauseHeader]) (by simp [clauseHeader]) (by simp)
    false (.digitCopyOut j) (.digitCopyBack j) (some (.trim j)) program rfl rfl seeded
    (by simpa [seeded] using hscratch) () none
  let copied := Function.update seeded (.remaining j) (encodeWord m)
  have he : Function.update seeded (.remaining j)
      (seeded clauseHeader ++ seeded (.remaining j)) = copied := by
    have hcount' : base (.extra (.inl .clauseCount)) = encodeWord m := hcount
    simp [copied, seeded, clauseHeader, hremaining, hcount']
  rw [he] at copying
  have trimRun : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.trim j), ((), none), copied⟩
      (some ⟨some (labelAt (j.val + 1)), ((), none), digitOutput j m base⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (.trim j), ((), none), copied⟩ = _
    have hn : m = (m - 1) + 1 := by omega
    have htail : (encodeWord m).tail = encodeWord (m - 1) := by
      conv_lhs => rw [hn]
      simp [encodeWord, List.replicate_succ]
    simp [program, TM2.step, TM2.stepAux, copied, seeded, digitOutput, htail]
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ seedRun copying) trimRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hs : seeded clauseHeader = encodeWord m := by simpa [seeded, clauseHeader] using hcount
  rw [hs, encodeWord_length]
  omega

def prefixInTime (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = [])
    (hscratch : base .copyScratch = []) (r : Nat) (hr : r ≤ u) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨some (labelAt r), ((), none), stageTapes m base r⟩)
      (r * (2 * m + 6)) := by
  induction r with
  | zero => exact { steps := 0, evals_in_steps := rfl, steps_le_m := by omega }
  | succ r ih =>
    have hru : r < u := by omega
    let j : Fin u := ⟨r, hru⟩
    let before := stageTapes m base r
    have one := digitInTime j m hm before
      (by dsimp only [before]; rw [stageTapes_frame _ _ _ _ (by simp [clauseHeader]) (by simp [clauseHeader])]; exact hcount)
      (by simp [before, stageTapes_current, j, hcurrent])
      (by simp [before, stageTapes_remaining, j, hremaining])
      (by dsimp only [before]; rw [stageTapes_frame _ _ _ _ (by simp) (by simp)]; exact hscratch)
    have one' : StateTransition.EvalsToInTime (TM2.step program)
        ⟨some (labelAt r), ((), none), before⟩
        (some ⟨some (labelAt (r + 1)), ((), none), stageTapes m base (r + 1)⟩)
        (2 * m + 6) := by
      simpa only [labelAt, dite_eq_left hru, j, stageTapes, before] using one
    have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
      (ih (by omega)) one'
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using joined

def digitsInTime (m : Nat) (hm : 0 < m) (base : Tape u Extra → List Bool)
    (hcount : base clauseHeader = encodeWord m)
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = [])
    (hscratch : base .copyScratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labelAt 0), ((), none), base⟩
      (some ⟨none, ((), none), stageTapes m base u⟩)
      (u * (2 * m + 6) + 1) := by
  have initialRun := prefixInTime m hm base hcount hcurrent hremaining hscratch u (Nat.le_refl _)
  have doneRun : StateTransition.EvalsToInTime (TM2.step (program (Extra := Extra)))
      ⟨some (labelAt u), ((), none), stageTapes m base u⟩
      (some ⟨none, ((), none), stageTapes m base u⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change TM2.step program ⟨some (labelAt u), ((), none), stageTapes m base u⟩ = _
    simp only [labelAt, Nat.lt_irrefl, ↓reduceDIte]
    rfl
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ initialRun doneRun

def initializeInTime (F : Target.Formula) (hm : 0 < F.clauses.length)
    (base : Tape u Extra → List Bool) (hformula : base .formula = formulaBits F)
    (hwork : base .work = []) (hscratch : base .scratch = []) (hcopy : base .copyScratch = [])
    (hclauseHeader : base clauseHeader = [])
    (hcurrent : ∀ j, base (.current j) = []) (hremaining : ∀ j, base (.remaining j) = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .inputCopyOut, ((), none), base⟩
      (some ⟨none, ((), none), outputTapes F base⟩)
      ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) := by
  have firstRun := headerInTime F base hformula hwork hscratch none
  have hcount : headerOutput F base clauseHeader = encodeWord F.clauses.length := by
    simp [headerOutput, hclauseHeader]
  have secondRun := digitsInTime F.clauses.length hm (headerOutput F base) hcount
    (by intro j; rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hcurrent j)
    (by intro j; rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hremaining j)
    (by rw [headerOutput_frame _ _ _ (by simp) (by simp [variableHeader])
      (by simp [clauseHeader])]; exact hcopy)
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ firstRun secondRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans joined.steps_le_m
  have hL := SourceContextLoad.clauses_length_le_input F
  have hb : u * (2 * F.clauses.length + 6) ≤ u * (2 * (formulaBits F).length + 6) :=
    Nat.mul_le_mul_left u (by omega)
  have he : (2 * u + 3) * (formulaBits F).length + 6 * u + 7 =
      u * (2 * (formulaBits F).length + 6) + 3 * (formulaBits F).length + 7 := by
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm, Nat.mul_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [he]
  omega

end MaxCutGames.Foundations.Hastad.SourceLoopInit

namespace MaxCutGames.Foundations.Hastad.SourceRankPhase

open Turing Complexity
open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceAddressArithmetic

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

def statement (slots : MachineHorner.Layout width ↪ K)
    (labels : MachineHorner.Label width → Λ) (exit : Option Λ) :
    MachineHorner.Label width → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineHorner.statement (reverseSlots slots) labels exit

def program (slots : MachineHorner.Layout width ↪ K) :
    MachineHorner.Label width → TM2.Stmt (fun _ : K => Bool)
      (MachineHorner.Label width) (MachineHorner.State σ) :=
  statement slots id none

variable {u : Nat} {Extra : Type}

theorem selectedDigits_loaded (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (controls : Fin 6 ↪ Extra) (base : SourceContextLoad.Tape u Extra → List Bool)
    (empty : ∀ i, base (SourceContextLoad.variableField i (slotEncoding.code (selected i))) = [])
    (i : Fin u) :
    SourceContextLoad.stageTapes F c base u (variableSlots controls selected (.inr i)) =
      encodeWord (sampledVariables F c selected i).val := by
  erw [variableSlots_digit, SourceContextLoad.output_variable, empty i, List.append_nil]
  congr 1
  cases hs : selected i <;> simp [sampledVariables, PCP.nameAt, PCP.clauseAt, slotEncoding, hs] <;> rfl

end MaxCutGames.Foundations.Hastad.SourceRankPhase

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_LocalEquation
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open MaxCutGames.Reduction.CloneGap
open MaxCutGames.Reduction.FiniteNoise

def localInputEncoding (u D : ℕ) : Encoding (LocalInput u D) :=
  (signatureEncoding u).prod (testTapeEncoding u D)

def emit (u D : ℕ) (p : LocalInput u D) : Equation (LocalKey u) :=
  equation u D p.1 p.2

theorem sourceEquation_eq_map_emit (F : Formula) (u D : ℕ)
    (p : SourceIndex F u D) :
    sourceEquation F u D p =
      mapEquation (addressMap F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (emit u D (ofContext F p.1.1 p.1.2, p.2)) :=
  contextEquation_eq_map F u D p.1.1 p.1.2 p.2

end MaxCutGames.Foundations.Hastad.SourceLocalEquation

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

namespace MaxCutGames.Foundations.Hastad.SourceAddressDescriptors

open Target SourceContexts SourceOccurrences SourceLocalEquation SourceLocalSignature
open SourceAddressArithmetic
open MaxCutGames.Reduction.CloneGap

theorem sourceEquation_words (F : Formula) (u D : ℕ) (p : SourceIndex F u D) :
    MaxCutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D p) =
      words (baseValue F u p.1.1 (sampledVariables F p.1.1 p.1.2))
        (mapEquation (descriptor u) (emit u D (ofContext F p.1.1 p.1.2, p.2))) := by
  rw [sourceEquation_eq_map_emit]
  simp only [MaxCutGames.Reduction.SourceEncoding.equationWords, words, mapEquation]
  rw [realize_descriptor, realize_descriptor, realize_descriptor]
  rfl

end MaxCutGames.Foundations.Hastad.SourceAddressDescriptors

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_EquationEmit
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Emit one fixed descriptor equation from three preserved unary base registers.
The output order is first address, second address, third address, RHS. The actual
stack program emits those fields in reverse order. -/

namespace MaxCutGames.Foundations.Hastad.SourceEquationEmit

open Turing Complexity
open SourceAddressDescriptors
open MaxCutGames.Reduction.CloneGap
open MaxCutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

theorem equationTrace (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement sources destination scratch e labels exit label)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps values e]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
  have hw (written : List Nat) (side : Fin 3) :
      prefixTapes destination base written (sources side) = encodeWord (values side) := by
    rw [prefixTapes_other _ _ _ _ (sourceDestination side), sourceWords side]
  have hs (written : List Nat) : prefixTapes destination base written scratch = [] := by
    rw [prefixTapes_other _ _ _ _ (Ne.symm destinationScratch), scratchEmpty]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩ := by
    change some (TM2.stepAux (p (labels .seed)) (ambient, register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      prefixTapes, encodeWords, List.append_nil]
  have hthird : (MachineComposition.advance (TM2.step p))^[2 * values e.third.1 + 5]
      (some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩) =
      some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.third.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.third.2
      (labels .thirdDrain) (labels .thirdFork) (labels .thirdEmit) (some (labels .secondDrain))
      p (atLabels .thirdDrain) (atLabels .thirdFork) (atLabels .thirdEmit)
      (prefixTapes destination base [rhsBit e]) (values e.third.1)
      (hw _ _) (hs _) ambient register
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hsecond : (MachineComposition.advance (TM2.step p))^[2 * values e.second.1 + 5]
      (some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩) =
      some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.second.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.second.2
      (labels .secondDrain) (labels .secondFork) (labels .secondEmit) (some (labels .firstDrain))
      p (atLabels .secondDrain) (atLabels .secondFork) (atLabels .secondEmit)
      (prefixTapes destination base [realize values e.third, rhsBit e]) (values e.second.1)
      (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hfirst : (MachineComposition.advance (TM2.step p))^[2 * values e.first.1 + 5]
      (some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.first.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.first.2
      (labels .firstDrain) (labels .firstFork) (labels .firstEmit) exit
      p (atLabels .firstDrain) (atLabels .firstFork) (atLabels .firstEmit)
      (prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e])
      (values e.first.1) (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, words, rhsBit, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  rw [show steps values e = (2 * values e.first.1 + 5) +
      ((2 * values e.second.1 + 5) + ((2 * values e.third.1 + 5) + 1)) by
        unfold steps; omega]
  rw [Function.iterate_add_apply _ (2 * values e.first.1 + 5),
    Function.iterate_add_apply _ (2 * values e.second.1 + 5),
    Function.iterate_add_apply _ (2 * values e.third.1 + 5), hseed, hthird, hsecond, hfirst]

end MaxCutGames.Foundations.Hastad.SourceEquationEmit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_DescriptorEmission
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceDescriptorEmission

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open MaxCutGames.Reduction.CloneGap
open MaxCutGames.Foundations.Complexity

variable {K Λ : Type} [DecidableEq K]

/-- Executable state equality is obtained from the explicit radix code. -/
instance localInputDecidableEq (u D : ℕ) : DecidableEq (LocalInput u D) :=
  fun x y =>
    if h : (localInputEncoding u D).code x = (localInputEncoding u D).code y then
      isTrue ((localInputEncoding u D).code.injective h)
    else isFalse (fun hxy => h (congrArg (localInputEncoding u D).code hxy))

end MaxCutGames.Foundations.Hastad.SourceDescriptorEmission

namespace MaxCutGames.Foundations.Hastad.SourceTestEmit

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit
open MaxCutGames.Reduction.CloneGap
open Complexity

abbrev Label (u D : ℕ) := Unit ⊕ (LocalInput u D × SourceEquationEmit.Label)

def localEquation (u D : ℕ) (state : LocalInput u D) : Equation Descriptor :=
  mapEquation (descriptor u) (SourceLocalEquation.emit u D state)

def bodyLabel (u D : ℕ) (state : LocalInput u D) (label : SourceEquationEmit.Label) :
    Label u D := .inr (state, label)

end MaxCutGames.Foundations.Hastad.SourceTestEmit

namespace MaxCutGames.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceAddressDescriptors SourceEquationEmit SourceTestEmit

inductive Label (u D : Nat)
  | test (label : SourceTestEmit.Label u D)
  | append
  deriving DecidableEq, Fintype

def equationBits (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : List Bool :=
  encodeWords (words values (localEquation u D state))

def steps (u D : Nat) (values : Fin 3 → Nat) (state : LocalInput u D) : Nat :=
  SourceEquationEmit.steps values (localEquation u D state) + 1 +
    (equationBits u D values state).length + 1

variable {K Λ : Type} [DecidableEq K]

def bodyLabel (u D : Nat) (labels : Label u D → Λ) (state : LocalInput u D)
    (label : SourceEquationEmit.Label) : Λ :=
  labels (.test (SourceTestEmit.bodyLabel u D state label))

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
          (MaxCutGames.Reduction.SourceEncoding.equationWords (sourceEquation F u D occurrence)))⟩)
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
    have hl := MaxCutGames.Reduction.SourceEncoding.equationBits_length_le
      (sourceEquation F u D occurrence)
    rw [sourceEquation_words] at hl
    unfold steps SourceEquationEmit.steps equationBits
    dsimp only [localEquation] at he hl ⊢
    omega

end MaxCutGames.Foundations.Hastad.SourceTestAppend

/-! An actual fixed finite traversal of all query/noise tapes. The finite
control contains one branch for each prescribed tape. The input-dependent
signature and the three address bases remain in registers throughout. -/

namespace MaxCutGames.Foundations.Hastad.SourceQueryLoop

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

inductive Label (u D n : Nat)
  | load (index : Fin (n + 1))
  | emit (index : Fin n) (label : SourceTestAppend.Label u D)
  deriving DecidableEq, Fintype

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

def prefixBits (u D : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u) : Nat → List Bool
  | 0 => []
  | n + 1 => prefixBits u D queries values signature n ++
      SourceTestAppend.equationBits u D values (signature, queries n)

def prefixSteps (u D : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixSteps u D queries values signature n +
      (SourceTestAppend.steps u D values (signature, queries n) + 1)

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

theorem prefixSteps_le (u D n B : Nat) (queries : Nat → Query u D)
    (values : Fin 3 → Nat) (signature : Signature u)
    (hbound : ∀ i, i < n → SourceTestAppend.steps u D values (signature, queries i) ≤ B) :
    prefixSteps u D queries values signature n ≤ n * (B + 1) := by
  induction n with
  | zero => simp [prefixSteps]
  | succ n ih =>
    have hp := ih (fun i hi => hbound i (by omega))
    have hb := hbound n (by omega)
    rw [prefixSteps, Nat.succ_mul]
    omega

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

end MaxCutGames.Foundations.Hastad.SourceQueryLoop

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_LoopOrder
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaxCutGames.Foundations.Hastad.SourceLoopOrder

open Complexity Complexity.MachineTupleOdometer
open Target SourceContexts SourceOccurrences
open MaxCutGames.Reduction

/-- Total extension of the declared tape decoder, for the query loop's natural
index register. Out-of-range values are never visited by that loop. -/
def rankedQuery (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (i : ℕ) : SourceQueryLoop.Query u D :=
  if h : i < (testTapeEncoding u D).size then
    (testTapeEncoding u D).code.symm ⟨i, h⟩
  else fallback

theorem rankedQuery_at (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (i : Fin (testTapeEncoding u D).size) :
    rankedQuery u D fallback i.val = (testTapeEncoding u D).code.symm i := by
  simp only [rankedQuery, i.isLt, ↓reduceDIte]

theorem query_prefixBits_eq_ofFn (u D n : ℕ) (queries : ℕ → SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D queries values signature n =
      (List.ofFn (fun i : Fin n => queries i.val)).flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  induction n with
  | zero => simp [SourceQueryLoop.prefixBits]
  | succ n ih =>
    rw [SourceQueryLoop.prefixBits, List.ofFn_succ', List.concat_eq_append,
      List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Fin.val_castSucc, Fin.val_last] using
      congrArg (fun bits => bits ++
        SourceTestAppend.equationBits u D values (signature, queries n)) ih

theorem query_prefixBits_eq_enumerate (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback) values signature
        (testTapeEncoding u D).size =
      (testTapeEncoding u D).enumerate.flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  rw [query_prefixBits_eq_ofFn]
  have hlist : List.ofFn (fun i : Fin (testTapeEncoding u D).size =>
      rankedQuery u D fallback i.val) = (testTapeEncoding u D).enumerate := by
    apply congrArg List.ofFn
    funext i
    exact rankedQuery_at u D fallback i
  rw [hlist]

end MaxCutGames.Foundations.Hastad.SourceLoopOrder

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextClear
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceContextClear

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

def main : Label u Extra := entryLabel_inline_SourceContextClear fields

variable [DecidableEq Extra]

def program : Label u Extra → TM2.Stmt (fun _ : Tape u Extra => Bool)
    (Label u Extra) (Unit × Option Bool)
  | .inl l => MachineDrainMany.instruction fields Sum.inl (some (.inr ())) l
  | .inr _ => .load (fun _ => ((), none)) .halt

omit [DecidableEq Extra] in
theorem entry_eq_inline_SourceContextClear :
    MachineDrainMany.entry (fields (u := u) (Extra := Extra)) Sum.inl (some (.inr ())) =
      some (main (u := u) (Extra := Extra)) := entryLabel_eq_inline_SourceContextClear fields

theorem finalTapes_eq (base : Tape u Extra → List Bool) :
    MachineDrainMany.finalTapes fields base = outputTapes base := by
  funext p
  rw [MachineDrainMany.finalTapes_apply]
  cases p <;> simp [mem_fields_iff, outputTapes]

theorem lengthSum_le_selected_inline_SourceContextClear {K : Type} (chosen : List K)
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

theorem clauseField_length_le {n : Nat} (c : Target.Clause n) (s : Fin 6) :
    (encodeWord ((clauseWords c)[s.val]'(by simp))).length ≤ n + 2 := by
  have h0 := (c)[0].variableIndex.isLt
  have h1 := (c)[1].variableIndex.isLt
  have h2 := (c)[2].variableIndex.isLt
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
  have h := lengthSum_le_selected_inline_SourceContextClear fields (SourceContextLoad.stageTapes F tuple base u)
    (formulaBits F).length (by
      intro p hp
      obtain ⟨j, s, rfl⟩ := (mem_fields_iff p).mp hp
      exact loaded_field_length_le F tuple base hfields j s)
  rw [fields_length] at h
  rw [Nat.mul_add, Nat.mul_one]
  omega

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

end MaxCutGames.Foundations.Hastad.SourceContextClear

namespace MaxCutGames.Foundations.Hastad.SourceQueryOrder

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

end MaxCutGames.Foundations.Hastad.SourceQueryOrder

namespace MaxCutGames.Foundations.Hastad.SourceTupleTape

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

theorem horner_variable_result (base : Arena u Extra → List Bool) (s : Snapshot)
    (selected : SlotContext u) (value : Nat) :
    MachineHorner.resultTapes (variableRankSlots selected) (tapes base s) value =
      tapes base {s with rank := encodeWord value ++ s.rank} := by
  change Function.update (tapes base s) (workTape .rank)
    (encodeWord value ++ tapes base s (workTape .rank)) = _
  rw [tapes_rank, update_rank]

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
theorem tapes_coordinateOutput {variableCount : Nat} (j : Fin u)
    (clause : Target.Clause variableCount)
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

end MaxCutGames.Foundations.Hastad.SourceTupleTape

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_HeaderCounts
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

noncomputable section

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

inductive Label (u D : Nat)
  | evaluate (kind : Kind) (localLabel : Eval.Label (polynomial u D kind))
  | copyLeftOut | copyLeftBack | addRight | clearTemporary
  | copyDummyOut | copyDummyBack | incrementBits
  deriving DecidableEq, Fintype

def evalStart (kind : Kind) : Label u D := .evaluate kind (Eval.start (polynomial u D kind))

def afterEval : Kind → Label u D
  | .left => evalStart .right | .right => evalStart .occurrences | .occurrences => .copyLeftOut

variable [DecidableEq K]

def statement (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ) :
    Label u D → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .evaluate kind l => Eval.statement (polynomial u D kind) (evalSlots slots kind)
      (fun l => labels (.evaluate kind l)) (some (labels (afterEval kind))) l
  | .copyLeftOut => Reduction.MachineTransfer.loopAt (control slots .leftBlockSize)
      (control slots .scratch) id false (labels .copyLeftOut) (some (labels .copyLeftBack))
  | .copyLeftBack => MachineCopy.forkLoop (control slots .scratch)
      (control slots .leftBlockSize) (control slots .dummyIndex) false
      (labels .copyLeftBack) (some (labels .addRight))
  | .addRight => MachineUnaryAddAt.loop (control slots .rightTemporary)
      (control slots .dummyIndex) (labels .addRight) (some (labels .clearTemporary))
  | .clearTemporary => .pop (control slots .rightTemporary) (fun state _ => state)
      (.goto fun _ => labels .copyDummyOut)
  | .copyDummyOut => Reduction.MachineTransfer.loopAt (control slots .dummyIndex)
      (control slots .scratch) id false (labels .copyDummyOut) (some (labels .copyDummyBack))
  | .copyDummyBack => MachineCopy.forkLoop (control slots .scratch)
      (control slots .dummyIndex) (control slots .bitCount) false
      (labels .copyDummyBack) (some (labels .incrementBits))
  | .incrementBits => .push (control slots .bitCount) (fun _ => true)
      (Reduction.MachineTransfer.exitAt (control slots .bitCount) exit)

def steps (u D n m : Nat) : Nat :=
  Eval.steps (polynomial u D .left) n + Eval.steps (polynomial u D .right) m +
    Eval.steps (polynomial u D .occurrences) m +
    2 * leftValue u n + rightValue u m + 2 * dummyValue u n m + 11

def timePolynomial (u D : Nat) : Polynomial Nat :=
  CookLevin.PolynomialMachine.timePolynomial (polynomial u D .left) +
    CookLevin.PolynomialMachine.timePolynomial (polynomial u D .right) +
    CookLevin.PolynomialMachine.timePolynomial (polynomial u D .occurrences) +
    Polynomial.C 2 * polynomial u D .left + polynomial u D .right +
    Polynomial.C 2 * (polynomial u D .left + polynomial u D .right) + Polynomial.C 11

theorem steps_le_timePolynomial (u D n m L : Nat) (hn : n ≤ L) (hm : m ≤ L) :
    steps u D n m ≤ (timePolynomial u D).eval L := by
  have hEval (p : Polynomial Nat) (a : Nat) (ha : a ≤ L) :
      Eval.steps p a ≤ (CookLevin.PolynomialMachine.timePolynomial p).eval L := by
    apply Nat.le_trans (m := (CookLevin.PolynomialMachine.timePolynomial p).eval a)
    · rw [CookLevin.PolynomialMachine.timePolynomial_eval]
      unfold Eval.steps
      omega
    · exact natPolynomial_eval_mono _ ha
  have h1 := hEval (polynomial u D .left) n hn
  have h2 := hEval (polynomial u D .right) m hm
  have h3 := hEval (polynomial u D .occurrences) m hm
  have hl : leftValue u n ≤ leftValue u L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn u)
  have hr : rightValue u m ≤ rightValue u L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm u)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    polynomial_left_eval, polynomial_right_eval]
  unfold steps dummyValue
  omega

end

end MaxCutGames.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_HeaderAccumulate
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceStartup

open Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition

noncomputable section

variable {u D : Nat}

abbrev State (u D : Nat) := SourceRuntimeModel.State u D
abbrev ArithmeticLabel (u D : Nat) := SourceHeaderCounts.Label u D ⊕ Bool
abbrev Label (u D : Nat) := SourceLoopInit.Label u ⊕ ArithmeticLabel u D

def arithmeticEntry (u D : Nat) : ArithmeticLabel u D :=
  .inl (SourceHeaderCounts.evalStart .left)

def arithmeticProgram : ArithmeticLabel u D →
    TM2.Stmt (fun _ : Tape u D => Bool) (ArithmeticLabel u D) ArithmeticState
  | .inl l => SourceHeaderCounts.statement (headerSlots u D) Sum.inl (some (.inr false)) l
  | .inr l => SourceHeaderAccumulate.statement (headerLayout u D) Sum.inr none l

attribute [local instance] OAI.MaxCutGames.Foundations.Hastad.SourceStartup.instDecidableEqExtra
def program : Label u D → TM2.Stmt (fun _ : Tape u D => Bool) (Label u D) (State u D)
  | .inl l => MachineStateFrame.statement Sum.inl (some (.inr (arithmeticEntry u D)))
      (SourceLoopInit.program l)
  | .inr l => MachineControl.statement id (arithmeticStateEquiv u D)
      (MachineStateFrame.statement Sum.inr none (arithmeticProgram l))

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

def phaseBound (F : Target.Formula) (u D : Nat) : Nat :=
  ((2 * u + 3) * (formulaBits F).length + 6 * u + 7) +
    (SourceHeaderCounts.steps u D F.«variables» F.clauses.length +
      SourceHeaderCounts.bitValue u F.«variables» F.clauses.length +
      SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4)

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

def timePolynomial (u D : Nat) : Polynomial Nat :=
  SourceLoopInit.timePolynomial u + SourceHeaderCounts.timePolynomial u D +
    SourceHeaderCounts.polynomial u D .left + SourceHeaderCounts.polynomial u D .right +
    SourceHeaderCounts.polynomial u D .occurrences + Polynomial.C 5

theorem phaseBound_le_polynomial (F : Target.Formula) (u D : Nat) :
    phaseBound F u D ≤ (timePolynomial u D).eval (formulaBits F).length := by
  have hn := SourceBounds.formulaBits_length_ge_variables F
  have hm := SourceBounds.formulaBits_length_ge_clauses F
  have hc := SourceHeaderCounts.steps_le_timePolynomial u D F.«variables» F.clauses.length
    (formulaBits F).length hn hm
  have hl : SourceHeaderCounts.leftValue u F.«variables» ≤
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

end

end MaxCutGames.Foundations.Hastad.SourceStartup

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

namespace MaxCutGames.Foundations.Hastad.SourceBasePhase

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceAddressDescriptors
open MaxCutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Layout ↪ K) (coefficient : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .seed => pushWord (slots (.inr 0)) (encodeWord coefficient).reverse
      (.goto fun _ => labels (.horner .start))
  | .horner label => MachineHorner.statement slots (fun l => labels (.horner l))
      (some (labels .clear)) label
  | .clear => MachineHorner.drainLoop (slots (.inr 0)) (labels .clear) exit

def program (slots : Layout ↪ K) (coefficient : Nat) :
    Label → TM2.Stmt (fun _ : K => Bool) Label (MachineHorner.State σ) :=
  statement slots coefficient id none

end MaxCutGames.Foundations.Hastad.SourceBasePhase

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_TupleBody
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual clause-tuple body. Its fixed finite control loads the context,
computes the shared right address base, traverses every selected-slot tuple and
query tape in their declared encoding order, and physically clears its work.
-/

namespace MaxCutGames.Foundations.Hastad.SourceTupleBody

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

def framed {K Λ Λ' σ τ S : Type} {Γ : K → Type}
    (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) :
    TM2.Stmt Γ Λ' S :=
  MachineControl.statement id e (MachineStateFrame.statement labels exit q)

def framedConfiguration {K Λ Λ' σ τ S : Type} {Γ : K → Type}
    (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' S :=
  MachineControl.configuration id e (MachineStateFrame.configuration labels exit ambient c)

section Frame

variable {K Λ Λ' σ τ S : Type} {Γ : K → Type} [DecidableEq K]

theorem framed_stepAux (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (framed e labels exit q) (e (state, ambient)) tapes =
      framedConfiguration e labels exit ambient (TM2.stepAux q state tapes) := by
  rw [framed, MachineControl.stepAux_simulation, MachineStateFrame.stepAux_simulation]
  rfl

theorem framed_step (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' S)
    (atLabels : ∀ l, target (labels l) = framed e labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (framedConfiguration e labels exit ambient a) =
      some (framedConfiguration e labels exit ambient b) := by
  rcases a with ⟨label, state, tapes⟩
  cases label with
  | none => cases h
  | some l =>
    change some (TM2.stepAux (source l) state tapes) = some b at h
    cases Option.some.inj h
    change some (TM2.stepAux (target (labels l)) (e (state, ambient)) tapes) = _
    rw [atLabels, framed_stepAux]

def framedExecution (e : σ × τ ≃ S) (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' S)
    (atLabels : ∀ l, target (labels l) = framed e labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (framedConfiguration e labels exit ambient a)
      (some (framedConfiguration e labels exit ambient b)) budget :=
  MachineComposition.liftExecutionInTime _ _ (framedConfiguration e labels exit ambient)
    (framed_step e labels exit ambient source target atLabels) run

end Frame

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
  variableCount : base variableHeader = encodeWord F.«variables»
  clauseCount : base clauseHeader = encodeWord F.clauses.length
  leftBlock : base (workTape .leftBlock) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u)
  dummy : base (workTape .dummy) =
    encodeWord (F.«variables» ^ u * 2 ^ (2 ^ u) + F.clauses.length ^ u * 2 ^ (8 ^ u))
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
  1 + (MachineHorner.timePolynomial u).eval F.«variables» +
    (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).eval
      (SourceBasePhase.operandLength (variableRank F c index) 0) +
    (QueryCount u D * (9 * nBits F u + 21) + 1) +
    (variableRank F c index + 2) + (leftValue F c index + 2)

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

def slotAt (u : Nat) (i : Nat) : SlotContext u :=
  if h : i < SlotCount u then selected ⟨i, h⟩ else fun _ => .first

def prefixBits (F : Target.Formula) (c : ClauseContext F u) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixBits F c r ++ SourceQueryOrder.slotBits F u D c (slotAt u r)

noncomputable def prefixBudget (F : Target.Formula) (c : ClauseContext F u) : Nat → Nat
  | 0 => 0
  | r + 1 => prefixBudget F c r + if h : r < SlotCount u then slotBudget (D := D) F c ⟨r, h⟩ else 0

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
        (2 ^ (2 ^ u) * F.«variables» ^ u)) +
    (((clauseEncoding F u).code c).val + 2)

def finishBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  1 + (rightValue F c + 2) + 2 + (6 * u * ((formulaBits F).length + 1) + 1) + 1

noncomputable def bodyBudget (F : Target.Formula) (c : ClauseContext F u) : Nat :=
  setupBudget F c + prefixBudget (D := D) F c (SlotCount u) + finishBudget F c

end MaxCutGames.Foundations.Hastad.SourceTupleBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Gap
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceGap

open Target SourceContexts SourceOccurrences SourceGame
open MaxCutGames.Integration.SourceParameters
open MaxCutGames.Reduction

/-- A clause gap includes nonemptiness: a cross-multiplied inequality alone
would hold vacuously for a formula with no clauses. -/
def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.«variables» → Bool,
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
    ∃ bits : Fin (source η ξ hη hη1 hξ D hD F).«variables» → Bool,
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
    (bits : Fin (source η ξ hη hη1 hξ D hD F).«variables» → Bool) :
    ((source η ξ hη hη1 hξ D hD F).equations.countP
      (fun e => CloneGap.satisfied e bits) : ℚ) /
        (source η ξ hη hη1 hξ D hD F).equations.length ≤ (1 + ξ) / 2 :=
  SourceSoundness.sourceList_sound_rat F hgap.1
    (repetitionCount η ξ hη hη1 hξ D hD) D hD hDtwo ξ hξ.le
      (repeated_game_bound F η ξ hη hη1 hξ D hD hgap) bits

end MaxCutGames.Foundations.Hastad.SourceGap

/-!
An executable finite-noise denominator for a positive rational target error.
Using the stored rational denominator avoids rounding, searches, and choice.
-/

namespace MaxCutGames.Foundations.Hastad.SourceGap

open Target SourceNoiseParameter MaxCutGames.Reduction

def forError (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    Formula → SourceEncoding.Input :=
  source η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)

theorem forError_complete (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits : Fin (forError η ξ hη hη1 hξ F).«variables» → Bool,
      1 - ξ ≤ ((forError η ξ hη hη1 hξ F).equations.countP
        (fun e => CloneGap.satisfied e bits) : ℚ) /
          (forError η ξ hη hη1 hξ F).equations.length :=
  source_complete η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)
    (noiseDenominator_inv_le hξ) F hF

theorem forError_sound (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (F : Formula) (hgap : ClauseGap F η)
    (bits : Fin (forError η ξ hη hη1 hξ F).«variables» → Bool) :
    ((forError η ξ hη hη1 hξ F).equations.countP
      (fun e => CloneGap.satisfied e bits) : ℚ) /
        (forError η ξ hη hη1 hξ F).equations.length ≤ (1 + ξ) / 2 :=
  source_sound η ξ hη hη1 hξ (noiseDenominator ξ) (noiseDenominator_pos ξ)
    (noiseDenominator_ge_two ξ) F hgap bits

end MaxCutGames.Foundations.Hastad.SourceGap

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorProgram

open Turing Complexity SourceGeneratorModel

noncomputable section

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

def main (u D : Nat) : Label u D := .startup (.inl .inputCopyOut)

end

end MaxCutGames.Foundations.Hastad.SourceGeneratorProgram

namespace MaxCutGames.Foundations.Hastad.SourceGenerator
open Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram
noncomputable section

variable {u D : Nat}
local instance instDecidableEqExtra : DecidableEq (Extra u D) := Classical.decEq _

theorem source_initial (u D : Nat) (hD : 0 < D) :
    sourceStateEquiv u D (SourceGeneratorModel.initialState u D hD, ()) =
      (initialAmbient u D hD, none) := rfl

end
end MaxCutGames.Foundations.Hastad.SourceGenerator

/-! Uniform polynomial bounds for the actual tuple-body phase budgets.
The budget being bounded is the one used by the checked machine traces. -/

namespace MaxCutGames.Foundations.Hastad.SourceTupleBound

open Complexity SourceContexts SourceOccurrences SourceTupleBody
open Complexity.MachineComposition

variable {u D : Nat}

noncomputable def slotPolynomial (u D : Nat) : Polynomial Nat :=
  Polynomial.C 1 + MachineHorner.timePolynomial u +
    (SourceBasePhase.timePolynomial (2 ^ (2 ^ u))).comp (rankPolynomial u + Polynomial.C 2) +
    (Polynomial.C (QueryCount u D) * (Polynomial.C 9 * numberPolynomial u + Polynomial.C 21) +
      Polynomial.C 1) +
    (rankPolynomial u + Polynomial.C 2) + (numberPolynomial u + Polynomial.C 2)

noncomputable def preparePolynomial (u : Nat) : Polynomial Nat :=
  Polynomial.C u * (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) + Polynomial.C 1 +
    (Polynomial.C (SourceSignaturePrepare.Width u * SourceSignaturePrepare.Width u) *
      (Polynomial.C 5 * Polynomial.X + Polynomial.C 6) + Polynomial.C 2)

noncomputable def setupPolynomial (u : Nat) : Polynomial Nat :=
  preparePolynomial u + Polynomial.C 1 + MachineHorner.timePolynomial u +
    (SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).comp
      (rankPolynomial u + numberPolynomial u + Polynomial.C 2) +
    (rankPolynomial u + Polynomial.C 2)

noncomputable def bodyPolynomial (u D : Nat) : Polynomial Nat :=
  setupPolynomial u + Polynomial.C (SlotCount u) * slotPolynomial u D + finishPolynomial u

end MaxCutGames.Foundations.Hastad.SourceTupleBound

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

open Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceGeneratorProgram SourceOdometerSchedule

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal.instDecidableEqExtra
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
  · change (SourceStartup.readyTapes (u := u) (D := D) F) variableHeader = encodeWord F.«variables»
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

theorem allBits_eq_records (F : Target.Formula) (hne : F.clauses ≠ []) :
    allBits (SourceQueryOrder.tupleBits F u D) =
      (sourceList F u D).flatMap (fun e =>
        encodeWords (MaxCutGames.Reduction.SourceEncoding.equationWords e)) := by
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
      (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  rw [allBits_eq_records F hne, SourceStartup.ready_accumulator]
  have hi := SourceLoopOrder.inputBits_eq_header_records (sourceInput F u D hD)
  change MaxCutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD) =
    encodeWords [nBits F u, (sourceList F u D).length] ++
      (sourceList F u D).flatMap (fun e =>
        encodeWords (MaxCutGames.Reduction.SourceEncoding.equationWords e)) at hi
  rw [hi, List.reverse_append]

theorem traversalOutput_frame (F : Target.Formula) (hD : 0 < D)
    (k : SourceGeneratorModel.Tape u D) (hk : k ≠ accumulatorTape u D) :
    traversalOutput F hD k = SourceStartup.readyTapes F k := by
  simp [traversalOutput, hk]

def resetLabel (u D : Nat) (i : Nat) : SourceGeneratorProgram.Label u D :=
  if h : i < u then .reset ⟨i, h⟩ else .finishEnter

def timePolynomial (u D : Nat) : Polynomial Nat :=
  (SourceTupleBound.bodyPolynomial u D + Polynomial.C (2 * u)) * Polynomial.X ^ u

end

end MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Generator
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceGenerator

open Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram

noncomputable section

variable {u D : Nat}
local instance instDecidableEqExtra_1 : DecidableEq (Extra u D) := Classical.decEq _

def prefixPolynomial (u D : Nat) : Polynomial Nat :=
  SourceStartup.timePolynomial u D + SourceGeneratorTraversal.timePolynomial u D + 1

theorem output_empty (F : Formula) (hD : 0 < D) :
    SourceGeneratorTraversal.traversalOutput F hD (outputTape u D) = [] := by
  rw [SourceGeneratorTraversal.traversalOutput_frame F hD _
    (Ne.symm (accumulator_ne_output u D))]
  exact SourceStartup.ready_work_blank F (.extra (.inr ()))
    (by simp) (by simp) (by simp)

end

end MaxCutGames.Foundations.Hastad.SourceGenerator

/-!
# Executable directed-dart tables for the fixed 64-label alphabet

The header gives vertex and dart counts. Every dart has one ordered row:
tail index, reverse-dart index, and 4096 Boolean predicate entries. Entry
`b + 64 * a` is the predicate at labels `(a,b)`. All fields, including bits
as 0/1 words, use the existing zero-delimited unary natural-word codec.

The decoder checks all index bounds, row counts, predicate lengths, reverse
involution, predicate transpose, and absence of trailing fields. Directed rows
preserve loops, self-reversing darts, and repeated constraint occurrences.
The size theorems concern the full encoded table, not a machine runtime.
-/

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringOpinionTables
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

namespace MaxCutGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

/-- Serialized output in the shared generic graph codec. -/
def outputBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) : List Bool :=
  GenericGraphTables.tableBits (table input n)

/-- The actual function on variable-size regular input tables. -/
def transform (d n : Nat) (input : PortTables.Input d) : GenericGraphTables.Table (labelCount d n) :=
  table input.2 n

end MaxCutGames.Foundations.PCP.PoweringTables

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

end OAI
end


