-- Prove2me | Definitions.Def_OAIQ087A034
-- name    : OAIQ087A034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T18:02:26.997304+00:00
-- url     : https://prove2.me/theorems/df2a6f30-523b-4f17-aa47-0d75978d4c09
-- title:
--   Definitions bundle OAIQ087A034 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 80 declarations of OpenAI's Lean: 49 definitions and 31 theorems. The definitions and types are `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRuntime.finishSteps`, `OAI.MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget.preBudget`, `OAI.MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget.totalBudget`, `OAI.MaxCutGames.Foundations.Complexity.PoweringRuntimeBudget.tapeCount`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextPrepare.loadInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextPrepare.prepareInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextPrepare.signatureInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.beforeFinish`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.computableInPolyTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.enterFinishInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.forErrorComputableInPolyTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.outputInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.prefixInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.startupInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.timePolynomial`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorProgram.machine`, `OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorProgram.program`, `OAI.MaxCutGames.Foundations.Hastad.SourceHeaderCounts.inTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceStartup.arithmeticInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceStartup.arithmeticPlacedInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceStartup.phasesInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceStartup.startupInPolynomialTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceStartup.startupInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.clauseRankPhase`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.drainPhase`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.finishInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.leftBasePhase`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.preparePhase`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.program`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.resetInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.rightBasePhase`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.seedZeroPhase`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.selectPhase`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.setupInTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceTupleBody.variableRankPhase`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Body.rowStep`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Loop.runPrefix`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Loop.runRemaining`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Runtime.tableOutputsInTime`, `OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Runtime.tablePolynomialTime` and 9 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_BinaryParityReduction`, `MaxCut_Games_Clone100Counting`, `MaxCut_Games_PoweringPolynomialBudget`, `MaxCut_Machines_Body`, `MaxCut_Machines_MachineLazyTableRuntime`, `MaxCut_Machines_MachineTableIteration`, `MaxCut_Machines_PoweringMachineRuntime`, `MaxCut_Machines_PoweringRuntimeBudget`, `MaxCut_Machines_Runtime2`, `MaxCut_PCP_ContextPrepare`, `MaxCut_PCP_Gap`, `MaxCut_PCP_Generator`, `MaxCut_PCP_Hastad`, `MaxCut_PCP_HeaderAccumulate`, `MaxCut_PCP_HeaderCounts`, `MaxCut_PCP_RoundComputation`, `MaxCut_PCP_TableIteration`, `MaxCut_PCP_TupleBody`.
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
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextPrepare
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceContextPrepare

open Turing MaxCutGames.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

variable {u : Nat} {Extra τ : Type}

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

end MaxCutGames.Foundations.Hastad.SourceContextPrepare

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

variable {u D : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem evalPhaseTrace (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (kind : Kind) (base : K → List Bool) (n : Nat)
    (hinput : base (control slots (inputControl kind)) = encodeWord n)
    (hdest : base (control slots (outputControl kind)) = [])
    (clean : WorkClean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[Eval.steps (polynomial u D kind) n]
      (some ⟨some (labels (evalStart kind)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (afterEval kind)), ((ambient, ()), none),
        Function.update base (control slots (outputControl kind))
          (encodeWord ((polynomial u D kind).eval n))⟩ := by
  have h := Eval.trace (polynomial u D kind) (evalSlots slots kind)
    (fun l => labels (.evaluate kind l)) (some (labels (afterEval kind))) program
    (fun l => atLabels (.evaluate kind l)) base n (by simpa using hinput)
    (fun i => by simpa using clean.coefficients (coefficientBlock u D kind i))
    ⟨by simpa using clean.accA, by simpa using clean.accB,
      by simpa using clean.counter, by simpa using clean.scratch⟩ ambient register
  simpa only [evalStart, MachineHorner.resultTapes, evalSlots_destination,
    hdest, List.append_nil] using h

/-- The actual header program preserves its two operands and every caller frame.
The four retained outputs are left-block size, dummy index, bit count, and
occurrence count. The temporary and all coefficient/work tapes are restored. -/
theorem trace (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .clauseCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps u D n m]
      (some ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩ := by
  let t1 := Function.update base (control slots .leftBlockSize) (encodeWord (leftValue u n))
  let t2 := Function.update t1 (control slots .rightTemporary) (encodeWord (rightValue u m))
  let t3 := Function.update t2 (control slots .occurrenceCount) (encodeWord (occurrenceValue u D m))
  let t4 := Function.update t3 (control slots .dummyIndex) (encodeWord (leftValue u n))
  let t5 := Function.update (Function.update t4 (control slots .rightTemporary) [false])
    (control slots .dummyIndex) (encodeWord (dummyValue u n m))
  let t6 := Function.update t5 (control slots .rightTemporary) []
  let t7 := Function.update t6 (control slots .bitCount) (encodeWord (dummyValue u n m))
  have h1 := evalPhaseTrace slots labels exit program atLabels .left base n hn clean.left
    clean.work ambient register
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .left) n]
      (some ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (evalStart .right)), ((ambient, ()), none), _⟩ at h1
  simp only [polynomial_left_eval] at h1
  have cw1 : WorkClean slots t1 := clean.work.update_output .left _
  have h2 := evalPhaseTrace slots labels exit program atLabels .right t1 m
    (by simpa [t1, inputControl] using hm)
    (by simpa [t1, outputControl] using clean.right) cw1 ambient none
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .right) m]
      (some ⟨some (labels (evalStart .right)), ((ambient, ()), none), t1⟩) =
      some ⟨some (labels (evalStart .occurrences)), ((ambient, ()), none), _⟩ at h2
  simp only [polynomial_right_eval] at h2
  have cw2 : WorkClean slots t2 := cw1.update_output .right _
  have h3 := evalPhaseTrace slots labels exit program atLabels .occurrences t2 m
    (by simpa [t2, t1, inputControl] using hm)
    (by simpa [t2, t1, outputControl] using clean.occurrences) cw2 ambient none
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .occurrences) m]
      (some ⟨some (labels (evalStart .occurrences)), ((ambient, ()), none), t2⟩) =
      some ⟨some (labels .copyLeftOut), ((ambient, ()), none), _⟩ at h3
  simp only [polynomial_occurrences_eval] at h3
  have cw3 : WorkClean slots t3 := cw2.update_output .occurrences _
  have copyingLeft := MachineCopy.copyTrace (control slots .leftBlockSize)
    (control slots .dummyIndex) (control slots .scratch)
    (by simp) (by simp) (by simp) false (labels .copyLeftOut) (labels .copyLeftBack)
    (some (labels .addRight)) program (atLabels .copyLeftOut) (atLabels .copyLeftBack)
    t3 cw3.scratch (ambient, ()) none
  have hleft : t3 (control slots .leftBlockSize) = encodeWord (leftValue u n) := by
    simp [t3, t2, t1]
  have hdummy : t3 (control slots .dummyIndex) = [] := by
    simpa [t3, t2, t1] using clean.dummy
  rw [hleft, hdummy, List.append_nil, encodeWord_length] at copyingLeft
  have adding := MachineUnaryAddAt.addFromTapes (control slots .rightTemporary)
    (control slots .dummyIndex) (by simp) (labels .addRight) (some (labels .clearTemporary))
    program (atLabels .addRight) t4 (rightValue u m) (leftValue u n) [] []
    (by simp [t4, t3, t2]) (by simp [t4]) (ambient, ()) none
  have ha : MachineUnaryAddAt.unaryTapes (control slots .rightTemporary)
      (control slots .dummyIndex) t4 0 (rightValue u m + leftValue u n) [] [] = t5 := by
    simp [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt, t5,
      encodeWord, dummyValue, Nat.add_comm]
  rw [ha] at adding
  have clearing : (advance (TM2.step program))^[1]
      (some ⟨some (labels .clearTemporary), ((ambient, ()), none), t5⟩) =
      some ⟨some (labels .copyDummyOut), ((ambient, ()), none), t6⟩ := by
    change some (TM2.stepAux (program (labels .clearTemporary)) _ _) = _
    rw [atLabels]
    simp [statement, TM2.stepAux, t6, t5]
  have copyingDummy := MachineCopy.copyTrace (control slots .dummyIndex)
    (control slots .bitCount) (control slots .scratch)
    (by simp) (by simp) (by simp) false (labels .copyDummyOut) (labels .copyDummyBack)
    (some (labels .incrementBits)) program (atLabels .copyDummyOut) (atLabels .copyDummyBack)
    t6 (by simpa [t6, t5, t4] using cw3.scratch) (ambient, ()) none
  have hdi : t6 (control slots .dummyIndex) = encodeWord (dummyValue u n m) := by
    simp [t6, t5]
  have hbi : t6 (control slots .bitCount) = [] := by
    simpa [t6, t5, t4, t3, t2, t1] using clean.bits
  rw [hdi, hbi, List.append_nil, encodeWord_length] at copyingDummy
  have increment : (advance (TM2.step program))^[1]
      (some ⟨some (labels .incrementBits), ((ambient, ()), none), t7⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update t7 (control slots .bitCount) (encodeWord (bitValue u n m))⟩ := by
    change some (TM2.stepAux (program (labels .incrementBits)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt,
      t7, bitValue, encodeWord, List.replicate_succ]
  have total := trace_trans_inline_SourceHeaderCounts _ (trace_trans_inline_SourceHeaderCounts _ (trace_trans_inline_SourceHeaderCounts _ (trace_trans_inline_SourceHeaderCounts _
    (trace_trans_inline_SourceHeaderCounts _ (trace_trans_inline_SourceHeaderCounts _ (trace_trans_inline_SourceHeaderCounts _ h1 h2) h3) copyingLeft) adding) clearing)
      copyingDummy) increment
  have htime :
      Eval.steps (polynomial u D .left) n + Eval.steps (polynomial u D .right) m +
        Eval.steps (polynomial u D .occurrences) m + 2 * (leftValue u n + 1 + 1) +
        (rightValue u m + 1) + 1 + 2 * (dummyValue u n m + 1 + 1) + 1 =
      steps u D n m := by unfold steps; omega
  rw [htime] at total
  have frame : Function.update t7 (control slots .bitCount) (encodeWord (bitValue u n m)) =
      resultTapes slots base n m := by
    funext k
    by_cases hr : k = control slots .rightTemporary
    · subst k
      simp [t7, t6, t5, t4, t3, t2, t1, resultTapes, clean.right]
    · simp [t7, t6, t5, t4, t3, t2, t1, resultTapes, Function.update_apply, hr]
      split_ifs <;> rfl
  rw [frame] at total
  exact total

def inTime (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .clauseCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (steps u D n m) where
  steps := steps u D n m
  evals_in_steps := trace slots labels exit program atLabels base n m hn hm clean ambient register
  steps_le_m := Nat.le_refl _

end

end MaxCutGames.Foundations.Hastad.SourceHeaderCounts

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_HeaderAccumulate
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

attribute [local instance] OAI.MaxCutGames.Foundations.Hastad.SourceStartup.instDecidableEqExtra
def arithmeticInTime (F : Target.Formula) :
    StateTransition.EvalsToInTime (TM2.step arithmeticProgram)
      ⟨some (arithmeticEntry u D), (((), ()), none), initializedTapes F⟩
      (some ⟨none, (((), ()), none), outputTapes F⟩)
      (SourceHeaderCounts.steps u D F.«variables» F.clauses.length +
        SourceHeaderCounts.bitValue u F.«variables» F.clauses.length +
        SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4) := by
  have countRun := SourceHeaderCounts.inTime (headerSlots u D) Sum.inl (some (.inr false))
    arithmeticProgram (fun _ => rfl) (initializedTapes F) F.«variables» F.clauses.length
    (initialized_variableHeader F) (initialized_clauseHeader F) (initialized_clean F) () none
  have appendRun := SourceHeaderAccumulate.inTime (headerLayout u D) Sum.inr none
    arithmeticProgram (fun _ => rfl) (countedTapes F)
    (SourceHeaderCounts.bitValue u F.«variables» F.clauses.length)
    (SourceHeaderCounts.occurrenceValue u D F.clauses.length)
    (SourceHeaderCounts.result_bits (headerSlots u D) (initializedTapes F) _ _)
    (SourceHeaderCounts.result_occurrences (headerSlots u D) (initializedTapes F) _ _) ((), ()) none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step arithmeticProgram) _ _ _ _ _
    countRun appendRun
  refine { steps := joined.steps, evals_in_steps := joined.evals_in_steps, steps_le_m := ?_ }
  have ht := joined.steps_le_m
  omega

def arithmeticPlacedInTime (F : Target.Formula) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inr (arithmeticEntry u D)), SourceGeneratorModel.initialState u D hD, initializedTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, outputTapes F⟩)
      (SourceHeaderCounts.steps u D F.«variables» F.clauses.length +
        SourceHeaderCounts.bitValue u F.«variables» F.clauses.length +
        SourceHeaderCounts.occurrenceValue u D F.clauses.length + 4) := by
  have lifted := liftExecutionInTime (TM2.step arithmeticProgram) (TM2.step program)
    (arithmeticConfiguration (initialArithmeticMetadata u D hD))
    (arithmetic_step (initialArithmeticMetadata u D hD)) (arithmeticInTime F)
  simpa only [arithmeticConfiguration, MachineControl.configuration,
    MachineStateFrame.configuration, MachineStateFrame.frameConfiguration,
    MachineSubroutine.configuration, MachineSubroutine.label, Option.map_some, Option.map_none,
    id_eq, initial_arithmetic] using lifted

def phasesInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, outputTapes F⟩)
      (phaseBound F u D) := by
  have run := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (initializeInTime (u := u) F hm hD) (arithmeticPlacedInTime (u := u) F hD)
  simpa only [phaseBound, Nat.add_comm] using run

def startupInTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, readyTapes F⟩)
      (phaseBound F u D) := by
  have run := phasesInTime (u := u) F hm hD
  simpa only [output_eq_ready F hm] using run

def startupInPolynomialTime (F : Target.Formula) (hm : 0 < F.clauses.length) (hD : 0 < D) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.inl .inputCopyOut), SourceGeneratorModel.initialState u D hD, initialTapes F⟩
      (some ⟨none, SourceGeneratorModel.initialState u D hD, readyTapes F⟩)
      ((timePolynomial u D).eval (formulaBits F).length) := by
  have run := startupInTime (u := u) F hm hD
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  exact Nat.le_trans run.steps_le_m (phaseBound_le_polynomial F u D)

end

end MaxCutGames.Foundations.Hastad.SourceStartup

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_TupleBody
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.slotFintype _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
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

variable {u D : Nat} {Extra : Type}

variable [DecidableEq Extra]

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
    (hradix : base (variableRankSlots (selected index) (.inl 0)) = encodeWord F.«variables»)
    (hdigits : ∀ i, base (variableRankSlots (selected index) (.inr i)) =
      encodeWord (sampledVariables F c (selected index) i).val)
    (hclean : MachineHorner.Clean (variableRankSlots (selected index)) base)
    (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.variableRank index .start), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some (.leftBase index .seed), arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (variableRankSlots (selected index)) base
          (((variableEncoding F u).code (sampledVariables F c (selected index))).val)⟩)
      ((MachineHorner.timePolynomial u).eval F.«variables») := by
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
    (hleftBlock : base (baseSlots true (.inr 1)) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u))
    (hcoefficient : base (baseSlots true (.inr 0)) = [])
    (hclean : MachineHorner.Clean (baseSlots true) base) (metadata : ArithmeticMetadata u D) :
    StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.rightBase .seed), arithmeticStateEquiv u D ((((), ()), none), metadata), base⟩
      (some ⟨some .clearClauseRank, arithmeticStateEquiv u D ((((), ()), none), metadata),
        MachineHorner.resultTapes (baseSlots true) base
          (SourceAddressDescriptors.baseValue F u c (sampledVariables F c (fun _ => .first)) 1)⟩)
      ((SourceBasePhase.timePolynomial (2 ^ (8 ^ u))).eval
        (SourceBasePhase.operandLength (((clauseEncoding F u).code c).val)
          (2 ^ (2 ^ u) * F.«variables» ^ u))) := by
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
    (by change loaded variableHeader = encodeWord F.«variables»
        exact (loaded_extra F c base _).trans h.variableCount)
    (by intro i
        exact SourceRankPhase.selectedDigits_loaded F c (selected index)
          (rankControls .variableCount) base (fun j => h.fields j _) i)
    (clean_variable loaded (loopSnapshot F c bits) (selected index) h.loadedClean)
    (arithmeticMetadata F c sig initialQuery)
  have hr' : StateTransition.EvalsToInTime (TM2.step (program initialQuery exit))
      ⟨some (.variableRank index .start), workingState F c sig initialQuery, startTapes⟩
      (some ⟨some (.leftBase index .seed), workingState F c sig initialQuery, rankedTapes⟩)
      ((MachineHorner.timePolynomial u).eval F.«variables») := by
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
    (by change loaded (workTape .leftBlock) = encodeWord (2 ^ (2 ^ u) * F.«variables» ^ u)
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
          (2 ^ (2 ^ u) * F.«variables» ^ u))) := by
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

end MaxCutGames.Foundations.Hastad.SourceTupleBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Gap
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An executable finite-noise denominator for a positive rational target error.
Using the stored rational denominator avoids rounding, searches, and choice.
-/

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorProgram

open Turing Complexity SourceGeneratorModel

noncomputable section

attribute [local instance] OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorProgram.instDecidableEqExtra
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

end MaxCutGames.Foundations.Hastad.SourceGeneratorProgram

namespace MaxCutGames.Foundations.Hastad.SourceGenerator
open Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram SourceGeneratorContract
noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.instDecidableEqExtra
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
end MaxCutGames.Foundations.Hastad.SourceGenerator

/-! Uniform polynomial bounds for the actual tuple-body phase budgets.
The budget being bounded is the one used by the checked machine traces. -/

namespace MaxCutGames.Foundations.Hastad.SourceTupleBound

open Complexity SourceContexts SourceOccurrences SourceTupleBody
open Complexity.MachineComposition

variable {u D : Nat}

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

end MaxCutGames.Foundations.Hastad.SourceTupleBound

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

open Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceGeneratorProgram SourceOdometerSchedule

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal.instDecidableEqExtra
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

end MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Generator
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceGenerator

open Turing Complexity Target
open SourceGeneratorModel SourceGeneratorProgram SourceGeneratorContract

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MaxCutGames.Foundations.Hastad.SourceGenerator.instDecidableEqExtra_1
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

theorem halted_configuration (F : Formula) (hD : 0 < D) :
    (⟨none, (initialAmbient u D hD, none),
      SourceRuntimeFinish.canonicalTapes (outputTape u D)
        (SourceGeneratorTraversal.traversalOutput F hD (accumulatorTape u D)).reverse⟩ :
      (SourceGeneratorProgram.machine u D hD).Cfg) =
      haltList (SourceGeneratorProgram.machine u D hD)
        (MaxCutGames.Reduction.SourceEncoding.inputBits (SourceOccurrences.sourceInput F u D hD)) := by
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
      (some (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)))
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
    TM2ComputableInPolyTime inputEncoding MaxCutGames.Reduction.SourceEncoding.inputBits
      (sourceMap u D hD) where
  tm := SourceGeneratorProgram.machine u D hD
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial u D hD
  outputsFun F := by
    change TM2OutputsInTime (machine u D hD) ((inputEncoding F).map id)
      (some ((MaxCutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F)).map id)) _
    have hi := @List.map_id ((machine u D hD).Γ (machine u D hD).k₀) (inputEncoding F)
    have ho := @List.map_id ((machine u D hD).Γ (machine u D hD).k₁)
      (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceMap u D hD F))
    simpa only [hi, ho] using outputInTime (u := u) F hD

def forErrorComputableInPolyTime (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) :
    TM2ComputableInPolyTime inputEncoding MaxCutGames.Reduction.SourceEncoding.inputBits
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
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Body
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
One actual iteration of the alphabet-table driver. The positive unary guard,
row parser, preserving head lookup, comparison, finite emission plan, three
drains, and unary index increment all execute inside `Driver.program`.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Body

open Turing
open MaxCutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

/-- Execute a whole row iteration from the exact guard invariant. Every run
below is obtained from the concrete code at its component labels. -/
def rowStep (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base)
    (oldRelation : GenericGraphTables.RelationTable q) (oldFlag : Bool) :
    RowStepResult input e base oldRelation oldFlag := by
  let N := (LoopState.inputBits input).length
  have guarded : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal oldRelation oldFlag, base⟩
      (some ⟨some .tailStart, normal oldRelation oldFlag, guardTapes input e base⟩) 1 := by
    have hbase : MachineUnaryCounter.counterTapes .counter base
        (input.darts - (e.val + 1) + 1) [] = base := by
      simp only [MachineUnaryCounter.counterTapes, List.append_nil,
        ← ready.counter_succ e.isLt, Function.update_eq_self]
    have run := MachineUnaryCounter.guardInTime_succ Tape.counter Driver.Label.guard
      .tailStart .reverseOutput (Driver.program q) (by rfl) base
      (input.darts - (e.val + 1)) [] (normal oldRelation oldFlag).1 none
    rw [hbase] at run
    simpa only [MachineUnaryCounter.counterTapes, List.append_nil, guardTapes,
      normal] using run
  have parsed : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .tailStart, normal oldRelation oldFlag, guardTapes input e base⟩
      (some ⟨some .headCopyFirst, normal input.rows[e].relation oldFlag,
        parsedTapes input e base⟩) (Lookup.readRowCost input.rows[e]) := by
    have hcursor : guardTapes input e base .cursor = Lookup.rowBits input.rows[e] ++
        LoopState.cursorBits input (e.val + 1) := by
      simpa only [guardTapes, Function.update_of_ne (by decide : Tape.cursor ≠ .counter),
        Lookup.rowBits] using ready.cursor.trans (LoopState.cursorBits_succ input e.val e.isLt)
    have htail : guardTapes input e base .tail = [] := by simp [guardTapes, ready.tail]
    have hreverse : guardTapes input e base .reverseIndex = [] := by
      simp [guardTapes, ready.reverseIndex]
    simpa only [normal, parsedTapes] using
      Lookup.readRowInTime Tape.cursor Tape.tail Tape.reverseIndex
        (by decide) (by decide) (by decide) Driver.Label.tailStart .tailLoop
        .reverseStart .reverseLoop .readPredicate .headCopyFirst (Driver.program q)
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (guardTapes input e base) input.rows[e] (LoopState.cursorBits input (e.val + 1))
        hcursor htail hreverse (oldFlag, false, none) oldRelation none
  have looked : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .headCopyFirst, normal input.rows[e].relation oldFlag, parsedTapes input e base⟩
      (some ⟨some (.compare .leftFirst), normal input.rows[e].relation oldFlag,
        workingTapes input e base⟩) (7 * N + 5) := by
    have htable : parsedTapes input e base (headPorts 0) = GenericGraphTables.tableBits input := by
      simpa [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes,
        LoopState.inputBits] using ready.original
    have hreverse : parsedTapes input e base (headPorts 1) =
        encodeWord (Lookup.headIndex input e).val := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, Lookup.headIndex]
    have hhead : parsedTapes input e base (headPorts 4) = [] := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes, ready.head]
    have hscratch : parsedTapes input e base (headPorts 5) = [] := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes, ready.scratch]
    have run := Lookup.headLookupInTime headPorts headPorts_injective
      Driver.Label.headCopyFirst .headCopySecond .indexCopyFirst .indexCopySecond
      .headVertices .headDarts Driver.Label.headLookup (some (.compare .leftFirst))
      (Driver.program q) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun _ => rfl) (parsedTapes input e base) input e htable hreverse hhead hscratch
      (normal input.rows[e].relation oldFlag).1 none
    simpa only [workingTapes, normal, N, LoopState.inputBits, Lookup.headTimePolynomial,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using run
  have hleft : workingTapes input e base .compareLeft = [] :=
    (workingTapes_other_inline_Body input e base .compareLeft (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareLeft
  have hright : workingTapes input e base .compareRight = [] :=
    (workingTapes_other_inline_Body input e base .compareRight (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareRight
  have hscratch : workingTapes input e base .scratch = [] :=
    (workingTapes_other_inline_Body input e base .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.scratch
  let compared := CompareLoop.compareRowInTime Driver.Label.compare (Driver.rowEntry q)
    (Driver.program q) (fun _ => rfl) input e (workingTapes input e base)
    (workingTapes_tail_inline_Body input e base) (workingTapes_head_inline_Body input e base)
    hleft hright hscratch oldFlag
  let emitted := emitInTime input e (workingTapes input e base)
    (workingOperands_inline_Body input e base ready) hscratch
  let cleared := clearFieldsInTime (emittedTapes input e base) (CompareLoop.rowState input e).1
  have hedge : clearFieldsTapes (emittedTapes input e base) .edge = encodeWord e.val := by
    simp [clearFieldsTapes, emittedTapes, Emitter.resultTapes, workingTapes,
      Lookup.headLookupTapes, MachineLookup.tapes, headPorts, parsedTapes,
      Lookup.readRowTapes, guardTapes, ready.edge]
  let incremented := incrementInTime (clearFieldsTapes (emittedTapes input e base))
    (CompareLoop.rowState input e).1 e.val hedge
  let run₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guarded parsed
  let run₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ looked
  let run₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₂ compared
  let run₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₃ emitted
  let run₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₄ cleared
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₅ incremented
  refine {
    tapes := resultTapes input e base
    ready := result_ready_inline_Body input e base ready
    run := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  }
  have hn : input.vertices ≤ N := GenericGraphTables.vertices_le_tableBits_length input
  have hm : input.darts ≤ N := GenericGraphTables.darts_le_tableBits_length input
  have hr : Lookup.readRowCost input.rows[e] ≤ 2 * N + 5 :=
    Lookup.readRowCost_table_le input e
  have ht : (emittedTapes input e base .tail).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.tail ≠ .reversed), workingTapes_tail_inline_Body,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].tail.isLt).trans hn
  have hv : (emittedTapes input e base .reverseIndex).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.reverseIndex ≠ .reversed), workingTapes_reverse_inline_Body,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].reverseIndex.isLt).trans hm
  have hh : (emittedTapes input e base .head).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.head ≠ .reversed), workingTapes_head_inline_Body,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[input.rows[e].reverseIndex].tail.isLt).trans hn
  have budget := run.steps_le_m
  change run.steps ≤ (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)
  nlinarith

end MaxCutGames.Foundations.PCP.AlphabetTable.Body

/-!
Actual setup-to-guard execution of the alphabet-table driver. The preserved
input is parsed by Setup; the finite header template runs through an explicit
state equivalence. The resulting loop invariant is a complete tape equation.
-/

/-!
The concrete tapes produced by initialization satisfy the row-zero loop
invariant. Execution of initialization is proved separately by
`Initialization.initializeInTime`; this bridge identifies its resulting tapes.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Loop

open Turing
open MaxCutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

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

end MaxCutGames.Foundations.PCP.AlphabetTable.Loop

/-! The actual final driver phases: reverse the accumulated output, drain all
fifteen nonoutput stacks, reset the finite state, and reach `haltList`.
Polynomial resource bounds below require an actual preceding execution. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Runtime2
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Runtime

open Turing
open MaxCutGames.Foundations.Complexity
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
      (some ((GraphTables.tableBits (Table.build input)).map id)) _
    have hi := @List.map_id ((Driver.machine q).Γ (Driver.machine q).k₀)
      (GenericGraphTables.tableBits input)
    have ho := @List.map_id ((Driver.machine q).Γ (Driver.machine q).k₁)
      (GraphTables.tableBits (Table.build input))
    simpa only [hi, ho] using tableOutputsInTime input

end MaxCutGames.Foundations.PCP.AlphabetTable.Runtime

/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/

namespace MaxCutGames.Foundations.PCP.AlphabetTable

open MaxCutGames.Foundations.Complexity

theorem Runtime.finiteAlphabet (q : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (Runtime.tablePolynomialTime q).tm :=
  Driver.finiteAlphabet q

end MaxCutGames.Foundations.PCP.AlphabetTable

/-!
# Exact register-equivalence transport for finite-stack programs

The instruction translation reuses `MachineControl.statement` with unchanged
labels. An explicit register equivalence changes neither tapes nor labels.
The transition function, every iterated trace, and runtime witnesses are
transported in exactly the same number of transitions, including failed or
halted traces. No simulation premise is assumed.
-/

/-!
# Finite tape program for a powered relation row

The radius, address count, and powered alphabet size are fixed machine
parameters. The machine consumes live base predicate bits and endpoint-match
bits. Its finite register selects the first matching address, looks up the two
fixed powered labels, and conjoins the bounded list of base predicates.

Both input and output bits use the graph-table unary natural-word codec.
The theorems below describe actual TM2 transitions, not assumed execution
costs. Producing this input block from live graph rotor lookups is a separate
frontend composition obligation; no graph table occurs in the machine's
finite transition function.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
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

/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingFinishRuntime

open Turing MaxCutGames.Foundations.Complexity
open PreprocessingRegularTables

def finish (H : PreprocessingTables.BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (2 * (d + internalDegree)) :=
  PreprocessingStageMaps.lazy (d + internalDegree)
    (PreprocessingStageMaps.paddedOverlay H d input)

end MaxCutGames.Foundations.PCP.PreprocessingFinishRuntime

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
-- module Solutions.OAIQ087_MC.MaxCut_PCP_TableIteration
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace MaxCutGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def output (H : BaseTable) (F : Formula) : Input := run H (iterationCount F) (initial F)

theorem output_val (H : BaseTable) (F : Formula) : (output H F).val = outputTable H F :=
  run_val H (iterationCount F) (initial F)

theorem output_darts_positive (H : BaseTable) (F : Formula) : 0 < (outputTable H F).darts := by
  rw [← output_val]
  exact (output H F).property

theorem gapMap_nonempty (H : BaseTable) (F : Formula) : (gapMap H F).clauses ≠ [] :=
  FinalTableFormula.nonempty (outputTable H F) (output_darts_positive H F)

end MaxCutGames.Foundations.PCP.TableIteration

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map's polynomial-time machine is certified separately. -/

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

namespace MaxCutGames.Foundations.Complexity.TableIterationFiniteAlphabet

open PCP MachineFiniteAlphabet

theorem initial : FiniteAlphabet MachineRawInitialTable.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

theorem finalCNF : FiniteAlphabet FinalCNFMachine.Program.computableInPolyTime.tm := by
  intro k
  change Finite Bool
  infer_instance

end MaxCutGames.Foundations.Complexity.TableIterationFiniteAlphabet

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

/-- Initial setup, the actual vertex loop, and the bridge to cleanup. -/
def preBudget (d n vertices inputLength : Nat) : Nat :=
  (3 * vertices + 5) +
    (vertices * (PoweringMachineVertex.budget d n inputLength + 2) + 1)

def totalBudget (d n pushBound tapeCount vertices inputLength : Nat) : Nat :=
  preBudget d n vertices inputLength +
    finishBudget d n pushBound tapeCount vertices inputLength
      (preBudget d n vertices inputLength)

theorem preBudget_mono_vertices (d n inputLength : Nat) {v w : Nat} (h : v ≤ w) :
    preBudget d n v inputLength ≤ preBudget d n w inputLength := by
  have hthree := Nat.mul_le_mul_left 3 h
  have hloop := Nat.mul_le_mul_right (PoweringMachineVertex.budget d n inputLength + 2) h
  unfold preBudget
  omega

theorem totalBudget_mono_vertices (d n pushBound tapeCount inputLength : Nat)
    {v w : Nat} (hvertices : v ≤ w) :
    totalBudget d n pushBound tapeCount v inputLength ≤
      totalBudget d n pushBound tapeCount w inputLength := by
  have hpre := preBudget_mono_vertices d n inputLength hvertices
  unfold totalBudget
  exact Nat.add_le_add hpre
    (finishBudget_mono d n pushBound tapeCount inputLength hvertices hpre)

end MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringRuntimeBudget
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finishing cost from the actual preceding machine execution

Every stack can grow by at most the fixed program's push bound in one
transition. Consequently an actual bounded execution from the standard input
configuration supplies the uniform stack bound needed by the finishing phase.
The bound below uses the same global machine for that preceding execution; no
separate tape-size hypothesis or numerical simulation is substituted for it.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringRuntimeBudget

open Turing

/-- Cleanup's concrete tape count is the size of the global tape enumeration. -/
abbrev tapeCount (radius : Nat) : Nat :=
  4 + (11 + PoweringMachineRowBody.capacity radius + 1)

/-- The actual global prefix execution supplies every finishing stack bound.
The physical header premises are used by `PoweringMachineFinish.traceAt`; this
arithmetic consequence of that prefix is valid for any two proposed header values. -/
theorem finish_steps_le_of_execution (d radius : Nat) (input : List Bool)
    (before : (PoweringMachineGlobal.machine d radius).Cfg)
    (priorBudget vertices darts : Nat)
    (prior : StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d radius).step
      (initList (PoweringMachineGlobal.machine d radius) input) (some before) priorBudget) :
    PoweringMachineFinish.steps (PoweringMachineGlobal.enumeration radius)
      (PoweringMachineGlobal.outputTape radius) before.stk vertices darts ≤
      2 * (vertices + darts) + 6 + tapeCount radius *
        (input.length + priorBudget * Runtime.programPushBound
          (PoweringMachineGlobal.machine d radius) + vertices + darts + 3) := by
  exact PoweringMachineFinish.steps_le_uniform (PoweringMachineGlobal.enumeration radius)
    (PoweringMachineGlobal.outputTape radius) before.stk vertices darts
    (input.length + priorBudget * Runtime.programPushBound (PoweringMachineGlobal.machine d radius))
    (stackLength_le_from_input (PoweringMachineGlobal.machine d radius) input before priorBudget prior)

end MaxCutGames.Foundations.Complexity.PoweringRuntimeBudget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
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

theorem beforeFinish_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (placement n) (beforeFinish graph n) :=
  PoweringMachineOuterLoop.finalTapes_ready graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _)
    (outputTape n) (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n)

theorem beforeFinish_output (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (outputTape n) =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_output graph n (placement n)
    (PoweringMachineInitialize.commonPlacement_injective _) (outputTape n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_finalOutput _ i))
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (PoweringInitializeFrame.prepared_ready graph n),
    PoweringMachineOuterLoop.prefixRows_all, PoweringInitializeFrame.prepared_output,
    List.append_nil]

theorem beforeFinish_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (headerVertices n) = encodeWord vertices := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_other graph n (placement n)
    (outputTape n) vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (headerVertices n) (PoweringGlobalConfiguration.headerVertices_ne_output n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header _ i .vertices (by decide)))]
  exact PoweringInitializeFrame.prepared_vertices graph n

theorem beforeFinish_darts (graph : PortTables.Table vertices d) (n : Nat) :
    beforeFinish graph n (headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := by
  rw [beforeFinish, PoweringMachineOuterLoop.finalTapes_other graph n (placement n)
    (outputTape n) vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)
    (headerDarts n) (PoweringGlobalConfiguration.headerDarts_ne_output n)
    (fun i => Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header _ i .darts (by decide)))]
  exact PoweringInitializeFrame.prepared_darts graph n

/-- The serialized result is exactly the actual powering table, including its
header and every relation bit, in the existing output codec. -/
theorem serialized_eq (graph : PortTables.Table vertices d) (n : Nat) :
    encodeWords [vertices, PoweringTableLayout.blockSize d n * vertices] ++
      beforeFinish graph n (outputTape n) = PoweringTables.outputBits graph n := by
  rw [beforeFinish_output, PoweringTableLayout.outputBits_vertexRows]
  congr 2
  rw [PoweringTableLayout.dartCount_eq_vertex_blocks, Nat.mul_comm]

/-- The actual final-copy/cleanup cost on the tapes obtained from the loop. -/
def finishSteps (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  PoweringMachineFinish.steps (enumeration n) (outputTape n) (beforeFinish graph n)
    vertices (PoweringTableLayout.blockSize d n * vertices)

end MaxCutGames.Foundations.Complexity.PoweringMachineRuntime

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RoundComputation
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual sequential finite-machine composition for the concrete numbered round.
The initial composition lemma isolates the preprocessing and powering execution
certificates with their shared bit codecs. The final endpoint supplies the
checked powering and alphabet machines, leaving only preprocessing explicit.
-/

namespace MaxCutGames.Foundations.PCP.RoundComputation

open Turing
open MaxCutGames.Foundations.Complexity

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

end MaxCutGames.Foundations.PCP.RoundComputation

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Hastad
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Outer.HastadSource

open MaxCutGames.Foundations Target Complexity PCP
open MaxCutGames.Reduction ActualSource
open MachineFiniteAlphabet

def gapInput (H : RoundTables.BaseTable) (F : Formula) :
    Hastad.SourceGeneratorContract.NonemptyFormula :=
  ⟨TableIteration.gapMap H F, TableIteration.gapMap_nonempty H F⟩

def output (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : SourceEncoding.Input :=
  sourceMap ξ hξ (gapInput H F)

noncomputable def sourceMachine (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime Hastad.SourceGeneratorContract.inputEncoding
      SourceEncoding.inputBits (sourceMap ξ hξ) :=
  Hastad.SourceGenerator.forErrorComputableInPolyTime PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ

end MaxCutGames.Outer.HastadSource

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Clone100Counting
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete clone sample space. Global distinctness is a stronger
conditioning rule than distinctness only at repeated original «variables».
It retains the same 3/100 bound and makes the number of copies uniform. -/

namespace MaxCutGames.Outer.SourceIncidence

open MaxCutGames.Reduction ActualSource
open MaxCutGames.Foundations Games Target PCP
open MaxCutGames.Soundness.IncidenceExtraction
open MaxCutGames.Clean.IncidenceGap
open scoped BigOperators

noncomputable section

def input (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : SourceEncoding.Input :=
  Clone100.clonedInput (HastadSource.output H ξ hξ F)

def source (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : Source := HastadSource.asSource (input H ξ hξ F)

theorem source_distinct (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : (source H ξ hξ F).DistinctNames :=
  Clone100.clonedSource_distinct (HastadSource.output H ξ hξ F)

end
end MaxCutGames.Outer.SourceIncidence

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BinaryParityReduction
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Outer.BinaryParityReduction

open MaxCutGames.Foundations Target Complexity PCP
open MaxCutGames.Reduction ActualSource
open MachineFiniteAlphabet

noncomputable section

def output (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (word : List Bool) : SourceEncoding.Input :=
  SourceIncidence.input H ξ hξ (BinaryLanguage.totalRename word)

end
end MaxCutGames.Outer.BinaryParityReduction

end OAI
end


