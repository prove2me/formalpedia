-- Prove2me | Definitions.Def_OAIQ081S134
-- name    : OAIQ081S134
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:44:30.528486+00:00
-- url     : https://prove2.me/theorems/a2c27587-952f-4538-8641-0450d3f384f5
-- title:
--   Definitions bundle OAIQ081S134 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 20 definitions, 3 inductive types or structures and 30 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.LooseMemory`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.cleaned`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.afterNormalize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixProgram.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.SetupReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Zip.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Zip.base`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.Context.Valid`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.callbackCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.effect`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.invariant`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.updated`, `OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.Context`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.baseState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.validPayload`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.resultState`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawInput.preparationContext`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_PackingIncidenceInputLoose`, `SubexponentialSAT_SqrtLog_PackingPrefixProgram`, `SubexponentialSAT_SqrtLog_PackingPrefixProgramLift`, `SubexponentialSAT_SqrtLog_PackingPrefixProgramRun`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup`, `SubexponentialSAT_SqrtLog_PackingProgramZip`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGate`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGateNative`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_OneHotAlphabetProgram`, `SubexponentialSAT_Subexp_PairPreparationBounds`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ScoreBuilderProgram`, `SubexponentialSAT_Subexp_ScoreBuilderRawInput`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102`, `OAIQ081S106`, `OAIQ081S110`, `OAIQ081S111` and `OAIQ081S113` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S147`, `OAIQ081S148`, `OAIQ081S149` and `OAIQ081S150`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S110
import Definitions.Def_OAIQ081S111
import Definitions.Def_OAIQ081S113

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionGenerateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Generating and evaluating collision tuples with fixed control

The alphabet and unary tuple depth are input data. The generator and collision
stream are linked through actual stack ports. The current word table and the
two selected read plans remain runtime inputs and are preserved.
-/

namespace SubexponentialSAT.Subexp.CollisionGenerateProgram

open BitProgram StackRoutines StructuredCalls

theorem generator_eval (current width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth stream : List Bool) :
    ∃ n ≤ TupleProgram.powerCost alphabet depth.length [[]] + 9,
      ∃ regs : Fin 10 → Bool, Eval generator n
        (inputState current width left right alphabet depth stream)
        (storedState regs current width left right (ProgramEncoding.encodeRecords alphabet) []
          (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet depth.length [[]]))
          [false] stream) := by
  let d := inputState current width left right alphabet depth stream
  let a : StructuredProgram.State 10 9 := ⟨d.regs, d.stacks ∘ generatorPorts⟩
  have ha : TupleProgram.outerInvariant alphabet depth false a := by
    simp [a, d, inputState, storedState, generatorPorts, TupleProgram.outerInvariant]
  obtain ⟨b, hb, n, hn, ht⟩ := TupleProgram.generateProgram_runsIn alphabet depth false a ha
    (by simp [a, d, inputState, storedState, generatorPorts])
    (by simp [a, d, inputState, storedState, generatorPorts])
    (by simp [a, d, inputState, storedState, generatorPorts])
  have hin : embedState id generatorPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id generatorPorts_injective
    · intro i; rfl
    · intro i; rfl
    · intros; rfl
    · intros; rfl
  rcases hb with ⟨⟨hb1, hb3, hb4, hb6, hb7, hb8, _⟩, hb0, hb2, hb5⟩
  have hout : embedState id generatorPorts d b =
      storedState b.regs current width left right (ProgramEncoding.encodeRecords alphabet) []
        (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet depth.length [[]]))
        [false] stream := by
    apply embedState_eq _ _ Function.injective_id generatorPorts_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [storedState, generatorPorts, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8]
    · intro j hj
      exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      have h16 : j ≠ 16 := fun h => hj ⟨0, by simpa [generatorPorts] using h.symm⟩
      have h17 : j ≠ 17 := fun h => hj ⟨8, by simpa [generatorPorts] using h.symm⟩
      have h6 : j ≠ 6 := fun h => hj ⟨5, by simpa [generatorPorts] using h.symm⟩
      simp [d, inputState, storedState, h16, h17, h6]
  have he := eval_call_lifted TupleProgram.generateProgram id generatorPorts d
    Function.injective_id generatorPorts_injective ht
  exact ⟨n, hn, b.regs, by simpa only [hin, hout, generator] using he⟩

theorem program_run (current : List (List Bool)) (width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth stream : List Bool)
    (hv : ∀ bits ∈ TupleProgram.powerRows alphabet depth.length [[]],
      CollisionTupleProgram.validPayload current width.length left right bits) :
    RunsIn program (sourceBudget current.flatten width.length left right alphabet depth.length)
      ((inputState current.flatten width left right alphabet depth stream).withPC (some program.entry))
      ((outputState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
        (CollisionTupleProgram.streamed current.flatten width.length left right
          (TupleProgram.powerRows alphabet depth.length [[]]) stream)).withPC none) := by
  obtain ⟨n, hn, regs, hg⟩ := generator_eval current.flatten width left right alphabet depth stream
  have hc := clearWork_eval regs current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
    (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet depth.length [[]])) stream
  have hr := reset_eval (storedState (readRegs regs 0 1 none) current.flatten width left right
    (ProgramEncoding.encodeRecords alphabet) []
    (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet depth.length [[]])) [] stream)
  obtain ⟨m, hm, hs⟩ := stream_eval current width left right (ProgramEncoding.encodeRecords alphabet)
    (TupleProgram.powerRows alphabet depth.length [[]]) stream hv
  have he : Eval command (n + (5 + (10 + m)))
      (inputState current.flatten width left right alphabet depth stream)
      (outputState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
        (CollisionTupleProgram.streamed current.flatten width.length left right
          (TupleProgram.powerRows alphabet depth.length [[]]) stream)) :=
    hg.seq (hc.seq (hr.seq hs))
  exact ⟨n + (5 + (10 + m)) + 1, by dsimp [sourceBudget]; omega,
    compiled_halt_trace he 19 11⟩

/-- The generated tuples' schema is proved from the input word widths; no
assumption about a generated callback result is needed. -/
theorem program_run_uniform (current : List (List Bool)) (width : List Bool) (left right : List ℕ)
    (alphabet : List (List Bool)) (depth stream : List Bool)
    (hc : ∀ row ∈ current, row.length = width.length)
    (ha : ∀ row ∈ alphabet, row.length = width.length)
    (hl : ∀ i ∈ left, i < current.length + depth.length)
    (hr : ∀ i ∈ right, i < current.length + depth.length) :
    RunsIn program (sourceBudget current.flatten width.length left right alphabet depth.length)
      ((inputState current.flatten width left right alphabet depth stream).withPC (some program.entry))
      ((outputState current.flatten width left right (ProgramEncoding.encodeRecords alphabet)
        (CollisionTupleProgram.streamed current.flatten width.length left right
          (TupleProgram.powerRows alphabet depth.length [[]]) stream)).withPC none) :=
  program_run current width left right alphabet depth stream
    (generated_validPayload current alphabet width.length depth.length left right hc ha hl hr)

end SubexponentialSAT.Subexp.CollisionGenerateProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Aggregating the actual collision streams of all vertex pairs

The fixed program consumes framed pairs of already selected read plans.
Producing those selected plans from original plans and the remaining-index
table is a separate preparation step.  Every pair invokes the actual tuple
generator and collision machine; a final fixed unary tally produces the score.
-/

namespace SubexponentialSAT.Subexp.PairScoreProgram

open BitProgram StackRoutines StructuredCalls

theorem streamedPairs_length (ctx : Context) (pairs : List PlanPair) (stream : List Bool) :
    (streamedPairs ctx pairs stream).length =
      pairs.length * ctx.alphabet.length ^ ctx.depth.length + stream.length := by
  induction pairs generalizing stream with
  | nil => simp [streamedPairs]
  | cons pair pairs ih =>
    change (streamedPairs ctx pairs (pairStream ctx pair stream)).length = _
    rw [ih, pairStream_length]
    simp only [List.length_cons]
    ring

theorem score_le_leafCount (ctx : Context) (pairs : List PlanPair) :
    score ctx pairs ≤ pairs.length * ctx.alphabet.length ^ ctx.depth.length := by
  have h := List.length_filter_le id (streamedPairs ctx pairs [])
  simpa [score, PaddedCompletion.trueCount, PaddedCompletion.successful,
    streamedPairs_length] using h

def validPayload (ctx : Context) (bits : List Bool) : Prop :=
  ∃ pair : PlanPair, bits = pairBytes pair ∧ ValidPair ctx pair

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control candidate scoring

Score records are accumulated as reversed serialized bytes and reversed once
at the end, so output score order agrees with the input candidate order.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem resetLow_eval (a : State 16 36) : Eval resetLow 13 a (resetLowState a) := by
  simpa [resetLow,resetLowState] using
    Eval.base (resetList_eval ((List.finRange 13).map lowRegisters) a)

theorem embed_eq {r s R S : ℕ} (ρ : Fin r → Fin R) (σ : Fin s → Fin S)
    (frame : State R S) (small : State r s) (large : State R S)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (hr : ∀ i, large.regs (ρ i) = small.regs i)
    (hs : ∀ i, large.stacks (σ i) = small.stacks i)
    (hfr : ∀ i, (¬ ∃ j, ρ j = i) → large.regs i = frame.regs i)
    (hfs : ∀ i, (¬ ∃ j, σ j = i) → large.stacks i = frame.stacks i) :
    embedState ρ σ frame small = large := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, ρ j = i
    · obtain ⟨j,rfl⟩ := h
      exact (embedState_register ρ σ frame small hρ j).trans (hr j).symm
    · exact (embedState_register_frame ρ σ frame small i h).trans (hfr i h).symm
  · funext i
    by_cases h : ∃ j, σ j = i
    · obtain ⟨j,rfl⟩ := h
      exact (embedState_stack ρ σ frame small hσ j).trans (hs j).symm
    · exact (embedState_stack_frame ρ σ frame small i h).trans (hfs i h).symm

structure Context.Valid (ctx : Context) : Prop where
  index_length : ctx.index.length = ctx.before.length
  before_width : ∀ row ∈ ctx.before, row.length = ctx.width.length
  old_width : ctx.old.length = ctx.width.length
  after_width : ∀ row ∈ ctx.after, row.length = ctx.width.length
  alphabet_width : ∀ row ∈ ctx.alphabet, row.length = ctx.width.length
  candidate_width : ∀ row ∈ ctx.candidates, row.length = ctx.width.length
  pairs_valid : ∀ pair ∈ ctx.pairs, PairScoreProgram.ValidPair (pairContext ctx ctx.old) pair

def updated (ctx : Context) (candidate : List Bool) : List Bool :=
  ctx.before.flatten ++ (candidate ++ ctx.after.flatten)

theorem pairContext_valid (ctx : Context) (hc : ctx.Valid) (candidate : List Bool)
    (hw : candidate.length = ctx.width.length) : (pairContext ctx candidate).Valid := by
  refine ⟨?_,hc.alphabet_width⟩
  intro row hr
  simp only [pairContext,List.mem_append,List.mem_cons] at hr
  rcases hr with hr | rfl | hr
  · exact hc.before_width row hr
  · exact hw
  · exact hc.after_width row hr

theorem pairContext_pairs (ctx : Context) (hc : ctx.Valid) (candidate : List Bool) :
    ∀ pair ∈ ctx.pairs, PairScoreProgram.ValidPair (pairContext ctx candidate) pair := by
  intro pair hp
  simpa [PairScoreProgram.ValidPair,pairContext] using hc.pairs_valid pair hp

theorem transferCandidate_eval (ctx : Context) (regs : Fin 16 → Bool)
    (tail builder candidate : List Bool) :
    Eval transferCandidate (3 * candidate.length + 3)
      (RecordPrograms.state outerPorts (baseState ctx regs builder)
        false true false tail candidate.reverse)
      (workState ctx
        (readRegs (RecordPrograms.state outerPorts (baseState ctx regs builder)
          false true false tail candidate.reverse).regs 0 1 none)
        tail candidate [] [] [] builder) := by
  have h := TupleProgram.transfer_eval 34 27 0 1 (by decide) (by decide)
    (RecordPrograms.state outerPorts (baseState ctx regs builder)
      false true false tail candidate.reverse)
  convert h using 1
  · simp [RecordPrograms.state,outerPorts]
  · apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [workState,baseState,StackRoutines.transferStacks,
      RecordPrograms.state,outerPorts]

theorem updateCandidate_eval (ctx : Context) (hc : ctx.Valid) (regs : Fin 16 → Bool)
    (tail builder candidate : List Bool) (hw : candidate.length = ctx.width.length) :
    Eval updateCandidate
      (CandidateArrayProgram.sourceCost (original ctx).length ctx.before.length ctx.width.length)
      (workState ctx regs tail candidate [] [] [] builder)
      (workState ctx (readRegs regs 0 1 none) tail candidate (updated ctx candidate) [] [] builder) := by
  let a := workState ctx regs tail candidate [] [] [] builder
  let smallIn := CandidateArrayProgram.state (regs ∘ arrayRegisters)
    (original ctx) candidate ctx.index ctx.width [] []
  let smallOut := CandidateArrayProgram.state (readRegs (regs ∘ arrayRegisters) 0 1 none)
    (original ctx) candidate ctx.index ctx.width (updated ctx candidate) []
  have hin : embedState arrayRegisters arrayStacks a smallIn = a := by
    apply embed_eq _ _ _ _ _ arrayRegisters_injective arrayStacks_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> simp [a,smallIn,workState,arrayStacks]
    · intros; rfl
    · intros; rfl
  have hout : embedState arrayRegisters arrayStacks a smallOut =
      workState ctx (readRegs regs 0 1 none) tail candidate (updated ctx candidate) [] [] builder := by
    apply embed_eq _ _ _ _ _ arrayRegisters_injective arrayStacks_injective
    · intro i
      fin_cases i <;> simp [smallOut,workState,arrayRegisters,readRegs]
    · intro i
      fin_cases i <;> simp [smallOut,workState,arrayStacks]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [arrayRegisters] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,by simpa [arrayRegisters] using h.symm⟩
      simp [workState,a,readRegs,h0,h1]
    · intro i hi
      have h13 : i ≠ 13 := fun h => hi ⟨8,by simpa [arrayStacks] using h.symm⟩
      simp [workState,a,h13]
  have ht := CandidateArrayProgram.program_trace (regs ∘ arrayRegisters)
    ctx.before ctx.old candidate ctx.after.flatten ctx.index ctx.width
    hc.index_length hc.before_width hc.old_width hw
  have he := eval_call_lifted CandidateArrayProgram.program arrayRegisters arrayStacks a
    arrayRegisters_injective arrayStacks_injective ht
  change Eval updateCandidate
    (CandidateArrayProgram.sourceCost (original ctx).length ctx.before.length ctx.width.length)
    (embedState arrayRegisters arrayStacks a smallIn)
    (embedState arrayRegisters arrayStacks a smallOut) at he
  rw [hin,hout] at he
  exact he

theorem copyPairs_eval (ctx : Context) (regs : Fin 16 → Bool)
    (tail builder candidate current : List Bool) :
    Eval copyPairs (7 * (PairScoreProgram.pairRecords ctx.pairs).length + 5)
      (workState ctx regs tail candidate current [] [] builder)
      (workState ctx (readRegs regs 0 1 none) tail candidate current []
        (PairScoreProgram.pairRecords ctx.pairs) builder) := by
  have h := TupleProgram.copy_eval 31 20 33 0 1 (by decide) (by decide)
    (by decide) (by decide) (workState ctx regs tail candidate current [] [] builder)
    (by simp [workState])
  convert h using 1
  · simp [workState]
  · apply congrArg₂ StructuredProgram.State.mk rfl
    funext j; fin_cases j <;> simp [workState,StackRoutines.copyStacks]

theorem resetLow_work (ctx : Context) (regs : Fin 16 → Bool)
    (tail builder candidate current : List Bool)
    (h13 : regs 13 = false) (h14 : regs 14 = true) (h15 : regs 15 = false) :
    Eval resetLow 13
      (workState ctx regs tail candidate current [] (PairScoreProgram.pairRecords ctx.pairs) builder)
      (workState ctx pairStartRegs tail candidate current [] (PairScoreProgram.pairRecords ctx.pairs) builder) := by
  have h := resetLow_eval
    (workState ctx regs tail candidate current [] (PairScoreProgram.pairRecords ctx.pairs) builder)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;>
      simp [resetValues_apply,lowRegisters,List.mem_map,
        Fin.exists_fin_succ,workState,pairStartRegs,h13,h14,h15]
  · rfl

def callbackCost (ctx : Context) (candidate : List Bool) : ℕ :=
  CandidateArrayProgram.sourceCost (original ctx).length ctx.before.length ctx.width.length +
    PairScoreProgram.sourceBudget (pairContext ctx candidate) ctx.pairs +
    4 * candidateScore ctx candidate + 5 * candidate.length + 2 * (updated ctx candidate).length +
    7 * (PairScoreProgram.pairRecords ctx.pairs).length + 35

def invariant (ctx : Context) (a : State 16 36) : Prop :=
  ∃ regs builder, a = baseState ctx regs builder

def effect (ctx : Context) (candidate : List Bool) (a b : State 16 36) : Prop :=
  b.stacks 35 = reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) (a.stacks 35)

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ActivePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Computing the active completion positions

A fixed program filters a runtime list of unary seed positions. It retains a
position precisely when it is at least the runtime threshold and belongs to
the runtime pair read plan. The plan and threshold are preserved. Applying the
program to the complete ascending seed list gives a duplicate-free completion
plan in ascending order.
-/

namespace SubexponentialSAT.Subexp.ActivePlanProgram

open BitProgram StructuredCalls StackRoutines

theorem emit_eval (bits source plan threshold acc output : List Bool) (regs : Regs) :
    Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps (regs 9) bits + 1)
      (state regs source plan threshold acc bits.reverse output)
      (state (flags regs false true false) source plan threshold
        (if regs 9 then true :: (Encoding.frame bits ++ acc) else acc) [] output) := by
  have ht := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStack
    (state regs source plan threshold acc bits.reverse output) emitRegs_injective emitStack_injective
    (SubexpNormalizeProgram.emitIfSelected_trace (regs 9) bits source threshold acc (regs 0) (regs 1))
  simpa only [embed_emit, flags_self, emit] using ht

set_option maxHeartbeats 1600000 in
theorem callback_eval (records : List (List Bool))
    (bits source threshold acc output : List Bool) (regs : Regs) :
    ∃ n ≤ callbackCost records threshold bits, ∃ rf : Regs,
      rf 7 = regs 7 ∧ rf 8 = regs 8 ∧ rf 9 = false ∧
      Eval callback n
        (state regs source (Encoding.encodeList id records) threshold acc bits.reverse output)
        (state rf source (Encoding.encodeList id records) threshold
          (if keep records threshold bits then true :: (Encoding.frame bits ++ acc) else acc)
          [] output) := by
  obtain ⟨n, hn, ra, ha, hframea, hea⟩ := member_eval records bits source threshold acc output regs
  obtain ⟨m, hm, rb, hb, hframeb, heb⟩ :=
    compare_eval bits source (Encoding.encodeList id records) threshold acc output ra
  let rc := Function.update rb 9 (rb 4 && rb 3)
  have hc : Eval (RecordPrograms.atom (.band 9 4 3)) 1
      (state rb source (Encoding.encodeList id records) threshold acc bits.reverse output)
      (state rc source (Encoding.encodeList id records) threshold acc bits.reverse output) :=
    .base (.atom _ _)
  have hselect : rc 9 = keep records threshold bits := by
    simp [rc, keep, hframeb 4 (by decide), ha, hb, Bool.and_comm]
  have hec := emit_eval bits source (Encoding.encodeList id records) threshold acc output rc
  rw [hselect] at hec
  refine ⟨_, ?_, flags rc false true false, ?_, ?_, ?_, hea.seq (heb.seq (hc.seq hec))⟩
  · have he := SubexpNormalizeProgram.emitIfSelected_steps_le (keep records threshold bits) bits
    dsimp [callbackCost]
    omega
  · simp [flags, rc, hframeb 7 (by decide), hframea 7 (by decide)]
  · simp [flags, rc, hframeb 8 (by decide), hframea 8 (by decide)]
  · simp [flags]

theorem callback_contract (records : List (List Bool)) (threshold : List Bool) :
    RecordPrograms.CallbackContractWith ports callback (fun _ => false)
      (callbackCost records threshold) (invariant records threshold)
      (SubexpNormalizeProgram.FilterEffect 8 (keep records threshold)) := by
  intro bits tail base hbase
  rcases hbase with ⟨regs, source, acc, query, rfl⟩
  obtain ⟨n, hn, rf, h7, h8, h9, he⟩ :=
    callback_eval records bits tail threshold acc [] (outerFlags regs false true false)
  let next := state rf tail (Encoding.encodeList id records) threshold
    (if keep records threshold bits then true :: (Encoding.frame bits ++ acc) else acc) [] []
  have hnext : RecordPrograms.state ports next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self
    · simpa [next, state, ports, outerFlags] using h7
    · simpa [next, state, ports, outerFlags] using h8
    · exact h9
    · rfl
    · rfl
  refine ⟨n, next, hn, ⟨rf, tail, _, [], rfl⟩, ?_, ?_⟩
  · rfl
  · rw [hnext, recordState_state]
    exact he

theorem filter_eval (records seeds : List (List Bool)) (threshold : List Bool) (regs : Regs) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost records threshold) seeds, ∃ rf : Regs,
      Eval (RecordPrograms.iterate ports callback) n
        (state regs (Encoding.encodeList id seeds) (Encoding.encodeList id records) threshold [false] [] [])
        (state rf [] (Encoding.encodeList id records) threshold
          (Encoding.encodeList id (seeds.filter (keep records threshold)).reverse) [] []) := by
  let base := state regs (Encoding.encodeList id seeds) (Encoding.encodeList id records)
    threshold [false] [] []
  have hb : invariant records threshold base := ⟨regs, _, _, _, rfl⟩
  obtain ⟨n, next, hn, hnext, hout, he⟩ := SubexpNormalizeProgram.filter_iterate_run
    ports callback (keep records threshold) (callbackCost records threshold)
    (invariant records threshold) 8 (by decide) (by decide)
    (callback_contract records threshold) seeds [] [] base hb rfl (regs 7) (regs 8) (regs 9)
  rcases hnext with ⟨rr, ss, aa, qq, rfl⟩
  have haa : aa = Encoding.encodeList id (seeds.filter (keep records threshold)).reverse := by
    simpa [recordState_state, state] using hout
  rw [haa] at he
  refine ⟨n, hn, outerFlags rr false true false, ?_⟩
  simpa only [base, List.append_nil, recordState_state, outerFlags_self] using he

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preparing all selected pair plans once per assignment step

The fixed program preserves the full seed-index records, original pair
records, seed count, and processed counter. It computes the next cutoff,
builds each pair's actual selection table, and emits selected pair records.
The candidate value is not an input to this preparation phase.
-/

namespace SubexponentialSAT.Subexp.PairPreparationProgram

open BitProgram StructuredCalls StackRoutines

structure Context where
  seedCount : ℕ
  processedBits : List Bool
  pairs : List PlanPair

/-- Only the four immutable inputs are populated initially. In particular,
processed bits are arbitrary; their length is the logical processed count. -/
def inputState (ctx : Context) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun j =>
    if j = 30 then seedBytes ctx.seedCount
    else if j = 31 then PairScoreProgram.pairRecords ctx.pairs
    else if j = 32 then SelectionTableProgram.unary ctx.seedCount
    else if j = 33 then ctx.processedBits else []⟩

def baseState (ctx : Context) (acc : List Bool) : Data :=
  ⟨fun _ => false, fun j =>
    if j = 7 then true :: ctx.processedBits
    else if j = 29 then acc else (inputState ctx (fun _ => false)).stacks j⟩

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual once-per-step pair preparation
program. The common parameter bounds physical input lengths and record count. -/

namespace SubexponentialSAT.Subexp.PairPreparationBounds

open BitProgram PairPreparationProgram

theorem pair_plan_lengths (pair : PlanPair) :
    (CollisionStreamProgram.planBytes pair.1).length ≤ (PairScoreProgram.pairBytes pair).length ∧
      (CollisionStreamProgram.planBytes pair.2).length ≤ (PairScoreProgram.pairBytes pair).length := by
  simp only [PairScoreProgram.pairBytes, List.length_append, Encoding.length_frame]
  omega

theorem seedBytes_length_le (M : ℕ) : (seedBytes M).length ≤ 3 * (M + 1)^2 := by
  have h := planBytes_le (List.range M) M (fun n hn => Nat.le_of_lt (List.mem_range.mp hn))
  change (seedBytes M).length ≤ _ at h
  simp only [List.length_range] at h
  nlinarith

theorem unionBytes_le (pair : PlanPair) :
    (CollisionStreamProgram.planBytes (pair.1.reverse ++ pair.2)).length ≤
      (CollisionStreamProgram.planBytes pair.1).length +
        (CollisionStreamProgram.planBytes pair.2).length := by
  simp only [planBytes_length, List.sum_append, List.sum_reverse, List.length_append,
    List.length_reverse]
  omega

theorem activeCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hb : (PairScoreProgram.pairBytes pair).length ≤ B) :
    ActivePlanProgram.traceBoundThreshold (List.range ctx.seedCount)
      (pair.1.reverse ++ pair.2) (true :: ctx.processedBits) ≤ 4096 * (B + 1)^4 := by
  have hu := unionBytes_le pair
  have hl := (pair_plan_lengths pair).1.trans hb
  have hr := (pair_plan_lengths pair).2.trans hb
  have hseed : (seedBytes ctx.seedCount).length ≤ 3 * (B + 1)^2 :=
    (seedBytes_length_le _).trans (by gcongr)
  have h := ActivePlanProgram.sourceBound_le
    (ActivePlanProgram.indexRecords (pair.1.reverse ++ pair.2))
    (ActivePlanProgram.indexRecords (List.range ctx.seedCount)) (true :: ctx.processedBits)
  change ActivePlanProgram.traceBoundThreshold _ _ _ ≤
    256 * ((CollisionStreamProgram.planBytes (pair.1.reverse ++ pair.2)).length +
      (true :: ctx.processedBits).length + 1) * ((seedBytes ctx.seedCount).length + 1) at h
  have hu' : (CollisionStreamProgram.planBytes (pair.1.reverse ++ pair.2)).length ≤ 2 * B := by omega
  have hp' : (true :: ctx.processedBits).length ≤ B + 1 := by simpa using Nat.add_le_add_right hp 1
  calc
    _ ≤ 256 * (2 * B + (B + 1) + 1) * (3 * (B + 1)^2 + 1) := h.trans (by gcongr)
    _ ≤ _ := by ring_nf; omega

end SubexponentialSAT.Subexp.PairPreparationBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual global candidate-score builder

Pair read plans are prepared once for the current processed position. The
candidate loop then executes the local collision enumeration and emits scores
in candidate order. A final fixed routine restores the temporary table ports.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderProgram

open BitProgram StructuredCalls

def resultState (d : Data) (regs : Fin 16 → Bool) (scores : List Bool) : Data :=
  ⟨regs, Function.update d.stacks 0 scores⟩

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderRawInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Score-builder inputs from physically generated raw pair plans

The runtime pair table is retained in its actual generated order. A
permutation proof connects that order to the mathematical vertex-pair list;
the code never decodes plans back to vertex identifiers.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderRawInput

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

def preparationContext (seedCount : ℕ) (rawPlans : List PairScoreProgram.PlanPair)
    (d : ScoreBuilderProgram.Data) : PairPreparationProgram.Context where
  seedCount := seedCount
  processedBits := d.stacks 19
  pairs := rawPlans

end SubexponentialSAT.Subexp.ScoreBuilderRawInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputLoose
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The incidence scorer does not touch controller storage on ports 12--18. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.PackingIncidenceProgram

structure LooseMemory {r Q : ℕ} (a : Word r Q) (fixed : List (Word r Q))
    (n : ℕ) (d : ScoreBuilderProgram.Data) : Prop where
  assignment : d.stacks 8 =
    (fixed.reverse.map ReadPlan.encodeWord ++ List.replicate (n+1) (ReadPlan.encodeWord a)).flatten
  width : (d.stacks 10).length = ReadPlan.wordWidth r Q
  processed : (d.stacks 19).length = fixed.length
  scratch : ∀ j : Fin 48, j.val < 8 → d.stacks j = []

def cleaned {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (d : ScoreBuilderProgram.Data) : ScoreBuilderProgram.Data :=
  ⟨d.regs, fun j => if j ∈ SequentialProgram.scratchPorts then []
    else if j = 9 then ((a::tail).map ReadPlan.encodeWord).flatten else d.stacks j⟩

theorem cleaned_memory {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n : ℕ) (d : ScoreBuilderProgram.Data) (hm : LooseMemory a fixed n d) :
    SequentialProgram.Memory ReadPlan.encodeWord a tail (n+1) fixed (cleaned a tail d).stacks := by
  constructor
  · simpa [cleaned, SequentialProgram.scratchPorts] using hm.assignment
  · simp [cleaned, SequentialProgram.scratchPorts]
  · simpa [cleaned, SequentialProgram.scratchPorts, ReadPlan.encodeWord_length] using hm.width
  · simpa [cleaned, SequentialProgram.scratchPorts] using hm.processed
  · intro j hj; simp [cleaned, hj]

theorem cleaned_high {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (d : ScoreBuilderProgram.Data) (env : Fin 48 → List Bool)
    (hh : SequentialProgram.HighState env d.stacks) :
    SequentialProgram.HighState env (cleaned a tail d).stacks := by
  intro j hj
  have hnot : j ∉ SequentialProgram.scratchPorts := by
    have hs : ∀ k ∈ SequentialProgram.scratchPorts, k.val < 20 := by decide
    exact fun h => (Nat.not_le_of_lt (hs j h)) hj
  have h9 : j ≠ 9 := by intro h; subst j; omega
  simpa [cleaned, hnot, h9] using hh j hj

end SubexponentialSAT.SqrtLog.PackingIncidenceInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid prefix preparation. Raw unary inputs may contain arbitrary bits;
only their lengths matter. The persistent table and both counters survive. -/

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

def afterNormalize (out : Fin 11) (a : Data) : Data :=
  ⟨fun _ => false, Function.update (Function.update a.stacks 5 []) out
    (unary (a.stacks 5).length ++ a.stacks out)⟩

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

/-- Three persistent inputs and eight initially empty output/work stacks. -/
def input (regs : Fin 3 → Bool) (table count width : List Bool) : Data :=
  ⟨regs, ![table,count,width,[],[],[],[],[],[],[],[]]⟩

def output (regs : Fin 3 → Bool) (table count width : List Bool) : Data :=
  ⟨regs, ![table,count,width,table.take (count.length * width.length),
    unary count.length,[],[],[],[],[],[]]⟩

def copied (source target : Fin 11) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks source target a.stacks⟩

def cleared (stack : Fin 11) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks stack a.stacks⟩

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls

def Ready {r s : ℕ} (p : Ports r s) (before after : State r s) : Prop :=
  (∀ i : Fin 3, after.stacks (p.stack ⟨i.val, by omega⟩) =
    before.stacks (p.stack ⟨i.val, by omega⟩)) ∧
  after.stacks (p.stack 3) = (before.stacks (p.stack 0)).take
    ((before.stacks (p.stack 1)).length * (before.stacks (p.stack 2)).length) ∧
  after.stacks (p.stack 4) = unary (before.stacks (p.stack 1)).length ∧
  (∀ i : Fin 11, 5 ≤ i.val → after.stacks (p.stack i) = []) ∧
  (∀ i, (∀ j, p.stack j ≠ i) → after.stacks i = before.stacks i) ∧
  (∀ i, (∀ j, p.register j ≠ i) → after.regs i = before.regs i)

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem copy_eval (d : Data) (src dst : Fin 7) (hne : src ≠ dst)
    (hs : src ≠ 6) (ht : (6 : Fin 7) ≠ dst) (h6 : d.stacks 6 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 6 0 1 hne hs ht (by decide)
    d.regs d.stacks h6)

theorem clear_eval (d : Data) (j : Fin 7) :
    Eval (clear j) (2 * (d.stacks j).length + 3) d (cleared d j) :=
  .call _ (ListRegisterProgram.clear_run j 0 1 d.regs d.stacks)

theorem convert_eval (d : Data) (h4 : d.stacks 4 = []) (h6 : d.stacks 6 = []) :
    ∃ t ≤ CounterConversions.runtimeBound (d.stacks 3), ∃ e : Data,
      Eval convert t d e ∧ e.stacks 3 = [] ∧
      e.stacks 4 = List.replicate (CounterPrograms.value (d.stacks 3)) true ∧
      (∀ j, j ≠ 3 → j ≠ 4 → e.stacks j = d.stacks j) := by
  let a := projectState unaryRegisters unaryStacks d
  obtain ⟨t, ht, hb⟩ := CounterConversions.unary_correct a h6
  let b := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (a.stacks 0)) true ++ a.stacks 1)
  let e := embedState unaryRegisters unaryStacks d b
  have he := eval_liftCommand_from_state CounterConversions.unaryCmd 0 1
    unaryRegisters unaryStacks d unaryRegisters_injective unaryStacks_injective ht
  have hbound := CounterConversions.coreBound_le (d.stacks 3)
  change t ≤ CounterConversions.coreBound (d.stacks 3) at hb
  refine ⟨t+1, by omega, e, he, ?_, ?_, ?_⟩
  · exact embedState_stack unaryRegisters unaryStacks d b unaryStacks_injective 0
  · have h := embedState_stack unaryRegisters unaryStacks d b unaryStacks_injective 1
    simpa [e, b, a, projectState, unaryStacks, CounterConversions.state, h4] using h
  · intro j hj3 hj4
    by_cases hj6 : j = 6
    · subst j
      have h := embedState_stack unaryRegisters unaryStacks d b unaryStacks_injective 2
      simpa [e, b, unaryStacks, CounterConversions.state, h6] using h
    · apply embedState_stack_frame
      rintro ⟨i, rfl⟩
      fin_cases i <;> simp [unaryStacks] at hj3 hj4 hj6

theorem compare_eval (d : Data) :
    ∃ t ≤ 4 * min (d.stacks 4).length (d.stacks 5).length + 6, ∃ e : Data,
      Eval compare t d e ∧
      e.regs 3 = decide ((d.stacks 4).length ≤ (d.stacks 5).length) ∧
      (e.stacks 4).length ≤ (d.stacks 4).length ∧
      (e.stacks 5).length ≤ (d.stacks 5).length ∧
      (∀ j, j ≠ 4 → j ≠ 5 → e.stacks j = d.stacks j) := by
  obtain ⟨t, hb, c, ht, hpc, hf⟩ := Subexp.UnaryCompare.runs d.regs (d.stacks 4) (d.stacks 5)
  let a : State 4 2 := ⟨c.regs, c.stacks⟩
  have hc : a.withPC none = c := by cases c; simp_all [a, StructuredProgram.State.withPC]
  have hp : Subexp.UnaryCompare.start d.regs (d.stacks 4) (d.stacks 5) =
      (projectState id compareStacks d).withPC (some Subexp.UnaryCompare.program.entry) := by
    change Cfg.mk _ _ _ = Cfg.mk _ _ _
    congr 1
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [hp, ← hc] at ht
  let e := embedState id compareStacks d a
  have he := eval_call_from_state Subexp.UnaryCompare.program id compareStacks d
    Function.injective_id compareStacks_injective ht
  have hs (i : Fin 2) : e.stacks (compareStacks i) = c.stacks i :=
    embedState_stack _ _ _ _ compareStacks_injective i
  refine ⟨t, hb, e, he, ?_, ?_, ?_, ?_⟩
  · exact (embedState_register _ _ _ _ Function.injective_id 3).trans hf
  · have h := Subexp.UnaryCompare.trace_length_le ht 0
    change (c.stacks 0).length ≤ (d.stacks 4).length at h
    have he : e.stacks 4 = c.stacks 0 := by simpa [compareStacks] using hs 0
    rw [he]
    exact h
  · have h := Subexp.UnaryCompare.trace_length_le ht 1
    change (c.stacks 1).length ≤ (d.stacks 5).length at h
    have he : e.stacks 5 = c.stacks 1 := by simpa [compareStacks] using hs 1
    rw [he]
    exact h
  · intro j hj4 hj5
    apply embedState_stack_frame
    rintro ⟨i, rfl⟩
    fin_cases i <;> simp [compareStacks] at hj4 hj5

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramGate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem choose_eval (d : Data) (h2 : d.stacks 2 = []) (h6 : d.stacks 6 = []) :
    ∃ t ≤ 7 * (d.stacks 1).length + 6, ∃ e : Data,
      Eval choose t d e ∧
      e.stacks 2 = (if d.regs 3 then [] else d.stacks 1) ∧
      (∀ j, j ≠ 2 → e.stacks j = d.stacks j) := by
  cases hr : d.regs 3 with
  | true =>
      exact ⟨1, by omega, d, .ite_true hr (.base (.skip d)), by simp [ h2],
        fun _ _ => rfl⟩
  | false =>
      refine ⟨7 * (d.stacks 1).length + 5 + 1, by omega, copied d 1 2,
        .ite_false hr (copy_eval d 1 2 (by decide) (by decide) (by decide) h6), ?_, ?_⟩
      · simp [copied, StackRoutines.copyStacks, h2]
      · intro j hj; simp [copied, StackRoutines.copyStacks, hj]

theorem command_eval (d : Data) (hd : ready d) :
    ∃ t ≤ budget d, ∃ z : Data, Eval command t d z ∧ z.stacks 2 = output d ∧
      (∀ j, j ≠ 2 → z.stacks j = d.stacks j) := by
  let a := copied d 0 3
  have ha := copy_eval d 0 3 (by decide) (by decide) (by decide) (hd 6 (by decide))
  have ha3 : a.stacks 3 = d.stacks 0 := by simp [a, copied, StackRoutines.copyStacks, hd 3 (by decide)]
  have haf (j : Fin 7) (hj : j ≠ 3) : a.stacks j = d.stacks j := by
    simp [a, copied, StackRoutines.copyStacks, hj]
  obtain ⟨tu, htu, b, hu, hb3, hb4, hbf⟩ := convert_eval a
    ((haf 4 (by decide)).trans (hd 4 (by decide)))
    ((haf 6 (by decide)).trans (hd 6 (by decide)))
  rw [ha3] at htu hb4
  have hb1 : b.stacks 1 = d.stacks 1 := (hbf 1 (by decide) (by decide)).trans (haf 1 (by decide))
  have hb2 : b.stacks 2 = [] := (hbf 2 (by decide) (by decide)).trans
    ((haf 2 (by decide)).trans (hd 2 (by decide)))
  have hb5 : b.stacks 5 = [] := (hbf 5 (by decide) (by decide)).trans
    ((haf 5 (by decide)).trans (hd 5 (by decide)))
  have hb6 : b.stacks 6 = [] := (hbf 6 (by decide) (by decide)).trans
    ((haf 6 (by decide)).trans (hd 6 (by decide)))
  let c := copied b 1 5
  have hc := copy_eval b 1 5 (by decide) (by decide) (by decide) hb6
  have hcf (j : Fin 7) (hj : j ≠ 5) : c.stacks j = b.stacks j := by
    simp [c, copied, StackRoutines.copyStacks, hj]
  have hc4 : (c.stacks 4).length = CounterPrograms.value (d.stacks 0) := by
    rw [hcf 4 (by decide), hb4]; simp
  have hc5 : c.stacks 5 = d.stacks 1 := by
    simp [c, copied, StackRoutines.copyStacks, hb5, hb1]
  obtain ⟨tc, htc, e, he, her, he4, he5, hef⟩ := compare_eval c
  simp only [hc4, hc5] at htc her he4 he5
  have he1 : e.stacks 1 = d.stacks 1 := (hef 1 (by decide) (by decide)).trans
    ((hcf 1 (by decide)).trans hb1)
  have he2 : e.stacks 2 = [] := (hef 2 (by decide) (by decide)).trans
    ((hcf 2 (by decide)).trans hb2)
  have he6 : e.stacks 6 = [] := (hef 6 (by decide) (by decide)).trans
    ((hcf 6 (by decide)).trans hb6)
  obtain ⟨ts, hts, f, hs, hf2, hff⟩ := choose_eval e he2 he6
  rw [he1] at hts
  have hf4 : (f.stacks 4).length ≤ CounterPrograms.value (d.stacks 0) := by
    rw [hff 4 (by decide)]; exact he4
  have hf5 : (f.stacks 5).length ≤ (d.stacks 1).length := by
    rw [hff 5 (by decide)]; exact he5
  let g := cleared f 4
  let z := cleared g 5
  have hg := clear_eval f 4
  have hz := clear_eval g 5
  have hg5 : g.stacks 5 = f.stacks 5 := by simp [g, cleared]
  refine ⟨(7 * (d.stacks 0).length + 5) + (tu +
    ((7 * (b.stacks 1).length + 5) + (tc + (ts +
      ((2 * (f.stacks 4).length + 3) + (2 * (g.stacks 5).length + 3)))))),
    ?_, z, ha.seq (hu.seq (hc.seq (he.seq (hs.seq (hg.seq hz))))), ?_, ?_⟩
  · rw [hb1, hg5]
    have hm := Nat.min_le_right (CounterPrograms.value (d.stacks 0)) (d.stacks 1).length
    unfold budget
    omega
  · have hout : f.stacks 2 = output d := by
      rw [hf2, her, he1]
      unfold output
      by_cases h : (d.stacks 1).length < CounterPrograms.value (d.stacks 0)
      · simp [h, Nat.not_le.mpr h]
      · have hn : CounterPrograms.value (d.stacks 0) ≤ (d.stacks 1).length := by omega
        simp [h, hn]
    simpa [z, g, cleared] using hout
  · intro j hj2
    by_cases hj4 : j = 4
    · subst j; simp [z, g, cleared, hd 4 (by decide)]
    by_cases hj5 : j = 5
    · subst j; simp [z, cleared, hd 5 (by decide)]
    have hzf : z.stacks j = f.stacks j := by simp [z, g, cleared, hj4, hj5]
    rw [hzf, hff j hj2, hef j hj4 hj5, hcf j hj5]
    by_cases hj3 : j = 3
    · subst j; rw [hb3, hd 3 (by decide)]
    · exact (hbf j hj3 hj4).trans (haf j hj3)

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramGateNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_lifted {R S : ℕ} (register : Fin 4 → Fin R) (stack : Fin 7 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (hd : ∀ j : Fin 7, 2 ≤ j.val → d.stacks (stack j) = []) :
    ∃ t ≤ budget (projectState register stack d) + 1, ∃ e : State R S,
      Eval (liftCommand command 0 2 register stack) t d e ∧
      e.stacks (stack 2) = output (projectState register stack d) ∧
      (∀ j, j ≠ stack 2 → e.stacks j = d.stacks j) ∧
      (∀ j, (¬ ∃ i, register i = j) → e.regs j = d.regs j) := by
  obtain ⟨t, ht, b, he, ho, hf⟩ := command_eval (projectState register stack d) hd
  refine ⟨t+1, Nat.add_le_add_right ht 1, embedState register stack d b,
    eval_liftCommand_from_state command 0 2 register stack d hr hs he, ?_, ?_, ?_⟩
  · simpa only [embedState_stack register stack d b hs 2] using ho
  · intro j hj
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i]
      exact hf i (fun h => hj (congrArg stack h))
    · exact embedState_stack_frame register stack d b j hm
  · exact fun j hj => embedState_register_frame register stack d b j hj

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native head-stage gate and paid extraction of its prior-word prefix. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def SetupReady (d : Data) : Prop :=
  ∀ j : Fin 48,j ∈ ({1,2,3,4,5,6,7,13,18} : Finset (Fin 48)) → d.stacks j=[]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramZip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual pairing and weighting of two candidate-ordered unary score streams.
This is one fixed finite program; no precomputed pair list is an input premise. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Zip
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 8 14

def base (regs : Fin 8 → Bool) (wi wh : List Bool) : Data :=
  ⟨regs, fun j => if j=12 then wi else if j=13 then wh else []⟩

end SubexponentialSAT.SqrtLog.PackingProgram.Zip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_OneHotAlphabetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Runtime one-hot alphabet generation

The unary input length r is data. Each loop iteration constructs one r-bit
one-hot word using the checked repeated-copy program and prepends its frame.
The final order is the decreasing order of the hot bit's position.
-/

namespace SubexponentialSAT.Subexp.OneHotAlphabetProgram

open BitProgram StructuredCalls TupleProgram

abbrev Data := State 5 7

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

end OAI.Algorithms
end


