-- Prove2me | Definitions.Def_OAIQ081S149
-- name    : OAIQ081S149
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:56:31.20949+00:00
-- url     : https://prove2.me/theorems/8202494e-eb5f-47d3-8b27-fd4b0831d6b6
-- title:
--   Definitions bundle OAIQ081S149 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 53 declarations of OpenAI's Lean: 13 definitions, 2 inductive types or structures and 38 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram.context`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.liftBase`, `OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram.zeroedThird`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.callbackCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.loopCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.outputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.traceBound`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderBounds.BoundedInputs`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.InputFor`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.prepared`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.preparedBytes`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.scoreBytes`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.scored`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderRawInput.context`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputLoose`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgram`, `SubexponentialSAT_SqrtLog_PackingPrefixProgram`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup`, `SubexponentialSAT_Subexp_CandidateScoreBounds`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_OneHotAlphabetProgram`, `SubexponentialSAT_Subexp_PairPreparationBounds`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ScoreBuilderBounds`, `SubexponentialSAT_Subexp_ScoreBuilderProgram`, `SubexponentialSAT_Subexp_ScoreBuilderRawInput`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S130`, `OAIQ081S131`, `OAIQ081S132`, `OAIQ081S133` and `OAIQ081S134` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S162`, `OAIQ081S163` and `OAIQ081S164`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S130
import Definitions.Def_OAIQ081S131
import Definitions.Def_OAIQ081S132
import Definitions.Def_OAIQ081S133
import Definitions.Def_OAIQ081S134

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

/-- The actual generator is lifted into the aggregate scorer. Only the
separate parser/depth-template ports lie outside its footprint. -/
theorem generate_eval (ctx : Context) (hc : ctx.Valid) (pair : PlanPair)
    (hp : ValidPair ctx pair) (tail stream : List Bool) :
    ∃ n ≤ generateCost ctx pair, Eval generate n
      (pairPrepared ctx tail stream pair) (pairFinished ctx tail stream pair) := by
  obtain ⟨n, hn, ht⟩ := CollisionGenerateProgram.program_run_uniform
    ctx.current ctx.width pair.1 pair.2 ctx.alphabet ctx.depth stream hc.1 hc.2 hp.1 hp.2
  let d := pairPrepared ctx tail stream pair
  have hin : embedState generatorRegs generatorPorts d
      (CollisionGenerateProgram.inputState ctx.current.flatten ctx.width pair.1 pair.2
        ctx.alphabet ctx.depth stream) = d := by
    apply embedState_eq _ _ generatorRegs_injective generatorPorts_injective
    · intro i; fin_cases i <;>
        simp [d, pairPrepared, RecordPrograms.state, ports, baseState, generatorRegs,
          CollisionGenerateProgram.inputState, CollisionGenerateProgram.storedState]
    · intro i; fin_cases i <;>
        simp [d, pairPrepared, RecordPrograms.state, ports, baseState, generatorPorts,
          CollisionGenerateProgram.inputState, CollisionGenerateProgram.storedState]
    · intros; rfl
    · intros; rfl
  have hout : embedState generatorRegs generatorPorts d
      (CollisionGenerateProgram.outputState ctx.current.flatten ctx.width pair.1 pair.2
        (ProgramEncoding.encodeRecords ctx.alphabet) (pairStream ctx pair stream)) =
      pairFinished ctx tail stream pair := by
    apply embedState_eq _ _ generatorRegs_injective generatorPorts_injective
    · intro i; fin_cases i <;>
        simp [pairFinished, RecordPrograms.state, ports, baseState, generatorRegs,
          CollisionGenerateProgram.outputState, CollisionGenerateProgram.storedState]
    · intro i; fin_cases i <;>
        simp [pairFinished, RecordPrograms.state, ports, baseState, generatorPorts,
          CollisionGenerateProgram.outputState, CollisionGenerateProgram.storedState]
    · intro j hj
      have h6 : j ≠ 6 := fun h => hj ⟨6, by simpa [generatorRegs] using h.symm⟩
      simp [pairFinished, d, pairPrepared, h6, RecordPrograms.state, ports, baseState]
    · intro j hj
      have h11 : j ≠ 11 := fun h => hj ⟨11, by simpa [generatorPorts] using h.symm⟩
      have h17 : j ≠ 17 := fun h => hj ⟨17, by simpa [generatorPorts] using h.symm⟩
      simp [pairFinished, d, pairPrepared, RecordPrograms.state, ports, baseState,
        Function.update_apply, h11, h17]
  have he := eval_call_lifted CollisionGenerateProgram.program generatorRegs generatorPorts d
    generatorRegs_injective generatorPorts_injective ht
  dsimp only [pairStream] at hout
  exact ⟨n, hn, by simpa only [hin, hout, generate] using he⟩

theorem callback_eval (ctx : Context) (hc : ctx.Valid) (pair : PlanPair)
    (hp : ValidPair ctx pair) (tail stream : List Bool) :
    ∃ n ≤ callbackCost ctx (pairBytes pair), Eval callback n
      (RecordPrograms.state ports (baseState ctx stream)
        false true false tail (pairBytes pair).reverse)
      (RecordPrograms.state ports (baseState ctx (pairStream ctx pair stream))
        false true false tail []) := by
  obtain ⟨n, hn, he⟩ := generate_eval ctx hc pair hp tail stream
  refine ⟨prepareCost ctx pair + (n + cleanupCost pair), ?_,
    (prepare_eval ctx pair tail stream).seq (he.seq (cleanup_eval ctx pair tail stream))⟩
  simpa only [callbackCost, readPair_pairBytes, Nat.add_assoc] using
    Nat.add_le_add_left (Nat.add_le_add_right hn (cleanupCost pair)) (prepareCost ctx pair)

theorem callback_contract (ctx : Context) (hc : ctx.Valid) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost ctx) (invariant ctx) (effect ctx) (validPayload ctx) := by
  rintro bits tail base ⟨pair, rfl, hp⟩ ⟨stream, rfl⟩
  obtain ⟨n, hn, he⟩ := callback_eval ctx hc pair hp tail stream
  refine ⟨n, baseState ctx (pairStream ctx pair stream), hn, ⟨_, rfl⟩, ?_, he⟩
  simp [effect, baseState]

theorem loop_eval (ctx : Context) (hc : ctx.Valid) (pairs : List PlanPair)
    (hp : ∀ pair ∈ pairs, ValidPair ctx pair) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost ctx) (pairs.map pairBytes),
      Eval loop n (inputState ctx pairs) (baseState ctx (streamedPairs ctx pairs [])) := by
  have hv : ∀ bits ∈ pairs.map pairBytes, validPayload ctx bits := by
    intro bits hbits
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hbits
    exact ⟨pair, rfl, hp pair hpair⟩
  obtain ⟨n, next, hn, hnext, history, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost ctx) (invariant ctx) (effect ctx)
    (validPayload ctx) (callback_contract ctx hc) (pairs.map pairBytes) []
    (baseState ctx []) hv ⟨[], rfl⟩ false false false
  obtain ⟨stream, rfl⟩ := hnext
  have hout : stream = streamedPairs ctx pairs [] := by
    have h := history.fold_of_false (by simp) (fun d => d.stacks 11)
      (fun acc bits => pairStream ctx (readPair bits) acc) (fun _ _ _ h => h)
    simpa only [baseState, Fin.reduceEq, ite_false, ite_true, if_true, records_fold] using h
  subst stream
  have hf : RecordPrograms.state ports (baseState ctx (streamedPairs ctx pairs []))
      false true false [] [] = baseState ctx (streamedPairs ctx pairs []) := by
    apply RecordPrograms.state_eq_self <;> simp [ports, baseState]
  refine ⟨n, hn, ?_⟩
  simpa only [any_false, unread_false, hf, ProgramEncoding.encodeRecords,
    inputState, pairRecords, List.append_nil, loop] using he

/-- One fixed record iterator executes every pair's real generator/collision
program, then tallies its complete concatenated stream. -/
theorem program_run (ctx : Context) (pairs : List PlanPair) (hc : ctx.Valid)
    (hp : ∀ pair ∈ pairs, ValidPair ctx pair) :
    RunsIn program (sourceBudget ctx pairs)
      ((inputState ctx pairs).withPC (some program.entry))
      ((outputState ctx pairs).withPC none) := by
  obtain ⟨n, hn, he⟩ := loop_eval ctx hc pairs hp
  let d := baseState ctx (streamedPairs ctx pairs [])
  have ht := tally_eval d
  have hlen : (d.stacks 11).length = pairs.length * ctx.alphabet.length ^ ctx.depth.length := by
    simp [d, baseState, streamedPairs_length]
  have hcost := UnaryTally.steps_le (d.stacks 11)
  rw [hlen] at hcost
  refine ⟨n + UnaryTally.steps (d.stacks 11) + 1, ?_, ?_⟩
  · dsimp [sourceBudget]
    omega
  · exact compiled_halt_trace (he.seq ht) 20 18

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

theorem embed_writerData (a : State 16 36) (v pr tag : Bool) (input output : List Bool) :
    embedState writerRegisters writerStacks a (writerData v pr tag input output) =
      ⟨Function.update (Function.update (Function.update a.regs 0 v) 1 pr) 2 tag,
        Function.update (Function.update a.stacks 18 input) 35 output⟩ := by
  apply embed_eq _ _ _ _ _ writerRegisters_injective writerStacks_injective
  · intro i; fin_cases i <;> simp [writerData,writerRegisters]
  · intro i; fin_cases i <;> simp [writerData,writerStacks,ParserProgram.pair]
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [writerRegisters] using h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1,by simpa [writerRegisters] using h.symm⟩
    have h2 : i ≠ 2 := fun h => hi ⟨2,by simpa [writerRegisters] using h.symm⟩
    simp [h0,h1,h2]
  · intro i hi
    have h18 : i ≠ 18 := fun h => hi ⟨0,by simpa [writerStacks] using h.symm⟩
    have h35 : i ≠ 35 := fun h => hi ⟨1,by simpa [writerStacks] using h.symm⟩
    simp [h18,h35]

theorem reverseWriter_eval (a : State 16 36) :
    Eval reverseWriter (4 * (a.stacks 18).length + 4) a (reverseWritten a) := by
  have h := eval_call_lifted reverseEscapeProgram writerRegisters writerStacks a
    writerRegisters_injective writerStacks_injective
    (a := writerData (a.regs 0) (a.regs 1) (a.regs 2) (a.stacks 18) (a.stacks 35))
    (b := writerData false false true [] ((TupleProgram.escaped (a.stacks 18)).reverse ++ a.stacks 35))
    (reverseEscape_trace (a.stacks 18) (a.stacks 35) (a.regs 0) (a.regs 1) (a.regs 2))
  simpa [embed_writerData,reverseWriter,reverseWritten] using h

theorem emitScore_eval (a : State 16 36) :
    Eval emitScore (4 * (a.stacks 18).length + 8) a (emittedScore a) := by
  have h := (TupleProgram.pushConst_eval 35 0 true a).seq
    ((reverseWriter_eval (TupleProgram.pushedState 35 0 true a)).seq
      (TupleProgram.pushConst_eval 35 0 false
        (reverseWritten (TupleProgram.pushedState 35 0 true a))))
  convert h using 1 <;> simp [emittedScore,TupleProgram.pushedState] ; omega

theorem finish_eval (ctx : Context) (candidate tail builder : List Bool) :
    Eval (.seq emitScore cleanup)
      (4 * candidateScore ctx candidate + 8 + (2 * (updated ctx candidate).length + 3) +
        (2 * candidate.length + 3))
      (workState ctx scoredRegs tail candidate (updated ctx candidate)
        (UnaryCompare.encode (candidateScore ctx candidate)) [] builder)
      (workState ctx finishedRegs tail [] [] [] []
        (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder)) := by
  let a := workState ctx scoredRegs tail candidate (updated ctx candidate)
    (UnaryCompare.encode (candidateScore ctx candidate)) [] builder
  let b := emittedScore a
  let c : State 16 36 := ⟨readRegs b.regs 0 1 none,StackRoutines.clearStacks 13 b.stacks⟩
  let d : State 16 36 := ⟨readRegs c.regs 0 1 none,StackRoutines.clearStacks 27 c.stacks⟩
  have h1 := emitScore_eval a
  have h2 := TupleProgram.clear_eval 13 0 1 b
  have h3 := TupleProgram.clear_eval 27 0 1 c
  have hend : d = workState ctx finishedRegs tail [] [] [] []
      (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [c,b,a,emittedScore,reverseWritten,TupleProgram.pushedState,
        workState,readRegs,scoredRegs,finishedRegs]
    · funext i
      fin_cases i <;> simp [c,b,a,emittedScore,reverseWritten,TupleProgram.pushedState,
        workState,StackRoutines.clearStacks,reverseRecord,TupleProgram.frame_eq_escaped,
        List.reverse_append,List.append_assoc]
  have h := h1.seq (h2.seq h3)
  change Eval (.seq emitScore cleanup) _ a d at h
  rw [hend] at h
  convert h using 1 ;
    simp [a,b,c,emittedScore,reverseWritten,TupleProgram.pushedState,workState,
      StackRoutines.clearStacks,UnaryCompare.encode,Nat.add_assoc]

theorem copyCandidates_eval (ctx : Context) (regs : Fin 16 → Bool) :
    Eval copyCandidates (7 * (ProgramEncoding.encodeRecords ctx.candidates).length + 5)
      (inputState ctx regs)
      (RecordPrograms.state outerPorts (baseState ctx (readRegs regs 0 1 none) [])
        (regs 13) (regs 14) (regs 15) (ProgramEncoding.encodeRecords ctx.candidates) []) := by
  have h := TupleProgram.copy_eval 30 29 33 0 1 (by decide) (by decide)
    (by decide) (by decide) (inputState ctx regs) (by simp [inputState,baseState,workState])
  convert h using 1
  · simp [inputState, baseState, workState]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [inputState,baseState,workState,outerPorts,readRegs]
    · funext i; fin_cases i <;> simp [inputState,baseState,workState,outerPorts,StackRoutines.copyStacks]

theorem finish_run (ctx : Context) (regs : Fin 16 → Bool) :
    ∃ r, Eval finish (3 * (ProgramEncoding.encodeRecords (scoreRecords ctx)).length + 5)
      (baseState ctx regs (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse)
      (outputState ctx r) := by
  let a := baseState ctx regs (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse
  let b := TupleProgram.pushedState 35 0 false a
  let r := readRegs b.regs 0 1 none
  have h1 := TupleProgram.pushConst_eval 35 0 false a
  have h2 := TupleProgram.transfer_eval 35 32 0 1 (by decide) (by decide) b
  have hbytes : (b.stacks 35).reverse = ProgramEncoding.encodeRecords (scoreRecords ctx) := by
    simpa [b,a,TupleProgram.pushedState,baseState,workState] using reverseRecord_finish (scoreRecords ctx)
  have hlen : (b.stacks 35).length = (ProgramEncoding.encodeRecords (scoreRecords ctx)).length := by
    simpa using congrArg List.length hbytes
  have hflat : TupleProgram.appendEncoded (scoreRecords ctx) [] ++ [false] =
      ProgramEncoding.encodeRecords (scoreRecords ctx) := by
    simpa using reverseRecord_finish (scoreRecords ctx)
  have hend : (⟨readRegs b.regs 0 1 none,StackRoutines.transferStacks 35 32 b.stacks⟩ : State 16 36) =
      outputState ctx r := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [StackRoutines.transferStacks,hflat,b,a,baseState,workState]
  rw [hend] at h2
  refine ⟨r,?_⟩
  convert h1.seq h2 using 1 ; simp [hlen] ; omega

end SubexponentialSAT.Subexp.CandidateScoreProgram

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

def zeroedThird (d : Data) : Data := ⟨Function.update d.regs 2 false, d.stacks⟩

def inputState (regs : Fin 5 → Bool) (n : ℕ) : Data :=
  ⟨regs, ![unary n, [], [], [], [], [], []]⟩

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def liftBase (code : Cmd 16 768) : OuterCode :=
  liftCommand code 0 0 id basePort

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # Polynomial overhead of the actual candidate-scoring loop -/

namespace SubexponentialSAT.Subexp.CandidateScoreBounds

open BitProgram CandidateScoreProgram

theorem updated_length (ctx : Context) (candidate : List Bool)
    (h : candidate.length = ctx.old.length) :
    (updated ctx candidate).length = (original ctx).length := by
  simp only [updated, original, List.length_append, h]

theorem pairContext_flatten_length (ctx : Context) (candidate : List Bool)
    (h : candidate.length = ctx.old.length) :
    (pairContext ctx candidate).current.flatten.length = (original ctx).length := by
  simpa only [pairContext, updated, List.flatten_append, List.flatten_cons] using
    updated_length ctx candidate h

end SubexponentialSAT.Subexp.CandidateScoreBounds

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

def outputState (ctx : Context) : Data :=
  ⟨fun _ => false, Function.update (inputState ctx (fun _ => false)).stacks 29
    (PairScoreProgram.pairRecords (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs))⟩

def callbackCost (ctx : Context) (pair : PlanPair) : ℕ :=
  let l := pair.1.map SelectionTableProgram.unary
  let r := pair.2.map SelectionTableProgram.unary
  let rem := remaining ctx.seedCount ctx.processedBits.length pair
  let unionBytes := ProgramEncoding.encodeRecords (l.reverse ++ r)
  let remBytes := ProgramEncoding.encodeRecords (rem.map SelectionTableProgram.unary)
  let table := SelectorProgram.selectionEntries ctx.seedCount rem
  [PairPlanPreparation.parseCost l r,
   17 * (ProgramEncoding.encodeRecords l).length +
     7 * (ProgramEncoding.encodeRecords r).length + 10,
   7 * (seedBytes ctx.seedCount).length + 5,
   ActivePlanProgram.traceBoundThreshold (List.range ctx.seedCount)
     (pair.1.reverse ++ pair.2) (true :: ctx.processedBits),
   2 * unionBytes.length + 3,
   9 * remBytes.length + 8,
   7 * ctx.seedCount + 5,
   3,
   SelectionTableProgram.traceCost ctx.seedCount rem,
   2 * (ctx.seedCount + rem.length) + 3,
   10 * (ProgramEncoding.encodeRecords l).length +
     10 * (ProgramEncoding.encodeRecords r).length + 9,
   SelectorPairProgram.cost table (l.reverse) (r.reverse),
   2 * (SelectionTableProgram.tableBytes ctx.seedCount rem).length + 3,
   13].sum

def loopCost (ctx : Context) : List PlanPair → ℕ
  | [] => 1
  | pair :: rest => 6 * (PairScoreProgram.pairBytes pair).length +
      callbackCost ctx pair + 7 + loopCost ctx rest

/-- This bound sums the costs of the actual called instruction tables and
record scans. It is not an assumed bound on an abstract preparation function. -/
def traceBound (ctx : Context) : ℕ :=
  let selected := selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs
  7 * (PairScoreProgram.pairRecords ctx.pairs).length + 5 +
  (7 * ctx.processedBits.length + 5) + 2 + 2 + 16 +
  (2 + loopCost ctx ctx.pairs) + (2 * (ctx.processedBits.length + 1) + 3) + 2 +
  10 * (PairScoreProgram.pairRecords selected.reverse).length +
  (9 * (PairScoreProgram.pairRecords selected).length + 8) + 16 + 1

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

theorem remaining_length_le (M processed : ℕ) (pair : PlanPair) :
    (remaining M processed pair).length ≤ M := by
  simpa [remaining, ActivePlanProgram.active] using
    List.length_filter_le (fun n => decide (processed + 1 ≤ n ∧ n ∈ pair.1.reverse ++ pair.2))
      (List.range M)

theorem remaining_member_lt (M processed : ℕ) (pair : PlanPair) (n : ℕ)
    (hn : n ∈ remaining M processed pair) : n < M := by
  have h := (ActivePlanProgram.mem_active (List.range M) (pair.1.reverse ++ pair.2)
    (processed + 1) n).mp hn
  exact List.mem_range.mp h.1

theorem remaining_sum_le (M processed : ℕ) (pair : PlanPair) :
    (remaining M processed pair).sum ≤ M * M := by
  exact (sum_le_length_mul _ M (fun n hn =>
    Nat.le_of_lt (remaining_member_lt M processed pair n hn))).trans
      (Nat.mul_le_mul_right M (remaining_length_le M processed pair))

theorem remainingBytes_length_le (M processed : ℕ) (pair : PlanPair) :
    (CollisionStreamProgram.planBytes (remaining M processed pair)).length ≤ 3 * (M + 1)^2 := by
  have h := planBytes_le (remaining M processed pair) M
    (fun n hn => Nat.le_of_lt (remaining_member_lt M processed pair n hn))
  have hl := remaining_length_le M processed pair
  calc
    _ ≤ 1 + (2 * M + 2) * M := h.trans (by gcongr)
    _ ≤ _ := by nlinarith

theorem tableBytes_length_le (M processed : ℕ) (pair : PlanPair) :
    (SelectionTableProgram.tableBytes M (remaining M processed pair)).length ≤ 2 * (M + 1)^3 := by
  have h := SelectionTableProgram.tableBytes_length_le M (remaining M processed pair)
  have hl := remaining_length_le M processed pair
  have hs := remaining_sum_le M processed pair
  calc
    _ ≤ M * (2 * (M * M) + 2 * (M + M) + 2) := h.trans (by gcongr)
    _ ≤ _ := by ring_nf; omega

theorem tableCost_le (M processed : ℕ) (pair : PlanPair) :
    SelectionTableProgram.traceCost M (remaining M processed pair) ≤ 128 * (M + 1)^4 := by
  have h := SelectionTableProgram.traceCost_quadratic M (remaining M processed pair)
  have hl := remaining_length_le M processed pair
  have hs := remaining_sum_le M processed pair
  calc
    _ ≤ 128 * (M + M * M + M + 1)^2 := h.trans (by gcongr)
    _ = _ := by ring

theorem selectorCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hb : (PairScoreProgram.pairBytes pair).length ≤ B) :
    SelectorPairProgram.cost
      (SelectorProgram.selectionEntries ctx.seedCount (remaining ctx.seedCount ctx.processedBits.length pair))
      (pair.1.map SelectionTableProgram.unary).reverse
      (pair.2.map SelectionTableProgram.unary).reverse ≤ 6600 * (B + 1)^4 := by
  have hl := (pair_plan_lengths pair).1.trans hb
  have hr := (pair_plan_lengths pair).2.trans hb
  have ht : (SelectionTableProgram.tableBytes ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair)).length ≤ 2 * (B + 1)^3 :=
    (tableBytes_length_le _ _ _).trans (by gcongr)
  have h := SelectorPairProgram.cost_bound
    (SelectorProgram.selectionEntries ctx.seedCount (remaining ctx.seedCount ctx.processedBits.length pair))
    (pair.1.map SelectionTableProgram.unary).reverse
    (pair.2.map SelectionTableProgram.unary).reverse
  rw [← SelectionTableProgram.tableBytes_eq_rawRecords] at h
  simp only [ProgramEncoding.encodeRecords, ActivePlanProgram.encoded_reverse_length] at h
  change _ ≤ 1100 * (_ + 1) * ((CollisionStreamProgram.planBytes pair.1).length +
    (CollisionStreamProgram.planBytes pair.2).length + 1) at h
  calc
    _ ≤ 1100 * (2 * (B + 1)^3 + 1) * (B + B + 1) := h.trans (by gcongr)
    _ ≤ _ := by ring_nf; omega

theorem callbackCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hb : (PairScoreProgram.pairBytes pair).length ≤ B) :
    callbackCost ctx pair ≤ 20000 * (B + 1)^4 := by
  have hl := (pair_plan_lengths pair).1.trans hb
  have hr := (pair_plan_lengths pair).2.trans hb
  have hu : (CollisionStreamProgram.planBytes (pair.1.reverse ++ pair.2)).length ≤ 2 * B := by
    have h := unionBytes_le pair; omega
  have hseed : (seedBytes ctx.seedCount).length ≤ 3 * (B + 1)^2 :=
    (seedBytes_length_le _).trans (by gcongr)
  have hrem : (CollisionStreamProgram.planBytes
      (remaining ctx.seedCount ctx.processedBits.length pair)).length ≤ 3 * (B + 1)^2 :=
    (remainingBytes_length_le _ _ _).trans (by gcongr)
  have hremLen := (remaining_length_le ctx.seedCount ctx.processedBits.length pair).trans hm
  have htable : (SelectionTableProgram.tableBytes ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair)).length ≤ 2 * (B + 1)^3 :=
    (tableBytes_length_le _ _ _).trans (by gcongr)
  have htableCost : SelectionTableProgram.traceCost ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair) ≤ 128 * (B + 1)^4 :=
    (tableCost_le _ _ _).trans (by gcongr)
  have ha := activeCost_le ctx pair B hm hp hb
  have hs := selectorCost_le ctx pair B hm hb
  have hparse : PairPlanPreparation.parseCost
      (pair.1.map SelectionTableProgram.unary) (pair.2.map SelectionTableProgram.unary) ≤
      21 * B + 17 := by
    change 3 * (PairScoreProgram.pairBytes pair).length + 9 *
      ((CollisionStreamProgram.planBytes pair.1).length +
        (CollisionStreamProgram.planBytes pair.2).length) + 17 ≤ _
    omega
  have hcoarse : callbackCost ctx pair ≤
      (21 * B + 17) + (24 * B + 10) + (21 * (B + 1)^2 + 5) + 4096 * (B + 1)^4 +
      (4 * B + 3) + (27 * (B + 1)^2 + 8) + (7 * B + 5) + 3 + 128 * (B + 1)^4 +
      (4 * B + 3) + (20 * B + 9) + 6600 * (B + 1)^4 + (4 * (B + 1)^3 + 3) + 13 := by
    unfold callbackCost
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
    have hmap : (pair.1.map SelectionTableProgram.unary).reverse ++
        pair.2.map SelectionTableProgram.unary =
        (pair.1.reverse ++ pair.2).map SelectionTableProgram.unary := by simp
    rw [hmap]
    change _ ≤ _ at hrem
    change (ProgramEncoding.encodeRecords
      ((pair.1.reverse ++ pair.2).map SelectionTableProgram.unary)).length ≤ _ at hu
    change (ProgramEncoding.encodeRecords (pair.1.map SelectionTableProgram.unary)).length ≤ _ at hl
    change (ProgramEncoding.encodeRecords (pair.2.map SelectionTableProgram.unary)).length ≤ _ at hr
    change (ProgramEncoding.encodeRecords
      ((remaining ctx.seedCount ctx.processedBits.length pair).map SelectionTableProgram.unary)).length ≤ _ at hrem
    omega
  exact hcoarse.trans (by ring_nf; omega)

theorem loopCost_le (ctx : Context) (pairs : List PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hb : ∀ pair ∈ pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    loopCost ctx pairs ≤ 1 + pairs.length * (20000 * (B + 1)^4 + 6 * B + 7) := by
  induction pairs with
  | nil => simp [loopCost]
  | cons pair pairs ih =>
    have hpair := hb pair (by simp)
    have hc := callbackCost_le ctx pair B hm hp hpair
    have ht := ih (fun q hq => hb q (by simp [hq]))
    simp only [loopCost, List.length_cons]
    nlinarith

theorem selectedPair_length_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hb : (PairScoreProgram.pairBytes pair).length ≤ B) :
    (PairScoreProgram.pairBytes (selectedPair ctx.seedCount ctx.processedBits.length pair)).length ≤
      30 * (B + 1)^2 := by
  have hl := (pair_plan_lengths pair).1.trans hb
  have hr := (pair_plan_lengths pair).2.trans hb
  have hleft := plan_sizes_le pair.1
  have hright := plan_sizes_le pair.2
  have hrem := (remaining_length_le ctx.seedCount ctx.processedBits.length pair).trans hm
  have hselect : ∀ n, n ≤ B → ReadPlan.selectPosition ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair) n ≤ 2 * B := by
    intro n hn
    unfold ReadPlan.selectPosition
    split
    · have hi : (remaining ctx.seedCount ctx.processedBits.length pair).idxOf n ≤
          (remaining ctx.seedCount ctx.processedBits.length pair).length := List.idxOf_le_length
      omega
    · omega
  have hplan : ∀ plan : List ℕ, plan.sum ≤ B → plan.length ≤ B →
      (CollisionStreamProgram.planBytes (plan.map (ReadPlan.selectPosition ctx.seedCount
        (remaining ctx.seedCount ctx.processedBits.length pair)))).length ≤ 7 * (B + 1)^2 := by
    intro plan hsum hlen
    have h := planBytes_le (plan.map (ReadPlan.selectPosition ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair))) (2 * B) (by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
        exact hselect k ((member_le_sum hk).trans hsum))
    simp only [List.length_map] at h
    calc
      _ ≤ 1 + (2 * (2 * B) + 2) * B := h.trans (by gcongr)
      _ ≤ _ := by nlinarith
  have hsleft := hplan pair.1 (hleft.1.trans hl) (hleft.2.trans hl)
  have hsright := hplan pair.2 (hright.1.trans hr) (hright.2.trans hr)
  simp only [PairScoreProgram.pairBytes, selectedPair, List.length_append, Encoding.length_frame]
  nlinarith

theorem selectedPairs_bytes_length_le (ctx : Context) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hn : ctx.pairs.length ≤ B)
    (hb : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    (PairScoreProgram.pairRecords
      (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs)).length ≤ 63 * (B + 1)^3 := by
  have h := encoded_pairRecords_le (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs)
    (30 * (B + 1)^2) (by
      intro pair hpair
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hpair
      exact selectedPair_length_le ctx p B hm (hb p hp'))
  simp only [selectedPairs, List.length_map] at h
  calc
    _ ≤ 1 + (2 * (30 * (B + 1)^2) + 2) * B := h.trans (by gcongr)
    _ ≤ _ := by ring_nf; omega

theorem traceBound_le (ctx : Context) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hn : ctx.pairs.length ≤ B)
    (hb : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    traceBound ctx ≤ 30000 * (B + 1)^5 := by
  have hraw : (PairScoreProgram.pairRecords ctx.pairs).length ≤ 3 * (B + 1)^2 := by
    have h := encoded_pairRecords_le ctx.pairs B hb
    calc
      _ ≤ 1 + (2 * B + 2) * B := h.trans (by gcongr)
      _ ≤ _ := by nlinarith
  have hsel := selectedPairs_bytes_length_le ctx B hm hn hb
  have hrev : (PairScoreProgram.pairRecords
      (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs).reverse).length =
      (PairScoreProgram.pairRecords
        (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs)).length := by
    simp only [PairScoreProgram.pairRecords, List.map_reverse, ProgramEncoding.encodeRecords,
      ActivePlanProgram.encoded_reverse_length]
  have hloop : loopCost ctx ctx.pairs ≤ 21000 * (B + 1)^5 := by
    have h := loopCost_le ctx ctx.pairs B hm hp hb
    calc
      _ ≤ 1 + B * (20000 * (B + 1)^4 + 6 * B + 7) := h.trans (by gcongr)
      _ ≤ _ := by ring_nf; omega
  dsimp only [traceBound]
  rw [hrev]
  calc
    _ ≤ 7 * (3 * (B + 1)^2) + 5 + (7 * B + 5) + 2 + 2 + 16 +
        (2 + 21000 * (B + 1)^5) + (2 * (B + 1) + 3) + 2 +
        10 * (63 * (B + 1)^3) + (9 * (63 * (B + 1)^3) + 8) + 16 + 1 := by omega
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

def preparedBytes (pre : PairPreparationProgram.Context) : List Bool :=
  PairScoreProgram.pairRecords (PairPreparationProgram.selectedPairs
    pre.seedCount pre.processedBits.length pre.pairs)

def scoreBytes (ctx : CandidateScoreProgram.Context) : List Bool :=
  ProgramEncoding.encodeRecords (CandidateScoreProgram.scoreRecords ctx)

def prepared (pre : PairPreparationProgram.Context) (d : Data) : Data :=
  ⟨fun _ => false, Function.update d.stacks 40 (preparedBytes pre)⟩

def scored (pre : PairPreparationProgram.Context) (ctx : CandidateScoreProgram.Context)
    (d : Data) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, Function.update (prepared pre d).stacks 41 (scoreBytes ctx)⟩

/-- Exact encoded inputs for the two fixed subroutines. These are equalities
of runtime stack contents; no execution or mathematical score is assumed. -/
structure InputFor (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (d : Data) : Prop where
  preparation : ∀ i,
    (PairPreparationProgram.inputState pre d.regs).stacks i = d.stacks (preparationPorts i)
  candidates : ∀ i,
    (CandidateScoreProgram.inputState ctx (fun _ => false)).stacks i =
      (prepared pre d).stacks (candidatePorts i)

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A uniform bound for the actual complete score builder

The preparation program computes the selected plans. Its proved output-size
bound supplies the pair-payload bound needed by the candidate program.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderBounds

open BitProgram ScoreBuilderProgram

/-- Bounds on literal input lengths and counts, before selected plans are
computed. The prepared-payload bound is derived inside the theorem. -/
structure BoundedInputs (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (B : ℕ) : Prop where
  seedCount : pre.seedCount ≤ B
  processed : pre.processedBits.length ≤ B
  pairCount : pre.pairs.length ≤ B
  pairPayload : ∀ pair ∈ pre.pairs, (PairScoreProgram.pairBytes pair).length ≤ B
  original : (CandidateScoreProgram.original ctx).length ≤ B
  before : ctx.before.length ≤ B
  width : ctx.width.length ≤ B
  depth : ctx.depth.length ≤ B
  candidates : ctx.candidates.length ≤ B

end SubexponentialSAT.Subexp.ScoreBuilderBounds

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

def context {r Q : ℕ} (Δ : ℕ) (alphabet : List (Word r Q))
    (default : Word r Q) (fixed : List (Word r Q)) (n seedCount : ℕ)
    (rawPlans : List PairScoreProgram.PlanPair) (d : ScoreBuilderProgram.Data) :
    CandidateScoreProgram.Context :=
  CandidateScoreRefinement.candidateContext (Δ := Δ) alphabet default fixed n
    (d.stacks 10) (d.stacks 19)
    (PairPreparationProgram.selectedPairs seedCount (d.stacks 19).length rawPlans)

theorem preparation_input_of_memory {r Q : ℕ} (Δ : ℕ) (default : Word r Q)
    (tail fixed : List (Word r Q)) (n seedCount : ℕ)
    (rawPlans : List PairScoreProgram.PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (environment Δ (default :: tail) seedCount rawPlans)
      d.stacks) :
    ∀ i, (PairPreparationProgram.inputState (preparationContext seedCount rawPlans d) d.regs).stacks i =
      d.stacks (ScoreBuilderProgram.preparationPorts i) := by
  dsimp only [SequentialProgram.HighState] at hh
  intro i
  by_cases hi : 20 ≤ (ScoreBuilderProgram.preparationPorts i).val
  · rw [hh _ hi]
    fin_cases i <;> first
    | exact absurd hi (by decide)
    | simp [PairPreparationProgram.inputState, preparationContext,
        ScoreBuilderProgram.preparationPorts, environment, ScoreBuilderProgram.environment]
  · fin_cases i <;> first
    | exact absurd hi (by decide)
    | (simp [PairPreparationProgram.inputState, preparationContext,
        ScoreBuilderProgram.preparationPorts] <;>
        (apply hm.scratch ; decide))

theorem candidate_input_of_memory {r Q : ℕ} (Δ : ℕ) (default : Word r Q)
    (tail fixed : List (Word r Q)) (n seedCount : ℕ)
    (rawPlans : List PairScoreProgram.PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (environment Δ (default :: tail) seedCount rawPlans)
      d.stacks) :
    ∀ i, (CandidateScoreProgram.inputState (context Δ (default :: tail) default fixed n seedCount rawPlans d) (fun _ => false)).stacks i =
      (ScoreBuilderProgram.prepared (preparationContext seedCount rawPlans d) d).stacks
        (ScoreBuilderProgram.candidatePorts i) := by
  dsimp only [SequentialProgram.HighState] at hh
  intro i
  simp only [ScoreBuilderProgram.prepared]
  by_cases h40 : ScoreBuilderProgram.candidatePorts i = 40
  · rw [h40, Function.update_self]
    fin_cases i <;> first
    | exact absurd h40 (by decide)
    | simp [CandidateScoreProgram.inputState, CandidateScoreProgram.baseState,
        CandidateScoreProgram.workState, ScoreBuilderProgram.preparedBytes,
        context, preparationContext, CandidateScoreRefinement.candidateContext]
  · rw [Function.update_of_ne h40]
    by_cases hi : 20 ≤ (ScoreBuilderProgram.candidatePorts i).val
    · rw [hh _ hi]
      fin_cases i <;> first
      | exact absurd h40 (by decide)
      | exact absurd hi (by decide)
      | simp [CandidateScoreProgram.inputState, CandidateScoreProgram.baseState,
          CandidateScoreProgram.workState, ScoreBuilderProgram.candidatePorts,
          context, CandidateScoreRefinement.candidateContext,
          environment, ScoreBuilderProgram.environment]
    · fin_cases i <;> first
      | exact absurd h40 (by decide)
      | exact absurd hi (by decide)
      | (simp [CandidateScoreProgram.inputState, CandidateScoreProgram.baseState,
          CandidateScoreProgram.workState, CandidateScoreProgram.original,
          ScoreBuilderProgram.candidatePorts, context,
          CandidateScoreRefinement.candidateContext, hm.assignment, List.flatten_append,
          List.replicate_succ, List.map_replicate] <;>
          (apply hm.scratch ; decide))

/-- The two subroutine input conditions follow from the actual memory and high-stack invariants. -/
theorem inputFor_of_memory {r Q : ℕ} (Δ : ℕ) (default : Word r Q)
    (tail fixed : List (Word r Q)) (n seedCount : ℕ)
    (rawPlans : List PairScoreProgram.PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord default tail (n + 1) fixed d.stacks)
    (hh : SequentialProgram.HighState (environment Δ (default :: tail) seedCount rawPlans)
      d.stacks) :
    ScoreBuilderProgram.InputFor (preparationContext seedCount rawPlans d)
      (context Δ (default :: tail) default fixed n seedCount rawPlans d) d := by
  exact ⟨preparation_input_of_memory Δ default tail fixed n seedCount rawPlans d hm hh,
    candidate_input_of_memory Δ default tail fixed n seedCount rawPlans d hm hh⟩

end SubexponentialSAT.Subexp.ScoreBuilderRawInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete incidence collision scoring from raw two-word read plans.
The fixed legacy program constructs its selection tables and all four-word
completion tuples at runtime. No precomputed collision table is an input. -/

namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

theorem remaining_length_le (M processed : ℕ) (pair : PlanPair)
    (hp : ValidRawPair M pair) :
    (PairPreparationProgram.remaining M processed pair).length ≤ 4 := by
  have hn := ActivePlanProgram.active_nodup (List.range M)
    (pair.1.reverse ++ pair.2) (processed + 1) List.nodup_range
  change (PairPreparationProgram.remaining M processed pair).Nodup at hn
  have hs : PairPreparationProgram.remaining M processed pair ⊆ pair.1.reverse ++ pair.2 := by
    intro i hi
    exact ((ActivePlanProgram.mem_active _ _ _ _).mp hi).2.2
  have hsub : (PairPreparationProgram.remaining M processed pair).toFinset ⊆
      (pair.1.reverse ++ pair.2).toFinset := by
    intro i hi
    exact List.mem_toFinset.mpr (hs (List.mem_toFinset.mp hi))
  have hlen := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  rw [List.toFinset_card_of_nodup hn] at hlen
  simp only [List.length_append, List.length_reverse] at hlen
  have hleft := hp.left_length
  have hright := hp.right_length
  exact hlen.trans (by omega)

theorem selected_valid (M processed : ℕ) (pair : PlanPair)
    (hp : ValidRawPair M pair) :
    (∀ i ∈ (PairPreparationProgram.selectedPair M processed pair).1, i < M + 4) ∧
    (∀ i ∈ (PairPreparationProgram.selectedPair M processed pair).2, i < M + 4) := by
  have hlen := remaining_length_le M processed pair hp
  exact ⟨ReadPlan.completionPlan_valid M 4 _ _ hlen hp.left_valid,
    ReadPlan.completionPlan_valid M 4 _ _ hlen hp.right_valid⟩

def context {r Q : ℕ} (alphabet : List (Word r Q)) (default : Word r Q)
    (fixed : List (Word r Q)) (n M : ℕ) (raw : List PlanPair)
    (d : ScoreBuilderProgram.Data) : CandidateScoreProgram.Context :=
  ScoreBuilderRawInput.context 1 alphabet default fixed n M raw d

theorem context_valid {r Q : ℕ} (alphabet : List (Word r Q)) (default : Word r Q)
    (fixed : List (Word r Q)) (n M : ℕ) (raw : List PlanPair)
    (d : ScoreBuilderProgram.Data)
    (hsize : n + 1 + fixed.length = M)
    (hw : (d.stacks 10).length = ReadPlan.wordWidth r Q)
    (hi : (d.stacks 19).length = fixed.length)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    (context alphabet default fixed n M raw d).Valid := by
  constructor
  · simpa [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext] using hi
  · intro row hrow
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow
    simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · intro row hrow
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow
    simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · intro row hrow
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow
    simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · intro row hrow
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp hrow
    simp [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      ReadPlan.encodeWord_length, hw]
  · intro pair hpair
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hpair
    have hv := selected_valid M (d.stacks 19).length original (hp original horiginal)
    simpa [context, ScoreBuilderRawInput.context, CandidateScoreRefinement.candidateContext,
      CandidateScoreProgram.pairContext, PairScoreProgram.ValidPair, ← hsize,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv

theorem boundedInputs {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (n + 1) fixed d.stacks)
    (hsize : n + 1 + fixed.length = M)
    (hp : ∀ pair ∈ raw, ValidRawPair M pair) :
    ScoreBuilderBounds.BoundedInputs
      (ScoreBuilderRawInput.preparationContext M raw d)
      (context (a :: tail) a fixed n M raw d)
      (inputBound M raw.length (a :: tail).length (ReadPlan.wordWidth r Q)) := by
  let s := M + raw.length + (a :: tail).length + ReadPlan.wordWidth r Q + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hM : M + 1 ≤ s := by dsimp [s]; omega
  have hpairs : raw.length ≤ s := by dsimp [s]; omega
  have hq : (a :: tail).length ≤ s := by dsimp [s]; omega
  have hw : ReadPlan.wordWidth r Q ≤ s := by dsimp [s]; omega
  have hs2 : s ≤ s^2 := le_self_pow₀ hs (by omega)
  have hfixed : fixed.length ≤ M := by omega
  have hwidth : (d.stacks 10).length = ReadPlan.wordWidth r Q := by
    simpa only [ReadPlan.encodeWord_length] using hm.width
  have hmw : M * ReadPlan.wordWidth r Q ≤ s^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show M ≤ s by omega) hw
  change ScoreBuilderBounds.BoundedInputs _ _ (32*s^2)
  constructor
  · change M ≤ _
    nlinarith only [hM, hs2]
  · change (d.stacks 19).length ≤ _
    rw [hm.processed]
    nlinarith only [hfixed, hM, hs2]
  · change raw.length ≤ _
    nlinarith only [hpairs, hs2]
  · intro pair hpair
    have hb := pairBytes_length_le M pair (hp pair hpair)
    nlinarith only [hb, hM, hs2, hs]
  · change ((fixed.reverse.map ReadPlan.encodeWord).flatten ++
      (ReadPlan.encodeWord a ++ ((List.replicate n a).map ReadPlan.encodeWord).flatten)).length ≤ _
    rw [List.length_append, List.length_append, ScoreBuilderInputBounds.encodedWords_length,
      ScoreBuilderInputBounds.encodedWords_length, List.length_reverse, List.length_replicate,
      ReadPlan.encodeWord_length]
    have heq : fixed.length * ReadPlan.wordWidth r Q +
        (ReadPlan.wordWidth r Q + n * ReadPlan.wordWidth r Q) =
        M * ReadPlan.wordWidth r Q := by rw [← hsize]; ring
    rw [heq]
    nlinarith only [hmw]
  · change (fixed.reverse.map ReadPlan.encodeWord).length ≤ _
    simp only [List.length_map, List.length_reverse]
    nlinarith only [hfixed, hM, hs2]
  · change (d.stacks 10).length ≤ _
    rw [hwidth]
    nlinarith only [hw, hs2]
  · change (List.replicate (2 * (1 + 1)) true).length ≤ _
    rw [List.length_replicate]
    nlinarith only [hs, hs2]
  · change ((a :: tail).map ReadPlan.encodeWord).length ≤ _
    rw [List.length_map]
    nlinarith only [hq, hs2]

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

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

theorem cleaned_context {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data) :
    context (a::tail) a fixed n M raw (cleaned a tail d) =
      context (a::tail) a fixed n M raw d := by
  simp [context, ScoreBuilderRawInput.context, cleaned, SequentialProgram.scratchPorts]

theorem cleaned_preparation {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data) :
    ScoreBuilderRawInput.preparationContext M raw (cleaned a tail d) =
      ScoreBuilderRawInput.preparationContext M raw d := by
  simp [ScoreBuilderRawInput.preparationContext, cleaned, SequentialProgram.scratchPorts]

theorem inputFor_of_loose {r Q : ℕ} (a : Word r Q) (tail fixed : List (Word r Q))
    (n M : ℕ) (raw : List PlanPair) (d : ScoreBuilderProgram.Data)
    (hm : LooseMemory a fixed n d)
    (hh : SequentialProgram.HighState (ScoreBuilderRawInput.environment 1 (a::tail) M raw)
      d.stacks) :
    ScoreBuilderProgram.InputFor (ScoreBuilderRawInput.preparationContext M raw d)
      (context (a::tail) a fixed n M raw d) d := by
  have hi := ScoreBuilderRawInput.inputFor_of_memory 1 a tail fixed n M raw
    (cleaned a tail d) (cleaned_memory a tail fixed n d hm) (cleaned_high a tail d _ hh)
  change ScoreBuilderProgram.InputFor _ (context (a::tail) a fixed n M raw (cleaned a tail d)) _ at hi
  rw [cleaned_context, cleaned_preparation] at hi
  have h0 := hm.scratch 0 (by decide)
  have h1 := hm.scratch 1 (by decide)
  have h2 := hm.scratch 2 (by decide)
  have h3 := hm.scratch 3 (by decide)
  have h4 := hm.scratch 4 (by decide)
  have h5 := hm.scratch 5 (by decide)
  have h6 := hm.scratch 6 (by decide)
  have h7 := hm.scratch 7 (by decide)
  constructor
  · intro i
    have h := hi.preparation i
    fin_cases i <;>
      simpa [cleaned, SequentialProgram.scratchPorts, ScoreBuilderProgram.preparationPorts,
        h0,h1,h2,h3,h4,h5,h6,h7] using h
  · intro i
    have h := hi.candidates i
    fin_cases i <;>
      simpa [ScoreBuilderProgram.prepared, cleaned, SequentialProgram.scratchPorts,
        ScoreBuilderProgram.candidatePorts,h0,h1,h2,h3,h4,h5,h6,h7] using h

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

theorem normalize_eval (out : Fin 11) (ho : out ≠ 5) (a : Data) :
    Eval (normalize out) (4 * (a.stacks 5).length + 4) a (afterNormalize out a) := by
  have hi : Function.Injective (normStack out) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [normStack]
  let b := PackingHeadProgramPrepareCount.state (fun _ => false) []
    (unary (a.stacks 5).length ++ a.stacks out)
  have ht := PackingHeadProgramPrepareCount.trace a.regs (a.stacks 5) (a.stacks out)
  have hs : PackingHeadProgramPrepareCount.state a.regs (a.stacks 5) (a.stacks out) =
      projectState id (normStack out) a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [hs] at ht
  have he := eval_call_from_state PackingHeadProgramPrepareCount.program id (normStack out) a
    Function.injective_id hi ht
  have hb : embedState id (normStack out) a b = afterNormalize out a := by
    apply embedState_eq_of_ports id (normStack out) a _ _ Function.injective_id hi
    · intro i; rfl
    · intro i h; exact False.elim (h ⟨i,rfl⟩)
    · intro i; fin_cases i <;>
        simp [b, PackingHeadProgramPrepareCount.state, afterNormalize, normStack, Ne.symm ho]
    · intro i h
      have h5 : i ≠ 5 := fun hi => h ⟨0, by simpa [normStack] using hi.symm⟩
      have hout : i ≠ out := fun hi => h ⟨1, by simpa [normStack] using hi.symm⟩
      simp [afterNormalize, h5, hout]
  exact hb ▸ he

theorem readPrefix_eval (a : Data) (size : ℕ)
    (hw : a.stacks 6 = unary size) (hlen : size ≤ (a.stacks 0).length)
    (h5 : a.stacks 5 = []) (h7 : a.stacks 7 = []) (h8 : a.stacks 8 = [])
    (h9 : a.stacks 9 = []) (h10 : a.stacks 10 = []) :
    Eval readPrefix (15 * size + 16) a
      ⟨readRegs a.regs 0 1 none,
        Function.update a.stacks 3 ((a.stacks 0).take size ++ a.stacks 3)⟩ := by
  let d := projectState id readStack a
  let record := (a.stacks 0).take size
  let rest := (a.stacks 0).drop size
  have hrecord : record.length = (unary size).length := by
    simp [record, List.length_take, Nat.min_eq_left hlen]
  have he := ArrayUpdatePrograms.readProgram_trace (0 : Fin 3) 1 (by decide)
    [] record rest (unary size) [] d.regs d.stacks
    (by simp [d, projectState, readStack, record, rest]) hw h8 (by rfl) (by simp)
    hrecord h5 h7 h9 h10
  have hl := eval_call_from_state (ArrayUpdatePrograms.readProgram (0 : Fin 3) 1) id readStack a
    Function.injective_id readStack_injective
    (b := ⟨readRegs d.regs 0 1 none, ArrayUpdatePrograms.readStacks record d.stacks⟩) he
  let result : Data := ⟨readRegs a.regs 0 1 none,
    Function.update a.stacks 3 (record ++ a.stacks 3)⟩
  have hb : embedState id readStack a
      ⟨readRegs d.regs 0 1 none, ArrayUpdatePrograms.readStacks record d.stacks⟩ = result := by
    apply embedState_eq_of_ports id readStack a _ _ Function.injective_id readStack_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i
      fin_cases i <;> simp [result, d, projectState, readStack, ArrayUpdatePrograms.readStacks,
        Function.comp_def, h8]
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨1, by simpa [readStack] using h.symm⟩
      simp [result, h3]
  simpa only [List.length_nil, zero_mul, zero_add, List.length_replicate, hb] using hl

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native head-stage gate and paid extraction of its prior-word prefix. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem gate_eval (d : Data) (h : SetupReady d) :
    ∃ t ≤ PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d)+1,
      ∃ e : Data, Eval gate t d e ∧
      e.stacks 18=(if (d.stacks 19).length < SubexponentialSAT.CounterPrograms.value (d.stacks 20)
        then d.stacks 19 else []) ∧
      (∀ j,j≠18→e.stacks j=d.stacks j) := by
  obtain ⟨t,ht,e,he,ho,hf,_⟩ := PackingWeightProgram.Gate.command_lifted
    gateRegisters gatePorts gateRegisters_injective gatePorts_injective d (by
      intro i hi
      fin_cases i <;> try (norm_num at hi)
      all_goals simpa [gatePorts] using h _ (by simp))
  exact ⟨t,ht,e,he,ho,hf⟩

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end


