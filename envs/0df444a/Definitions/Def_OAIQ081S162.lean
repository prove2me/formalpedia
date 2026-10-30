-- Prove2me | Definitions.Def_OAIQ081S162
-- name    : OAIQ081S162
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:04:46.628423+00:00
-- url     : https://prove2.me/theorems/448dba71-e8b8-47c9-8cc4-1d98b62b13c4
-- title:
--   Definitions bundle OAIQ081S162 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 9 definitions and 23 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.queryLow`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.initialized`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.popped`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.prepareProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.Overlay.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.Overlay.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.sourceBudget`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_FactorTableProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableProgram.lean), [`SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryAdapter.lean), [`SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingHeadProgramCandidates.lean), [`SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesLift`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingHeadProgramCandidatesLift.lean), [`SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingHeadProgramCandidatesRun.lean), [`SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingIncidenceInputNative.lean), [`SubexponentialSAT_SqrtLog_ProducedQueryRankSchedule`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/ProducedQueryRankSchedule.lean), [`SubexponentialSAT_Subexp_BasisTransposePlanProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/BasisTransposePlanProgram.lean), [`SubexponentialSAT_Subexp_CandidateScoreBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/CandidateScoreBounds.lean), [`SubexponentialSAT_Subexp_CandidateScoreProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/CandidateScoreProgram.lean), [`SubexponentialSAT_Subexp_ScoreBuilderBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/ScoreBuilderBounds.lean), [`SubexponentialSAT_Subexp_ScoreBuilderProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/Subexp/ScoreBuilderProgram.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S142`, `OAIQ081S143`, `OAIQ081S144`, `OAIQ081S147`, `OAIQ081S148`, `OAIQ081S149` and `OAIQ081S151` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S169`, `OAIQ081S170`, `OAIQ081S171` and `OAIQ081S172`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.command_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace.prepare_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.prepared_head_update`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeOverlay.command_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S142
import Definitions.Def_OAIQ081S143
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S147
import Definitions.Def_OAIQ081S148
import Definitions.Def_OAIQ081S149
import Definitions.Def_OAIQ081S151

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

theorem runPairs_eval (ctx : Context) (hc : ctx.Valid) (candidate : List Bool)
    (hw : candidate.length = ctx.width.length) (tail builder : List Bool) :
    ∃ n ≤ PairScoreProgram.sourceBudget (pairContext ctx candidate) ctx.pairs,
      Eval runPairs n
        (workState ctx pairStartRegs tail candidate (updated ctx candidate) []
          (PairScoreProgram.pairRecords ctx.pairs) builder)
        (workState ctx scoredRegs tail candidate (updated ctx candidate)
          (UnaryCompare.encode (candidateScore ctx candidate)) [] builder) := by
  let a := workState ctx pairStartRegs tail candidate (updated ctx candidate) []
    (PairScoreProgram.pairRecords ctx.pairs) builder
  let b := workState ctx scoredRegs tail candidate (updated ctx candidate)
    (UnaryCompare.encode (candidateScore ctx candidate)) [] builder
  have hin : embedState lowRegisters lowStacks a (PairScoreProgram.inputState (pairContext ctx candidate) ctx.pairs) = a := by
    apply embed_eq _ _ _ _ _ lowRegisters_injective lowStacks_injective
    · intro i
      rw [PairScoreProgram.inputState_regs]
      fin_cases i <;> simp [a,workState,pairStartRegs,lowRegisters,Fin.castAdd]
    · intro i
      rw [PairScoreProgram.inputState_stacks]
      fin_cases i <;> simp [a,workState,pairContext,updated,lowStacks,Fin.castAdd,
        List.flatten_append,List.flatten_cons]
    · intros; rfl
    · intros; rfl
  have hout : embedState lowRegisters lowStacks a (PairScoreProgram.outputState (pairContext ctx candidate) ctx.pairs) = b := by
    apply embed_eq _ _ _ _ _ lowRegisters_injective lowStacks_injective
    · intro i
      rw [PairScoreProgram.outputState_regs]
      fin_cases i <;> simp [b,workState,scoredRegs,lowRegisters,Fin.castAdd]
    · intro i
      rw [PairScoreProgram.outputState_stacks]
      fin_cases i <;> simp [b,workState,pairContext,updated,candidateScore,lowStacks,Fin.castAdd,
        List.flatten_append,List.flatten_cons]
    · intro i hi
      have h11 : i ≠ 11 := fun h => hi ⟨11,by simpa [lowRegisters] using h.symm⟩
      simp [a,b,workState,pairStartRegs,scoredRegs,h11]
    · intro i hi
      have h18 : i ≠ 18 := fun h => hi ⟨18,by simpa [lowStacks] using h.symm⟩
      have h20 : i ≠ 20 := fun h => hi ⟨20,by simpa [lowStacks] using h.symm⟩
      simp [a,b,workState,h18,h20]
  obtain ⟨n,hn,ht⟩ := PairScoreProgram.program_run (pairContext ctx candidate) ctx.pairs
    (pairContext_valid ctx hc candidate hw) (pairContext_pairs ctx hc candidate)
  have he := eval_call_lifted PairScoreProgram.program lowRegisters lowStacks a
    lowRegisters_injective lowStacks_injective ht
  exact ⟨n,hn,by simpa only [hin,hout,runPairs,a,b] using he⟩

theorem callback_eval (ctx : Context) (hc : ctx.Valid) (candidate : List Bool)
    (hw : candidate.length = ctx.width.length) (regs : Fin 16 → Bool) (tail builder : List Bool) :
    ∃ n ≤ callbackCost ctx candidate,
      Eval callback n
        (RecordPrograms.state outerPorts (baseState ctx regs builder)
          false true false tail candidate.reverse)
        (RecordPrograms.state outerPorts
          (baseState ctx finishedRegs (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder))
          false true false tail []) := by
  let r0 := (RecordPrograms.state outerPorts (baseState ctx regs builder)
    false true false tail candidate.reverse).regs
  let r1 := readRegs r0 0 1 none
  let r2 := readRegs r1 0 1 none
  let r3 := readRegs r2 0 1 none
  have h1 := transferCandidate_eval ctx regs tail builder candidate
  have h2 := updateCandidate_eval ctx hc r1 tail builder candidate hw
  have h3 := copyPairs_eval ctx r2 tail builder candidate (updated ctx candidate)
  have h4 := resetLow_work ctx r3 tail builder candidate (updated ctx candidate)
    (by simp [r3,r2,r1,r0,readRegs,RecordPrograms.state,outerPorts])
    (by simp [r3,r2,r1,r0,readRegs,RecordPrograms.state,outerPorts])
    (by simp [r3,r2,r1,r0,readRegs,RecordPrograms.state,outerPorts])
  obtain ⟨n,hn,h5⟩ := runPairs_eval ctx hc candidate hw tail builder
  have h6 := finish_eval ctx candidate tail builder
  have hend : workState ctx finishedRegs tail [] [] [] []
      (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder) =
      RecordPrograms.state outerPorts
        (baseState ctx finishedRegs (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder))
        false true false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [workState,baseState,outerPorts,finishedRegs]
    · funext i; fin_cases i <;> simp [workState,baseState,outerPorts]
  rw [hend] at h6
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  refine ⟨_,?_,h⟩
  dsimp [callbackCost]
  omega

theorem callback_contract (ctx : Context) (hc : ctx.Valid) :
    RecordPrograms.CallbackContractWithOn outerPorts callback (fun _ => false)
      (callbackCost ctx) (invariant ctx) (effect ctx)
      (fun candidate => candidate.length = ctx.width.length) := by
  rintro candidate tail base hw ⟨regs,builder,rfl⟩
  obtain ⟨n,hn,he⟩ := callback_eval ctx hc candidate hw regs tail builder
  refine ⟨n,baseState ctx finishedRegs
    (reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) builder),hn,
    ⟨_,_,rfl⟩,?_,he⟩
  simp [effect,baseState,workState]

theorem iterateCandidates_eval (ctx : Context) (hc : ctx.Valid) (regs : Fin 16 → Bool) :
    ∃ n r, n ≤ 3 + RecordPrograms.budget (callbackCost ctx) ctx.candidates ∧
      Eval iterateCandidates n
        (RecordPrograms.state outerPorts (baseState ctx (readRegs regs 0 1 none) [])
          (regs 13) (regs 14) (regs 15) (ProgramEncoding.encodeRecords ctx.candidates) [])
        (baseState ctx r (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse) := by
  obtain ⟨n,next,hn,hnext,history,he⟩ := RecordPrograms.iterate_run_with_on
    outerPorts callback (fun _ => false) (callbackCost ctx) (invariant ctx) (effect ctx)
    (fun candidate => candidate.length = ctx.width.length) (callback_contract ctx hc)
    ctx.candidates [] (baseState ctx (readRegs regs 0 1 none) []) hc.candidate_width
    ⟨_,_,rfl⟩ (regs 13) (regs 14) (regs 15)
  obtain ⟨r,builder,rfl⟩ := hnext
  have hbuilder : builder = (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse := by
    have h := history.fold_of_false (by simp) (fun d => d.stacks 35)
      (fun acc candidate => reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) acc)
      (fun _ _ _ h => h)
    have hfold : ctx.candidates.foldl
        (fun acc candidate => reverseRecord (UnaryCompare.encode (candidateScore ctx candidate)) acc) [] =
        (scoreRecords ctx).foldl (fun acc bits => reverseRecord bits acc) [] := by
      simp [scoreRecords,List.foldl_map]
    simpa [baseState,workState,hfold,reverseRecord_fold] using h
  subst builder
  let r' := (RecordPrograms.state outerPorts (baseState ctx r []) false true false [] []).regs
  have hend : RecordPrograms.state outerPorts
      (baseState ctx r (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse)
      false true false [] [] =
      baseState ctx r' (TupleProgram.appendEncoded (scoreRecords ctx) []).reverse := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i; fin_cases i <;> simp [baseState,workState,outerPorts]
  have hany : ctx.candidates.any (fun _ => false) = false := by
    induction ctx.candidates <;> simp_all
  refine ⟨n,r',hn,?_⟩
  simpa only [hany,TupleProgram.unread_false,hend,ProgramEncoding.encodeRecords,
    List.append_nil,iterateCandidates] using he

theorem program_run (ctx : Context) (hc : ctx.Valid) (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn program (sourceBudget ctx)
      ((inputState ctx regs).withPC (some program.entry)) ((outputState ctx finalRegs).withPC none) := by
  have hcopy := copyCandidates_eval ctx regs
  obtain ⟨n,r,hn,hi⟩ := iterateCandidates_eval ctx hc regs
  obtain ⟨finalRegs,hf⟩ := finish_run ctx r
  refine ⟨finalRegs,_,?_,StructuredCalls.compiled_halt_trace (hcopy.seq (hi.seq hf)) 30 32⟩
  dsimp [sourceBudget]
  omega

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BasisTransposePlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical transpose read-plan generation

Two unary countdowns visit columns and rows in decreasing order. Each visit
constructs the unary physical index by repeated copying and emits one actual
framed record. Prepending these visits produces the increasing transpose
read order directly. All counters are runtime stacks and the code is fixed.
-/

namespace SubexponentialSAT.Subexp.BasisTransposePlanProgram

open BitProgram StructuredCalls

theorem down_run (body : Code) (counter output : Fin 7) (hco : counter ≠ output)
    (step : ℕ → List Bool → List Bool) (cost : ℕ → ℕ) (base d : Data)
    (spec : DownSpec body counter output step cost base)
    (n : ℕ) (hf : LoopFrame base counter output d) (hc : d.stacks counter = unary n) :
    ∃ t e, Eval (UnaryForPrograms.forCmd (ports counter) body) t d e ∧
      t ≤ downBudget cost n ∧
      e.stacks = Function.update (Function.update d.stacks counter []) output
        (downOutput step n (d.stacks output)) := by
  obtain ⟨costs, t, e, hv, ht, hs⟩ := down_visits body counter output hco
    step cost base spec n d hf hc
  exact ⟨t, e, hv.eval, ht, hs⟩

theorem copy_eval (src dst : Fin 7) (d : Data) (hsd : src ≠ dst)
    (hs6 : src ≠ 6) (hd6 : dst ≠ 6) (h6 : d.stacks 6 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst 6 0 1 hsd hs6 hd6.symm
    (by decide) d.regs d.stacks h6)

theorem multiply_eval (N u : ℕ) (d : Data)
    (hN : d.stacks 0 = unary N) (hu : d.stacks 5 = unary u) (h6 : d.stacks 6 = []) :
    ∃ t e, Eval multiply t d e ∧ t ≤ u * (7 * N + 7) + 2 ∧
      e.stacks = Function.update (Function.update d.stacks 5 []) 4
        (unary (u * N) ++ d.stacks 4) := by
  have spec : DownSpec (copy 0 4) 5 4 (fun _ acc => unary N ++ acc)
      (fun _ => 7 * N + 5) d := by
    intro n a hf _
    have ha0 : a.stacks 0 = unary N := (hf 0 (by decide) (by decide)).trans hN
    have ha6 : a.stacks 6 = [] := (hf 6 (by decide) (by decide)).trans h6
    refine ⟨7 * (a.stacks 0).length + 5, copied 0 4 a, ?_,
      copy_eval 0 4 a (by decide) (by decide) (by decide) ha6, ?_⟩
    · simp [ha0, unary]
    ·
      rw [copied_stacks, ha0]
  obtain ⟨t, e, he, ht, hs⟩ := down_run (copy 0 4) 5 4 (by decide)
    (fun _ acc => unary N ++ acc) (fun _ => 7 * N + 5) d d spec u
    (fun _ _ _ => rfl) hu
  refine ⟨t, e, he, ?_, ?_⟩
  · have hb := downBudget_le (fun _ => 7 * N + 5) u (7 * N + 5) (by intros; exact le_rfl)
    simpa only [Nat.add_assoc] using ht.trans hb
  · simpa only [multiply_output] using hs

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

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

def initialized (a : OuterData) : OuterData := SubexpSetupStorage.clearManyState entryPorts a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

namespace HeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def popped (regs : Fin 4 → Bool) (mask bits rev out ones : List Bool) : Data :=
  state (readRegs regs 0 1 mask.head?) mask.tail bits rev out ones

end HeadSelect

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace Overlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def command : Code := .seq (copy 0 5) (.seq (copy 1 6)
  (.seq expand (.seq transfer (.seq merge clear))))
def program := compiled command 0 10

end Overlay

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def command : Code := .call (ProgramLinking.liftProgram Overlay.program regMap stackMap)



def prepare : Code := .seq reset command
def prepareProgram := compiled prepare 859 145

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed producer of all incremental head scores from the candidate alphabet
and actual flattened prior-head table. No selected pair records are inputs. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open Subexp

theorem callback_eval (rows : List (List Bool)) (acc tail candidate : List Bool)
    (hlen : ∀ row ∈ rows,row.length=candidate.length) :
    ∃ n ≤ callbackCost rows candidate,
      Eval callback n (boundary rows acc tail candidate.reverse)
        (boundary rows (CandidateScoreProgram.reverseRecord
          (List.replicate (PackingHeadProgramPrefix.score candidate rows) false) acc) tail []) := by
  have hr := reverse_eval rows acc tail candidate
  obtain ⟨n,hn,hs⟩ := score_eval rows acc tail candidate hlen
  obtain ⟨e,he,he4,he9,hef⟩ := PackingProgram.Streams.emit_eval (scored rows acc tail candidate)
  let f : Data := ⟨readRegs e.regs 0 1 none,Function.update e.stacks 0 []⟩
  have hc : Eval clear (2*(e.stacks 0).length+3) e f :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 0 0 1 e.regs e.stacks)
  have hf := reset_eval f
  have h0 : e.stacks 0=candidate := by
    simpa [scored,boundary,RecordPrograms.state,ports] using hef 0 (by decide) (by decide)
  have hend : resetState f = boundary rows (CandidateScoreProgram.reverseRecord
      (List.replicate (PackingHeadProgramPrefix.score candidate rows) false) acc) tail [] := by
    apply state_ext
    · funext i; fin_cases i <;> simp [resetState,boundary,RecordPrograms.state,ports,baseState]
    · funext i
      fin_cases i
      · rfl
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (1 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (1 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (1 : Fin 12) ≠ 8)] using
          hef 1 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (2 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (2 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (2 : Fin 12) ≠ 8)] using
          hef 2 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (3 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (3 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (3 : Fin 12) ≠ 8)] using
          hef 3 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored] using he4
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (5 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (5 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (5 : Fin 12) ≠ 8)] using
          hef 5 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (6 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (6 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (6 : Fin 12) ≠ 8)] using
          hef 6 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (7 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (7 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (7 : Fin 12) ≠ 8)] using
          hef 7 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (8 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (8 : Fin 12) ≠ 0), Function.update_same] using
          hef 8 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored] using he9
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (10 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (10 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (10 : Fin 12) ≠ 8)] using
          hef 10 (by decide) (by decide)
      · simpa [resetState, f, boundary, RecordPrograms.state, ports, baseState, scored,
          Function.update_noteq (by decide : (11 : Fin 12) ≠ 4),
          Function.update_noteq (by decide : (11 : Fin 12) ≠ 0),
          Function.update_noteq (by decide : (11 : Fin 12) ≠ 8)] using
          hef 11 (by decide) (by decide)
  rw [hend] at hf
  have hh := hr.seq (hs.seq (he.seq (hc.seq hf)))
  refine ⟨_,?_,hh⟩
  simp only [scored,boundary,RecordPrograms.state,ports,Function.update_same,List.length_replicate,h0]
  unfold callbackCost
  omega

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives Subexp

theorem callback_contract (rows : List (List Bool)) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost rows) (invariant rows) (effect rows) (validPayload rows) := by
  rintro bits tail base hv ⟨acc,rfl⟩
  obtain ⟨n,hn,he⟩ := callback_eval rows acc tail bits hv
  refine ⟨n,baseState rows (CandidateScoreProgram.reverseRecord (scoreBits rows bits) acc),hn,
    ⟨_,rfl⟩,?_,he⟩
  rfl

theorem loop_eval (rows candidates : List (List Bool))
    (hlen : ∀ candidate ∈ candidates,validPayload rows candidate) :
    ∃ n ≤ 3+RecordPrograms.budget (callbackCost rows) candidates,
      Eval loop n (inputState rows candidates)
        (baseState rows (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse) := by
  obtain ⟨n,next,hn,hnext,history,he⟩ := RecordPrograms.iterate_run_with_on ports callback
    (fun _ => false) (callbackCost rows) (invariant rows) (effect rows)
    (validPayload rows) (callback_contract rows) candidates [] (baseState rows [])
    hlen ⟨[],rfl⟩ false false false
  obtain ⟨acc,rfl⟩ := hnext
  have hout : acc=(TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse := by
    have h := history.fold_of_false (by simp) (fun d => d.stacks 9)
      (fun acc bits => CandidateScoreProgram.reverseRecord (scoreBits rows bits) acc)
      (fun _ _ _ h => h)
    have hm : candidates.foldl (fun acc bits =>
        CandidateScoreProgram.reverseRecord (scoreBits rows bits) acc) [] =
        (scoreRecords rows candidates).foldl (fun acc bits =>
          CandidateScoreProgram.reverseRecord bits acc) [] := by
      simp [scoreRecords,List.foldl_map]
    simpa [baseState,hm,CandidateScoreProgram.reverseRecord_fold] using h
  subst acc
  have hf : RecordPrograms.state ports (baseState rows
      (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse)
      false true false [] [] = baseState rows
      (TupleProgram.appendEncoded (scoreRecords rows candidates) []).reverse := by
    apply RecordPrograms.state_eq_self <;> simp [ports,baseState]
  refine ⟨n,hn,?_⟩
  simpa only [any_false,unread_false,hf,ProgramEncoding.encodeRecords,inputState,List.append_nil,loop] using he

theorem program_run (rows candidates : List (List Bool))
    (hlen : ∀ candidate ∈ candidates,validPayload rows candidate) :
    RunsIn program (budget rows candidates)
      ((inputState rows candidates).withPC (some program.entry))
      ((baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))).withPC none) := by
  obtain ⟨n,hn,hl⟩ := loop_eval rows candidates hlen
  refine ⟨_,?_,compiled_halt_trace (hl.seq (finish_eval rows candidates)) 8 9⟩
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Caller-state interface for the fixed all-candidate head score producer. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines SubexpScanPrimitives Subexp

theorem command_lifted {R S : ℕ} (reg : Fin 8 → Fin R) (stack : Fin 12 → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (d : State R S) (rows candidates : List (List Bool))
    (hr : ∀ i,d.regs (reg i)=false)
    (h1 : d.stacks (stack 1)=rows.flatten)
    (h5 : d.stacks (stack 5)=List.replicate rows.length true)
    (h8 : d.stacks (stack 8)=ProgramEncoding.encodeRecords candidates)
    (hc : ∀ i : Fin 12,i≠1 → i≠5 → i≠8 → d.stacks (stack i)=[])
    (hlen : ∀ candidate ∈ candidates,validPayload rows candidate) :
    ∃ n ≤ budget rows candidates, ∃ e : State R S,
      Eval (lifted reg stack) n d e ∧
      e.stacks = Function.update (Function.update d.stacks (stack 8) []) (stack 9)
        (ProgramEncoding.encodeRecords (scoreRecords rows candidates)) ∧
      (∀ i,e.regs (reg i)=decide (i=6)) ∧
      (∀ j,(¬∃ i,reg i=j) → e.regs j=d.regs j) := by
  let a := inputState rows candidates
  let b := baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))
  have ha : embedState reg stack d a=d := by
    apply embedState_eq_of_ports reg stack d d a hreg hstack
    · intro i; fin_cases i <;> simp [a,inputState,baseState,RecordPrograms.state,ports,hr]
    · intros; rfl
    · intro i
      fin_cases i <;> first
        | simpa [a,inputState,baseState,RecordPrograms.state,ports] using h1
        | simpa [a,inputState,baseState,RecordPrograms.state,ports] using h5
        | simpa [a,inputState,baseState,RecordPrograms.state,ports] using h8
        | simpa [a,inputState,baseState,RecordPrograms.state,ports] using hc _ (by decide) (by decide) (by decide)
    · intros; rfl
  let e := embedState reg stack d b
  obtain ⟨n,hn,ht⟩ := program_run rows candidates hlen
  have he := eval_call_lifted program reg stack d hreg hstack (a:=a) (b:=b) ht
  refine ⟨n,hn,e,?_,?_,?_,?_⟩
  · simpa only [ha,lifted] using he
  · change Function.extend stack b.stacks d.stacks = _
    have hf : Function.extend stack a.stacks d.stacks=d.stacks :=
      congrArg StructuredProgram.State.stacks ha
    change Function.extend stack
      (baseState rows (ProgramEncoding.encodeRecords (scoreRecords rows candidates))).stacks d.stacks = _
    rw [final_stacks,ProgramLinking.extend_update hstack,ProgramLinking.extend_update hstack]
    rw [hf]
  · intro i
    have h := embedState_register reg stack d b hreg i
    simpa [e,b,baseState] using h
  · intro j hj
    exact embedState_register_frame reg stack d b j hj

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
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

theorem scoreBytes_length_le (ctx : Context) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length) (hn : ctx.candidates.length ≤ B) (hp : ctx.pairs.length ≤ B) :
    (ProgramEncoding.encodeRecords (scoreRecords ctx)).length ≤
      5 * (B + 1) ^ 2 * ctx.alphabet.length ^ ctx.depth.length := by
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hk : 1 ≤ K := one_le_pow₀ hA
  have hw : ∀ row ∈ scoreRecords ctx, row.length ≤ B * K := by
    intro row hrow
    obtain ⟨candidate, _, rfl⟩ := List.mem_map.mp hrow
    simp only [UnaryCompare.encode, List.length_replicate]
    exact (candidateScore_le ctx candidate).trans (Nat.mul_le_mul_right _ hp)
  have h := PairRuntimeBounds.encoded_length_le (scoreRecords ctx) (B * K) hw
  rw [scoreRecords_length] at h
  calc
    _ ≤ 2 * B * (B * K) + 2 * B + 1 := h.trans (by gcongr)
    _ ≤ 5 * (B + 1) ^ 2 * K := by nlinarith [Nat.mul_le_mul_left (2 * B + 1) hk]

theorem callbackCost_le (ctx : Context) (hc : ctx.Valid) (candidate : List Bool)
    (hcan : candidate ∈ ctx.candidates) (B : ℕ) (hA : 1 ≤ ctx.alphabet.length)
    (ho : (original ctx).length ≤ B) (hb : ctx.before.length ≤ B)
    (hw : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B) (hn : ctx.pairs.length ≤ B)
    (hp : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    callbackCost ctx candidate ≤ 5200 * (B + 1) ^ 5 * ctx.alphabet.length ^ ctx.depth.length := by
  let s := B + 1
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have hcand := hc.candidate_width candidate hcan
  have heq : candidate.length = ctx.old.length := hcand.trans hc.old_width.symm
  have hu := updated_length ctx candidate heq
  have hflat := pairContext_flatten_length ctx candidate heq
  have hpair := PairRuntimeBounds.sourceBudget_le (pairContext ctx candidate) ctx.pairs B hA
    (fun row hrow => (hc.alphabet_width row hrow).le) (by simpa only [hflat] using ho) hw hd hn hp
  have hscores := candidateScore_le ctx candidate
  have hscore : candidateScore ctx candidate ≤ B * K := hscores.trans (Nat.mul_le_mul_right _ hn)
  have hbytes := PairRuntimeBounds.pairRecords_length_le ctx.pairs B hp
  have hbytes' : (PairScoreProgram.pairRecords ctx.pairs).length ≤ 3 * s ^ 2 := by
    calc
      _ ≤ 2 * B * B + 2 * B + 1 := hbytes.trans (by gcongr)
      _ ≤ 3 * s ^ 2 := by dsimp [s]; nlinarith
  have harray : CandidateArrayProgram.sourceCost (original ctx).length ctx.before.length ctx.width.length ≤
      100 * s ^ 2 := by
    unfold CandidateArrayProgram.sourceCost
    calc
      _ ≤ 7 * B + 7 * B + B * (14 * B + 10) + 20 * B + 32 := by gcongr
      _ ≤ 100 * s ^ 2 := by dsimp [s]; nlinarith
  have h15 : s ≤ s ^ 5 := le_self_pow₀ hs (by omega)
  have h25 : s ^ 2 ≤ s ^ 5 := pow_le_pow_right₀ hs (by omega)
  have hscale : s ^ 2 ≤ s ^ 5 * K := by simpa using Nat.mul_le_mul h25 hk
  have hscale1 : s ≤ s ^ 5 * K := by simpa using Nat.mul_le_mul h15 hk
  have hscore' : candidateScore ctx candidate ≤ s ^ 5 * K := by
    exact hscore.trans (Nat.mul_le_mul_right _ (by dsimp [s] at h15 ⊢; omega))
  change PairScoreProgram.sourceBudget (pairContext ctx candidate) ctx.pairs ≤ 5000 * s ^ 5 * K at hpair
  change callbackCost ctx candidate ≤ 5200 * s ^ 5 * K
  unfold callbackCost
  rw [hu]
  have hcB : candidate.length ≤ B := hcand.le.trans hw
  dsimp [s] at harray hbytes' hscale hscale1 hscore' hpair ⊢
  nlinarith only [harray, hpair, hscore', hbytes', hscale, hscale1, ho, hcB]

/-- The exponent six is fixed; it accounts for traversing candidates and
their encoded score records as well as executing every pair scorer. -/
theorem sourceBudget_le (ctx : Context) (hc : ctx.Valid) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length) (ho : (original ctx).length ≤ B)
    (hb : ctx.before.length ≤ B) (hw : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B)
    (hn : ctx.candidates.length ≤ B) (hpn : ctx.pairs.length ≤ B)
    (hp : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    sourceBudget ctx ≤ 6000 * (B + 1) ^ 6 * ctx.alphabet.length ^ ctx.depth.length := by
  let s := B + 1
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have h15 : s ≤ s ^ 5 := le_self_pow₀ hs (by omega)
  have hscale : s ≤ s ^ 5 * K := by simpa using Nat.mul_le_mul h15 hk
  have hbud := PairRuntimeBounds.budget_bounded (callbackCost ctx) ctx.candidates B (5200 * s ^ 5 * K)
    (fun row hrow => (hc.candidate_width row hrow).le.trans hw)
    (fun row hrow => callbackCost_le ctx hc row hrow B hA ho hb hw hd hpn hp)
  have hstep : 6 * B + 5200 * s ^ 5 * K + 7 ≤ 5213 * s ^ 5 * K := by
    dsimp [s] at hscale ⊢
    nlinarith
  have hbud' : RecordPrograms.budget (callbackCost ctx) ctx.candidates ≤ 5213 * s ^ 6 * K := by
    calc
      _ ≤ ctx.candidates.length * (5213 * s ^ 5 * K) := hbud.trans (Nat.mul_le_mul_left _ hstep)
      _ ≤ s * (5213 * s ^ 5 * K) := Nat.mul_le_mul_right _ (by dsimp [s]; omega)
      _ = _ := by ring
  have hinput := PairRuntimeBounds.encoded_length_le ctx.candidates B
    (fun row hrow => (hc.candidate_width row hrow).le.trans hw)
  have hinput' : (ProgramEncoding.encodeRecords ctx.candidates).length ≤ 3 * s ^ 2 := by
    calc
      _ ≤ 2 * B * B + 2 * B + 1 := hinput.trans (by gcongr)
      _ ≤ 3 * s ^ 2 := by dsimp [s]; nlinarith
  have hout := scoreBytes_length_le ctx B hA hn hpn
  have h26 : s ^ 2 ≤ s ^ 6 := pow_le_pow_right₀ hs (by omega)
  have hscale2 : s ^ 2 ≤ s ^ 6 * K := by simpa using Nat.mul_le_mul h26 hk
  have hout' : (ProgramEncoding.encodeRecords (scoreRecords ctx)).length ≤ 5 * s ^ 6 * K :=
    hout.trans (by gcongr)
  have hone : 1 ≤ s ^ 6 * K := Nat.mul_le_mul (one_le_pow₀ hs) hk
  change 7 * (ProgramEncoding.encodeRecords ctx.candidates).length +
    RecordPrograms.budget (callbackCost ctx) ctx.candidates +
    3 * (ProgramEncoding.encodeRecords (scoreRecords ctx)).length + 14 ≤ 6000 * s ^ 6 * K
  nlinarith only [hbud', hinput', hout', hscale2, hone]

end SubexponentialSAT.Subexp.CandidateScoreBounds

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

def sourceBudget (pre : PairPreparationProgram.Context) (ctx : CandidateScoreProgram.Context) : ℕ :=
  PairPreparationProgram.traceBound pre + CandidateScoreProgram.sourceBudget ctx +
    6 * (scoreBytes ctx).length + 2 * (preparedBytes pre).length + 10

theorem candidates_eval (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (d : Data)
    (hinput : ∀ i, (CandidateScoreProgram.inputState ctx (fun _ => false)).stacks i =
      (prepared pre d).stacks (candidatePorts i)) :
    ∃ n ≤ CandidateScoreProgram.sourceBudget ctx, ∃ regs,
      Eval candidates n (prepared pre d) (scored pre ctx d regs) := by
  obtain ⟨regs, n, hn, ht⟩ := CandidateScoreProgram.program_run ctx hc (fun _ => false)
  have hout : (CandidateScoreProgram.outputState ctx regs).stacks =
      Function.update (CandidateScoreProgram.inputState ctx (fun _ => false)).stacks 32
        (scoreBytes ctx) := by
    rfl
  have he := call_lifted_update CandidateScoreProgram.program candidatePorts candidatePorts_injective
    (prepared pre d) (CandidateScoreProgram.inputState ctx (fun _ => false))
    (CandidateScoreProgram.outputState ctx regs) 32 (scoreBytes ctx) rfl hinput hout ht
  exact ⟨n, hn, regs, by
    simpa [candidates, scored, candidatePorts,
      CandidateScoreProgram.outputState] using he⟩

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

theorem sourceBudget_le (pre : PairPreparationProgram.Context)
    (ctx : CandidateScoreProgram.Context) (hc : ctx.Valid) (B : ℕ)
    (h : BoundedInputs pre ctx B) (hA : 1 ≤ ctx.alphabet.length)
    (hlink : ctx.pairs = PairPreparationProgram.selectedPairs
      pre.seedCount pre.processedBits.length pre.pairs) :
    sourceBudget pre ctx ≤ runtimeBound B ctx.alphabet.length ctx.depth.length := by
  let s := B + 1
  let C := 30 * s ^ 2
  let K := ctx.alphabet.length ^ ctx.depth.length
  let T := s ^ 12 * K
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have hself : s ≤ s ^ 2 := le_self_pow₀ hs (by omega)
  have hBC : B ≤ C := by
    change B ≤ 30 * (B + 1) ^ 2
    nlinarith
  have hC : C + 1 ≤ 31 * s ^ 2 := by dsimp [C]; nlinarith
  have hpn : ctx.pairs.length ≤ B := by
    rw [hlink]
    simpa only [PairPreparationProgram.selectedPairs, List.length_map] using h.pairCount
  have hpb : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ C := by
    intro pair hpair
    rw [hlink] at hpair
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hpair
    exact PairPreparationBounds.selectedPair_length_le pre raw B h.seedCount (h.pairPayload raw hraw)
  have hcan := CandidateScoreBounds.sourceBudget_le ctx hc C hA
    (h.original.trans hBC) (h.before.trans hBC) (h.width.trans hBC) (h.depth.trans hBC)
    (h.candidates.trans hBC) (hpn.trans hBC) hpb
  have hcan' : CandidateScoreProgram.sourceBudget ctx ≤ (6000 * 31 ^ 6) * T := by
    calc
      _ ≤ 6000 * (31 * s ^ 2) ^ 6 * K := hcan.trans (by gcongr)
      _ = _ := by dsimp [T]; ring
  have hpre := PairPreparationBounds.traceBound_le pre B h.seedCount h.processed h.pairCount h.pairPayload
  have hselected := PairPreparationBounds.selectedPairs_bytes_length_le pre B
    h.seedCount h.pairCount h.pairPayload
  have hscores := CandidateScoreBounds.scoreBytes_length_le ctx B hA h.candidates hpn
  have h5 : s ^ 5 ≤ T := by
    simpa only [T, Nat.mul_one] using Nat.mul_le_mul
      (pow_le_pow_right₀ hs (show 5 ≤ 12 by omega)) hk
  have h3 : s ^ 3 ≤ T := by
    simpa only [T, Nat.mul_one] using Nat.mul_le_mul
      (pow_le_pow_right₀ hs (show 3 ≤ 12 by omega)) hk
  have h2 : s ^ 2 * K ≤ T := Nat.mul_le_mul_right _ (pow_le_pow_right₀ hs (by omega))
  have h1 : 1 ≤ T := Nat.mul_le_mul (one_le_pow₀ hs) hk
  have hp' : PairPreparationProgram.traceBound pre ≤ 30000 * T := hpre.trans (Nat.mul_le_mul_left _ h5)
  have hs' : (preparedBytes pre).length ≤ 63 * T := hselected.trans (Nat.mul_le_mul_left _ h3)
  have ho' : (scoreBytes ctx).length ≤ 5 * T := hscores.trans (by
    change 5 * s ^ 2 * K ≤ 5 * T
    nlinarith only [h2])
  have hsum : sourceBudget pre ctx ≤ (6000 * 31 ^ 6 + 30166) * T := by
    unfold sourceBudget
    nlinarith only [hp', hcan', hs', ho', h1]
  calc
    _ ≤ (6000 * 31 ^ 6 + 30166) * T := hsum
    _ ≤ (10000 * 31 ^ 6) * T := Nat.mul_le_mul_right _ (by norm_num)
    _ = runtimeBound B ctx.alphabet.length ctx.depth.length := by
      simp only [runtimeBound, T, s, K, Nat.mul_assoc]

end SubexponentialSAT.Subexp.ScoreBuilderBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem callback_eval (r : Fin 6 → Bool) (h n j : ℕ) (source out : List Bool) :
    ∃ t rf, t ≤ callbackBound h n j ∧
      Eval callback t (data r h n source out (unary j))
        (data rf h n source (recordPrefix h n j ++ out) []) ∧
      (∀ i : Fin 6, 3 ≤ i.val → rf i = r i) := by
  let a := data r h n source out (unary j)
  let b := copied a
  let c := transferred b
  have h1 : Eval copy (7*n+5) a b := by
    simpa [copy,b,copied,a,data] using TupleProgram.copy_eval (1 : Fin 9) 3 4 (0 : Fin 6) 1
      (by decide) (by decide) (by decide) (by decide) a (by rfl)
  have h2 : Eval transfer (3*j+3) b c := by
    simpa [c,transferred,b,copied,a,data,StackRoutines.copyStacks] using
      TupleProgram.transfer_eval (2 : Fin 9) 3 (0 : Fin 6) 1 (by decide) (by decide) b
  obtain ⟨re, h3base⟩ := Emit.command_eval (c.regs ∘ registers) h (n+j) out
  let small := Emit.data (c.regs ∘ registers) (unary h) (unary (n+j)) [] [] [] out
  let smallOut := Emit.data re (unary h) (unary (n+j)) [] [] [] (recordPrefix h n j ++ out)
  have hin : embedState registers ports c small = c := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;>
        simp [small,Emit.data,ports,c,transferred,b,copied,a,data,
          StackRoutines.transferStacks,StackRoutines.copyStacks,Nat.add_comm]
    · intros; rfl
  let d := embedState registers ports c smallOut
  have h3 : Eval emit (60*(h+(n+j))+174) c d := by
    have hh := eval_call_lifted (compiled Emit.command 0 5) registers ports c
      registers_injective ports_injective (compiled_halt_trace h3base 0 5)
    change Eval emit _ (embedState registers ports c small) d at hh
    rw [hin] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
  have hd : d.stacks = (data d.regs h n source (recordPrefix h n j ++ out) [] (unary (n+j))).stacks := by
    funext i
    by_cases hi : ∃ k, ports k = i
    · obtain ⟨k,rfl⟩ := hi
      rw [show d.stacks (ports k) = smallOut.stacks k from
        embedState_stack registers ports c smallOut ports_injective k]
      fin_cases k <;> rfl
    · rw [show d.stacks i = c.stacks i from
        embedState_stack_frame registers ports c smallOut i hi]
      have hi0 : i ≠ 0 := fun hh => hi ⟨0,hh.symm⟩
      have hi3 : i ≠ 3 := fun hh => hi ⟨1,hh.symm⟩
      have hi4 : i ≠ 4 := fun hh => hi ⟨2,hh.symm⟩
      have hi5 : i ≠ 5 := fun hh => hi ⟨3,hh.symm⟩
      have hi6 : i ≠ 6 := fun hh => hi ⟨4,hh.symm⟩
      have hi7 : i ≠ 7 := fun hh => hi ⟨5,hh.symm⟩
      fin_cases i <;> simp_all [c,transferred,b,copied,a,data,
        StackRoutines.transferStacks,StackRoutines.copyStacks]
  have h4 : Eval clear (2*(n+j)+3) d (cleared d) := by
    have hh := TupleProgram.clear_eval (3 : Fin 9) (0 : Fin 6) 1 d
    simpa [hd,data,clear,cleared,StackRoutines.clearStacks] using hh
  have hend : cleared d = data (cleared d).regs h n source (recordPrefix h n j ++ out) [] := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i; simp only [hd]; fin_cases i <;> simp [data]
  have hf (i : Fin 6) (hi : 3 ≤ i.val) : (cleared d).regs i = r i := by
    have hi0 : i ≠ 0 := by intro hh; subst i; omega
    have hi1 : i ≠ 1 := by intro hh; subst i; omega
    have hr : ¬ ∃ k, registers k = i := by
      rintro ⟨k,hk⟩; subst i; fin_cases k <;> simp [registers] at hi
    have hh := embedState_register_frame registers ports c smallOut i hr
    simp only [cleared,readRegs,Function.update_of_ne hi0,Function.update_of_ne hi1]
    rw [show d.regs i = c.regs i from hh]
    simp [c,transferred,b,copied,a,data,readRegs,hi0,hi1]
  have hh := h1.seq (h2.seq (h3.seq h4))
  rw [hend] at hh
  exact ⟨_,(cleared d).regs,by dsimp [callbackBound]; omega,hh,hf⟩

theorem loop_eval (js : List ℕ) (r : Fin 6 → Bool) (h n : ℕ) (out suffix : List Bool) :
    ∃ t rf, t ≤ 1+budget h n js ∧
      Eval (RecordPrograms.loop readerPorts callback) t
        (RecordMappedPrograms.afterTag readerPorts unary (data r h n [] out []) js suffix)
        (data rf h n suffix (prefixes h n js.reverse ++ out) []) ∧
      rf 3 = false ∧ rf 4 = true ∧ rf 5 = false := by
  induction js generalizing r out with
  | nil =>
      let rf := Function.update (Function.update (Function.update r 3 false) 4 true) 5 false
      refine ⟨1,rf,by simp [budget],?_,by simp [rf],by simp [rf],by simp [rf]⟩
      have hs : RecordMappedPrograms.afterTag readerPorts unary (data r h n [] out []) [] suffix =
          data rf h n suffix out [] := state_data r h n [] out [] false true false suffix []
      rw [hs]
      simpa [prefixes] using
        (Eval.while_false (test := readerPorts.tag) (body := RecordPrograms.body readerPorts callback)
          (a := data rf h n suffix out []) (by simp [data,rf,readerPorts]))
  | cons j js ih =>
      let tail := Encoding.encodeList unary js ++ suffix
      let ra := Function.update (Function.update (Function.update r 3 false) 4 true) 5 false
      obtain ⟨tc,rc,htc,hcb,hfr⟩ := callback_eval ra h n j tail out
      have hr3 : rc 3 = false := by simpa [ra] using hfr 3 (by decide)
      have hr4 : rc 4 = true := by simpa [ra] using hfr 4 (by decide)
      have hr5 : rc 5 = false := by simpa [ra] using hfr 5 (by decide)
      have hread := RecordPrograms.reader_eval readerPorts (data r h n [] out [])
        (unary j) tail [] true true false
      have hin : RecordMappedPrograms.afterTag readerPorts unary (data r h n [] out [])
          (j::js) suffix = RecordPrograms.state readerPorts (data r h n [] out []) true true false
          (Encoding.frame (unary j) ++ tail) [] := rfl
      rw [← hin] at hread
      simp only [List.append_nil,List.reverse_replicate] at hread
      rw [state_data] at hread
      have hs : RecordPrograms.state readerPorts (data rc h n [] (recordPrefix h n j ++ out) [])
          false true false tail [] = data rc h n tail (recordPrefix h n j ++ out) [] := by
        rw [state_data]
        congr 1
        funext i; fin_cases i <;> simp [hr3,hr4,hr5]
      have hpop := RecordMappedPrograms.pop_list_eval readerPorts unary
        (data rc h n [] (recordPrefix h n j ++ out) []) js suffix false true
      change Eval _ _ (RecordPrograms.state readerPorts _ false true false tail []) _ at hpop
      rw [hs] at hpop
      have hbranch := Eval.ite_false (yes := RecordPrograms.atom (.set readerPorts.tag false))
        (show (data rc h n tail (recordPrefix h n j ++ out) []).regs readerPorts.found = false from hr5) hpop
      obtain ⟨tr,rr,htr,hrest,hrf⟩ := ih rc (recordPrefix h n j ++ out)
      have hg : (RecordMappedPrograms.afterTag readerPorts unary (data r h n [] out [])
          (j::js) suffix).regs readerPorts.tag = true := by simp [RecordMappedPrograms.afterTag]
      have he := Eval.while_true hg (hread.seq (hcb.seq hbranch)) hrest
      refine ⟨6*j+4+(tc+2)+tr+1,rr,?_,?_,hrf⟩
      · simpa only [List.length_replicate] using (show
          (6*j+4+(tc+2))+tr+1 ≤ 1+budget h n (j::js) by simp only [budget]; omega)
      · simpa [RecordPrograms.loop,RecordPrograms.body,prefixes,List.reverse_cons,
          List.flatMap_append,List.append_assoc] using he

theorem command_eval (js : List ℕ) (r : Fin 6 → Bool) (h n : ℕ) (out suffix : List Bool) :
    ∃ t rf, t ≤ 3+budget h n js ∧
      Eval command t (data r h n (Encoding.encodeList unary js ++ suffix) out [])
        (data rf h n suffix (prefixes h n js.reverse ++ out) []) := by
  obtain ⟨t,rf,ht,he,_⟩ := loop_eval js r h n out suffix
  have hs := RecordPrograms.set_found_eval readerPorts (data r h n [] out [])
    (r 3) (r 4) (r 5) false (Encoding.encodeList unary js ++ suffix) []
  have hp := RecordMappedPrograms.pop_list_eval readerPorts unary
    (data r h n [] out []) js suffix (r 3) (r 4)
  have hh := hs.seq (hp.seq he)
  have hin : RecordPrograms.state readerPorts (data r h n [] out []) (r 3) (r 4) (r 5)
      (Encoding.encodeList unary js ++ suffix) [] =
      data r h n (Encoding.encodeList unary js ++ suffix) out [] := by
    rw [state_data]; simp only [Function.update_eq_self]
  rw [hin] at hh
  exact ⟨1+(1+t),rf,by omega,hh⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows


/-! Native per-variable incident-factor scan from the original scope stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem command_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    ∃ t rf, t ≤ bound scopes v ∧
      Eval command t (data r scopes n v z mask out) (result rf scopes n v z mask out) ∧
      (∀ i : Fin 16, 10 ≤ i.val → rf i = r i) := by
  let a := data r scopes n v z mask out
  let b := prepared a
  obtain ⟨t,rs,hs,_,_,_,ht⟩ := SubexpIncidencePlanScan.command_eval scopes
    (b.regs ∘ registers) v 0 0 [false] []
  let small := SubexpIncidencePlanScan.data (b.regs ∘ registers) v 0
    (scopeBits scopes) [false] [] 0
  let smallOut := SubexpIncidencePlanScan.data rs v scopes.length []
    (Encoding.encodeList unary (indices scopes v).reverse) [] (indices scopes v).length
  have hin : embedState registers ports b small = b := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;>
        simp [small,SubexpIncidencePlanScan.data,b,prepared,copied,a,data,
          TupleProgram.pushedState,StackRoutines.copyStacks,ports,Encoding.encodeNat,
          scopeBits]
    · intros; rfl
  have hs' : Eval SubexpIncidencePlanScan.command t small smallOut := by
    simpa [small,smallOut,indices,IncidencePlanSpec.incidentIndices,scopeBits,
      SubexpIncidencePlanScan.scopeBytes,SubexpIncidencePlanProgram.encode_indexPrefix,
      ← List.map_reverse,records_map] using hs
  let e := embedState registers ports b smallOut
  have he := eval_call_lifted (compiled SubexpIncidencePlanScan.command 6 7)
    registers ports b registers_injective ports_injective (compiled_halt_trace hs' 6 7)
  rw [hin] at he
  have hout : e = result e.regs scopes n v z mask out := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    change e.stacks i = (result e.regs scopes n v z mask out).stacks i
    by_cases hi : i.val < 10
    · let k : Fin 10 := ⟨i.val,hi⟩
      have hik : ports k = i := Fin.ext rfl
      rw [← hik,show e.stacks (ports k) = smallOut.stacks k from
        embedState_stack registers ports b smallOut ports_injective k]
      clear_value k
      fin_cases k <;> simp [smallOut,SubexpIncidencePlanScan.data,result,ports,data]
    · have hframe : ¬ ∃ k, ports k = i := by
        rintro ⟨k,hk⟩
        apply hi
        have hval := congrArg Fin.val hk
        simpa [ports] using hval ▸ k.isLt
      rw [show e.stacks i = b.stacks i from
        embedState_stack_frame registers ports b smallOut i hframe]
      have h2 : i ≠ 2 := by intro h; subst i; omega
      have h5 : i ≠ 5 := by intro h; subst i; omega
      have h6 : i ≠ 6 := by intro h; subst i; omega
      have h7 : i ≠ 7 := by intro h; subst i; omega
      have h9 : i ≠ 9 := by intro h; subst i; omega
      simp [b,prepared,copied,a,result,data,TupleProgram.pushedState,
        StackRoutines.copyStacks,h2,h5,h6,h7,h9]
  change Eval scan (t+1) b e at he
  rw [hout] at he
  refine ⟨_,e.regs,by dsimp [bound]; omega,(prepare_eval r scopes n v z mask out).seq he,?_⟩
  intro i hi
  have hr : ¬ ∃ k, registers k = i := by
    rintro ⟨k,hk⟩
    have hv := congrArg Fin.val hk
    have hlt := k.isLt
    change k.val = i.val at hv
    omega
  have hh := embedState_register_frame registers ports b smallOut i hr
  have hi0 : i ≠ 0 := by intro h; subst i; omega
  have hi1 : i ≠ 1 := by intro h; subst i; omega
  change e.regs i = b.regs i at hh
  rw [hh]
  simp [b,prepared,copied,a,data,TupleProgram.pushedState,readRegs,hi0,hi1]
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem command_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ)
    (mask : List Bool) :
    ∃ rf, Eval command (budget scopes) (Scan.data r scopes n 0 0 mask [])
      (Scan.data rf scopes n 0 scopes.length mask [false]) := by
  let a := Scan.data r scopes n 0 0 mask []
  let b := Scan.copied 20 0 a
  have hc := Scan.copy_eval 20 0 (by decide) (by decide) (by decide) a
    (by simp [a,Scan.data])
  let small := SubexpScopeCountSetup.counterState (b.regs 0) (b.regs 1)
    (Encoding.encodeList id (records scopes)) []
  let smallOut := SubexpScopeCountSetup.counterState false false [] (Scan.unary scopes.length)
  have hin : embedState registers ports b small = b := by
    apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;>
        simp [small,SubexpScopeCountSetup.counterState,ParserProgram.pair,ports,b,
          Scan.copied,StackRoutines.copyStacks,a,Scan.data,scope_eq]
    · intros; rfl
  have hs := SubexpScopeCountSetup.counter_trace (records scopes) (b.regs 0) (b.regs 1)
  have hs' : Trace SubexpScopeCountSetup.counterProgram
      (SubexpSunflowerProgram.CountRecords.loopSteps (records scopes))
      (small.withPC (some SubexpScopeCountSetup.counterProgram.entry)) (smallOut.withPC none) := by
    simpa [small,smallOut,records] using hs
  let c := embedState registers ports b smallOut
  have hcount := eval_call_lifted SubexpScopeCountSetup.counterProgram registers ports b
    registers_injective ports_injective hs'
  rw [hin] at hcount
  have hout : c = Scan.data c.regs scopes n 0 scopes.length mask [] := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    change c.stacks i = (Scan.data c.regs scopes n 0 scopes.length mask []).stacks i
    by_cases hi : ∃ k, ports k = i
    · obtain ⟨k,rfl⟩ := hi
      rw [show c.stacks (ports k) = smallOut.stacks k from
        embedState_stack registers ports b smallOut ports_injective k]
      fin_cases k <;> simp [smallOut,SubexpScopeCountSetup.counterState,ParserProgram.pair,ports,Scan.data]
    · rw [show c.stacks i = b.stacks i from
        embedState_stack_frame registers ports b smallOut i hi]
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h24 : i ≠ 24 := fun h => hi ⟨1,h.symm⟩
      simp [b,Scan.copied,StackRoutines.copyStacks,a,Scan.data,h0,h24]
  change Eval count _ b c at hcount
  rw [hout] at hcount
  let d := Scan.data c.regs scopes n 0 scopes.length mask []
  have hp := TupleProgram.pushConst_eval (25 : Fin 32) (0 : Fin 16) false d
  let e := TupleProgram.pushedState 25 0 false d
  have he : e = Scan.data e.regs scopes n 0 scopes.length mask [false] := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i; fin_cases i <;> simp [d,Scan.data]
  change Eval _ _ d e at hp
  rw [he] at hp
  refine ⟨e.regs,?_⟩
  convert hc.seq (hcount.seq hp) using 1 ; simp [budget,a,Scan.data] ; ring

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankSchedule
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scheduled rank of the literal native packing. The intermediate scan
premises are discharged for produced queries in the final certificate. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LeafParametersProgram
open BucketProgram.ProducedRank

def queryLow (q : LeafQueryFrontend.Query) : List Bool := q.forward.map Bool.not

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end


