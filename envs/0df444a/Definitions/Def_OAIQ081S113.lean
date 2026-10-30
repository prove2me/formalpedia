-- Prove2me | Definitions.Def_OAIQ081S113
-- name    : OAIQ081S113
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:29:47.670711+00:00
-- url     : https://prove2.me/theorems/fa15e60c-a897-43a6-a78c-8bab22773bf2
-- title:
--   Definitions bundle OAIQ081S113 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 73 declarations of OpenAI's Lean: 24 definitions and 49 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.combineBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.ReplaceData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.clearTemporary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.liftChecker`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Guard.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Mask.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputCall.callCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.activeAfter`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.copied`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.innerReset`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.moved`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.selectorAfter`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.tableAfter`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram.tableReset`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.callbackCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.cleanupCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.effect`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.generateCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.pairFinished`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.pairPrepared`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.prepareCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.sourceBudget`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_SparseCodeProgram`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramCounts`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramSize`, `SubexponentialSAT_SqrtLog_PackingProgramCombine`, `SubexponentialSAT_SqrtLog_SquarefreeProgramReplace`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_AssignmentInputCall`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_PairPlanPreparation`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_PairRuntimeBounds`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_SelectionTableProgram`, `SubexponentialSAT_Subexp_SelectorPairProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S090`, `OAIQ081S092`, `OAIQ081S094`, `OAIQ081S095`, `OAIQ081S096` and `OAIQ081S097` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S132`, `OAIQ081S133`, `OAIQ081S134`, `OAIQ081S135` and `OAIQ081S136`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S088
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S090
import Definitions.Def_OAIQ081S092
import Definitions.Def_OAIQ081S094
import Definitions.Def_OAIQ081S095
import Definitions.Def_OAIQ081S096
import Definitions.Def_OAIQ081S097

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted query physically receives the saved history, without a trial
candidate prefix. All routing, scratch reset and source reclamation are paid
commands. The query is composed through its actual evaluation and prefix proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage

open BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafOuterProgram

/-- Reset the routing temporary by an actual finite program. -/
def clearTemporary : Cmd 40 896 := .call (clearProgram 767 0 1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace Guard

def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 5 (d.stacks 9)⟩

end Guard

namespace Mask

def state (regs : Regs) (source mask output : List Bool) : Data :=
  ⟨regs, ![source, mask, [], output]⟩

end Mask

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionStreamProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed collision callback with a persistent output stream

The runtime ABI reserves stack 0 for a packed row table, stack 3 for its unary
word width, stacks 8 and 10 for the two read plans, and stack 11 for the output
stream. Stacks 1 and 12 hold the two gathered type encodings. The remaining
stacks are gathering scratch. All sizes, plans, and encoded words are data.

The equality stage below uses the existing fixed equality program, clears its
possibly unconsumed input suffixes, and pushes one collision bit. In particular,
an early mismatch cannot leave stale type bytes in the next callback's scratch.
-/

namespace SubexponentialSAT.Subexp.CollisionStreamProgram

open BitProgram StackRoutines StructuredCalls

theorem leftGather_eval (rows : List (List Bool)) (width : List Bool)
    (plan : List ℕ) (rightPlan stream : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ n ≤ GatherProgram.traceCost rows width.length plan,
    Eval leftGather n
      (stageState rows width [] [] (planBytes plan) rightPlan stream)
      (stageState rows width (GatherProgram.gathered rows plan) [] [] rightPlan stream) := by
  let d := stageState rows width [] [] (planBytes plan) rightPlan stream
  have ha : embedState gatherRegs leftPorts d (GatherProgram.inputState rows width plan) = d := by
    apply embedState_eq _ _ gatherRegs_injective leftPorts_injective
    · intro j; fin_cases j <;> simp [d, stageState, gatherRegs, GatherProgram.inputState,
        GatherProgram.baseState, RecordPrograms.state, GatherProgram.ports]
    · intro j; fin_cases j <;> simp [d, stageState, leftPorts, planBytes,
        GatherProgram.inputState, GatherProgram.baseState, RecordPrograms.state,
        GatherProgram.ports]
    · intros; rfl
    · intros; rfl
  have hb : embedState gatherRegs leftPorts d (GatherProgram.outputState rows width plan) =
      stageState rows width (GatherProgram.gathered rows plan) [] [] rightPlan stream := by
    apply embedState_eq _ _ gatherRegs_injective leftPorts_injective
    · intro j; fin_cases j <;> simp [stageState, gatherRegs, GatherProgram.outputState]
    · intro j; fin_cases j <;> simp [stageState, leftPorts, GatherProgram.outputState]
    · intros; rfl
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [leftPorts] using h.symm⟩
      have h8 : j ≠ 8 := fun h => hj ⟨8, by simpa [leftPorts] using h.symm⟩
      simp [d, stageState, h1, h8]
  obtain ⟨n, hn, ht⟩ := GatherProgram.program_run rows width plan hrows hplan
  have he := eval_call_lifted GatherProgram.program gatherRegs leftPorts d
    gatherRegs_injective leftPorts_injective ht
  exact ⟨n, hn, by simpa only [ha, hb, leftGather] using he⟩

theorem rightGather_eval (rows : List (List Bool)) (width left stream : List Bool)
    (plan : List ℕ) (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ n ≤ GatherProgram.traceCost rows width.length plan,
    Eval rightGather n
      (stageState rows width left [] [] (planBytes plan) stream)
      (stageState rows width left (GatherProgram.gathered rows plan) [] [] stream) := by
  let d := stageState rows width left [] [] (planBytes plan) stream
  have ha : embedState gatherRegs rightPorts d (GatherProgram.inputState rows width plan) = d := by
    apply embedState_eq _ _ gatherRegs_injective rightPorts_injective
    · intro j; fin_cases j <;> simp [d, stageState, gatherRegs, GatherProgram.inputState,
        GatherProgram.baseState, RecordPrograms.state, GatherProgram.ports]
    · intro j; fin_cases j <;> simp [d, stageState, rightPorts, leftPorts, planBytes,
        GatherProgram.inputState, GatherProgram.baseState, RecordPrograms.state,
        GatherProgram.ports]
    · intros; rfl
    · intros; rfl
  have hb : embedState gatherRegs rightPorts d (GatherProgram.outputState rows width plan) =
      stageState rows width left (GatherProgram.gathered rows plan) [] [] stream := by
    apply embedState_eq _ _ gatherRegs_injective rightPorts_injective
    · intro j; fin_cases j <;> simp [stageState, gatherRegs, GatherProgram.outputState]
    · intro j; fin_cases j <;> simp [stageState, rightPorts, leftPorts, GatherProgram.outputState]
    · intros; rfl
    · intro j hj
      have h12 : j ≠ 12 := fun h => hj ⟨1, by simpa [rightPorts] using h.symm⟩
      have h10 : j ≠ 10 := fun h => hj ⟨8, by simpa [rightPorts] using h.symm⟩
      simp [d, stageState, h12, h10]
  obtain ⟨n, hn, ht⟩ := GatherProgram.program_run rows width plan hrows hplan
  have he := eval_call_lifted GatherProgram.program gatherRegs rightPorts d
    gatherRegs_injective rightPorts_injective ht
  exact ⟨n, hn, by simpa only [ha, hb, rightGather] using he⟩

theorem callback_eval (rows : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (stream : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hleft : ∀ i ∈ left, i < rows.length) (hright : ∀ i ∈ right, i < rows.length) :
    ∃ n, n + 1 ≤ sourceBudget rows width.length left right ∧
      Eval command n (inputState rows width left right stream)
        (outputState rows width (collisionBit rows left right :: stream)) := by
  obtain ⟨nl, hnl, hl⟩ := leftGather_eval rows width left (planBytes right) stream hrows hleft
  obtain ⟨nr, hnr, hr⟩ := rightGather_eval rows width
    (GatherProgram.gathered rows left) stream right hrows hright
  let d := stageState rows width (GatherProgram.gathered rows left)
    (GatherProgram.gathered rows right) [] [] stream
  obtain ⟨n, hn, hs⟩ := seal_eval d
  have hd : sealed d (decide (d.stacks 1 = d.stacks 12)) =
      outputState rows width (collisionBit rows left right :: stream) := by
    apply state_ext
    · rfl
    · funext j
      fin_cases j <;> simp [d, stageState, sealed, outputState, collisionBit]
  rw [hd] at hs
  refine ⟨nl + (nr + n), ?_, hl.seq (hr.seq hs)⟩
  simp [d, stageState] at hn
  simp only [sourceBudget]
  omega

/-- One actual fixed-program run gathers both types, emits their collision bit,
and restores the scratch stacks and registers for the next callback. -/
theorem program_trace (rows : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (stream : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hleft : ∀ i ∈ left, i < rows.length) (hright : ∀ i ∈ right, i < rows.length) :
    ∃ n ≤ sourceBudget rows width.length left right,
      Trace program n
        ((inputState rows width left right stream).withPC (some program.entry))
        ((outputState rows width (collisionBit rows left right :: stream)).withPC none) := by
  obtain ⟨n, hn, he⟩ := callback_eval rows width left right stream hrows hleft hright
  exact ⟨n + 1, hn, compiled_halt_trace he 0 11⟩

end SubexponentialSAT.Subexp.CollisionStreamProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Streaming collisions from framed runtime tuples

The current word array and selected read plans are preserved. Each parsed
tuple is appended to the current array by actual transfer/copy routines, then
the fixed collision callback gathers the two types and emits one bit.
-/

namespace SubexponentialSAT.Subexp.CollisionTupleProgram

open BitProgram StackRoutines StructuredCalls

theorem collision_eval (f : Frame) (rows : List (List Bool)) (stream : List Bool)
    (hrows : ∀ row ∈ rows, row.length = f.width.length)
    (hl : ∀ i ∈ f.left, i < rows.length) (hr : ∀ i ∈ f.right, i < rows.length) :
    ∃ n ≤ CollisionStreamProgram.planBudget f.width.length f.left f.right,
      Eval collision n
        (state f rows.flatten (CollisionStreamProgram.planBytes f.left)
          (CollisionStreamProgram.planBytes f.right) stream [])
        (state f rows.flatten [] []
          (CollisionStreamProgram.collisionBit rows f.left f.right :: stream) []) := by
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.program_trace rows f.width f.left f.right
    stream hrows hl hr
  rw [CollisionStreamProgram.sourceBudget_eq_planBudget rows f.width.length f.left f.right
    hrows hl hr] at hn
  have he := eval_call_lifted CollisionStreamProgram.program lowRegs lowStacks
    (state f rows.flatten (CollisionStreamProgram.planBytes f.left)
      (CollisionStreamProgram.planBytes f.right) stream []) lowRegs_injective lowStacks_injective ht
  rw [show CollisionStreamProgram.inputState rows f.width f.left f.right stream =
    CollisionStreamProgram.stageState rows f.width [] [] (CollisionStreamProgram.planBytes f.left)
      (CollisionStreamProgram.planBytes f.right) stream from rfl,
    embed_state f _ _ _ _ rows rfl, embed_output] at he
  exact ⟨n, hn, he⟩

theorem callback_eval (current candidate : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (tail stream : List Bool)
    (hrows : ∀ row ∈ current ++ candidate, row.length = width.length)
    (hl : ∀ i ∈ left, i < (current ++ candidate).length)
    (hr : ∀ i ∈ right, i < (current ++ candidate).length) :
    let f : Frame := ⟨current.flatten, width, left, right, tail⟩
    ∃ n ≤ callbackCost current.flatten width.length left right candidate.flatten,
      Eval callback n (state f [] [] [] stream candidate.flatten.reverse)
        (state f [] [] [] (leafBit current.flatten width.length left right candidate.flatten :: stream) []) := by
  dsimp only
  let f : Frame := ⟨current.flatten, width, left, right, tail⟩
  let d0 := state f [] [] [] stream candidate.flatten.reverse
  let d1 := transferState d0 17 0
  let d2 := copyState d1 13 0
  let d3 := copyState d2 14 8
  let d4 := copyState d3 15 10
  have he : d4 = state f (current ++ candidate).flatten
      (CollisionStreamProgram.planBytes left) (CollisionStreamProgram.planBytes right) stream [] := by
    apply state_ext
    · funext j; fin_cases j <;> simp [d4, d3, d2, d1, d0, f, state, copyState,
        transferState, readRegs]
    · funext j; fin_cases j <;> simp [d4, d3, d2, d1, d0, f, state, copyState,
        transferState, copyStacks, transferStacks]
  have t0 := transfer_eval d0 17 0 (by decide)
  have t1 := copy_eval d1 13 0 (by decide) (by decide) (by decide)
    (by simp [d1, d0, f, transferState, state, transferStacks])
  have t2 := copy_eval d2 14 8 (by decide) (by decide) (by decide)
    (by simp [d2, d1, d0, f, copyState, transferState, state, copyStacks, transferStacks])
  have t3 := copy_eval d3 15 10 (by decide) (by decide) (by decide)
    (by simp [d3, d2, d1, d0, f, copyState, transferState, state, copyStacks, transferStacks])
  obtain ⟨n, hn, t4⟩ := collision_eval f (current ++ candidate) stream hrows hl hr
  rw [← he] at t4
  let d5 := state f (current ++ candidate).flatten [] []
    (CollisionStreamProgram.collisionBit (current ++ candidate) left right :: stream) []
  have t5 := clear_eval d5 0
  have hf : clearState d5 0 = state f [] [] []
      (leafBit current.flatten width.length left right candidate.flatten :: stream) [] := by
    rw [leafBit_eq_collision current candidate width.length hrows left right]
    apply state_ext
    · funext j; fin_cases j <;> simp [d5, state, clearState, readRegs]
    · funext j; fin_cases j <;> simp [d5, state, clearState, clearStacks]
  rw [hf] at t5
  have t := t0.seq (t1.seq (t2.seq (t3.seq (t4.seq t5))))
  refine ⟨_, ?_, t⟩
  simp [d5, d3, d2, d1, d0, f, state, copyState, transferState,
    copyStacks, transferStacks, callbackCost] at hn ⊢
  omega

theorem callback_contract (current : List (List Bool)) (width : List Bool)
    (left right : List ℕ) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost current.flatten width.length left right)
      (invariant current.flatten width left right)
      (effect current.flatten width.length left right)
      (validPayload current width.length left right) := by
  intro bits tail base hv hi
  obtain ⟨candidate, rfl, hrows, hl, hr⟩ := hv
  obtain ⟨stream, rfl⟩ := hi
  obtain ⟨n, hn, he⟩ := callback_eval current candidate width left right tail stream hrows hl hr
  refine ⟨n, baseState current.flatten width left right
      (leafBit current.flatten width.length left right candidate.flatten :: stream), hn,
      ⟨_, rfl⟩, ?_, ?_⟩
  · simp [effect, baseState, state]
  · simpa only [parser_state_eq] using he

/-- Every framed tuple is parsed and processed by the fixed callback. The
result is the reverse visit-order leaf stream, suitable for unary tallying. -/
theorem command_eval (current : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (tuples : List (List Bool)) (stream : List Bool)
    (hv : ∀ bits ∈ tuples, validPayload current width.length left right bits) :
    ∃ n, n + 1 ≤ sourceBudget current.flatten width.length left right tuples ∧
      Eval command n (inputState current.flatten width left right tuples stream)
        (baseState current.flatten width left right
          (streamed current.flatten width.length left right tuples stream)) := by
  obtain ⟨n, next, hn, hnext, history, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost current.flatten width.length left right)
    (invariant current.flatten width left right)
    (effect current.flatten width.length left right)
    (validPayload current width.length left right)
    (callback_contract current width left right) tuples []
    (baseState current.flatten width left right stream) hv ⟨stream, rfl⟩ false false false
  obtain ⟨out, rfl⟩ := hnext
  have hout : out = streamed current.flatten width.length left right tuples stream := by
    have h := history.fold_of_false (by simp) (fun d => d.stacks 11)
      (fun acc bits => leafBit current.flatten width.length left right bits :: acc)
      (fun _ _ _ h => h)
    simpa only [baseState, state, Fin.reduceEq, ite_true, if_true, ite_false, streamed] using h
  subst out
  have hany : tuples.any (fun _ => false) = false := by
    induction tuples <;> simp_all
  refine ⟨n, by dsimp [sourceBudget]; omega, ?_⟩
  have hfinal : RecordPrograms.state ports
      (baseState current.flatten width left right
        (streamed current.flatten width.length left right tuples stream))
      false true false [] [] =
      baseState current.flatten width left right
        (streamed current.flatten width.length left right tuples stream) := by
    rw [parser_state_eq]
    rfl
  simpa only [hany, unread_false, hfinal, ProgramEncoding.encodeRecords,
    inputState, List.append_nil, command] using he

theorem program_run (current : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (tuples : List (List Bool)) (stream : List Bool)
    (hv : ∀ bits ∈ tuples, validPayload current width.length left right bits) :
    RunsIn program (sourceBudget current.flatten width.length left right tuples)
      ((inputState current.flatten width left right tuples stream).withPC (some program.entry))
      ((baseState current.flatten width left right
        (streamed current.flatten width.length left right tuples stream)).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_eval current width left right tuples stream hv
  exact ⟨n + 1, hn, compiled_halt_trace he 16 11⟩

end SubexponentialSAT.Subexp.CollisionTupleProgram

end OAI.Algorithms
end

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

theorem stream_eval (current : List (List Bool)) (width : List Bool) (left right : List ℕ)
    (alphabet : List Bool) (tuples : List (List Bool)) (stream : List Bool)
    (hv : ∀ bits ∈ tuples, CollisionTupleProgram.validPayload current width.length left right bits) :
    ∃ n ≤ CollisionTupleProgram.sourceBudget current.flatten width.length left right tuples,
      Eval streamCommand n
        (storedState (fun _ => false) current.flatten width left right alphabet []
          (ProgramEncoding.encodeRecords tuples) [] stream)
        (outputState current.flatten width left right alphabet
          (CollisionTupleProgram.streamed current.flatten width.length left right tuples stream)) := by
  let d := storedState (fun _ => false) current.flatten width left right alphabet []
    (ProgramEncoding.encodeRecords tuples) [] stream
  obtain ⟨n, hn, ht⟩ := CollisionTupleProgram.program_run current width left right tuples stream hv
  have hin : embedState streamRegs streamPorts d
      (CollisionTupleProgram.inputState current.flatten width left right tuples stream) = d := by
    apply embedState_eq _ _ streamRegs_injective streamPorts_injective
    · intro i; fin_cases i <;> simp [d, storedState, streamRegs, CollisionTupleProgram.inputState,
        CollisionTupleProgram.baseState, CollisionTupleProgram.state, RecordPrograms.state,
        CollisionTupleProgram.ports]
    · intro i; fin_cases i <;> simp [d, storedState, streamPorts, CollisionTupleProgram.inputState,
        CollisionTupleProgram.baseState, CollisionTupleProgram.state, RecordPrograms.state,
        CollisionTupleProgram.ports]
    · intros; rfl
    · intros; rfl
  have hout : embedState streamRegs streamPorts d
      (CollisionTupleProgram.baseState current.flatten width left right
        (CollisionTupleProgram.streamed current.flatten width.length left right tuples stream)) =
      outputState current.flatten width left right alphabet
        (CollisionTupleProgram.streamed current.flatten width.length left right tuples stream) := by
    apply embedState_eq _ _ streamRegs_injective streamPorts_injective
    · intro i; fin_cases i <;> simp [outputState, storedState, streamRegs,
        CollisionTupleProgram.baseState, CollisionTupleProgram.state]
    · intro i; fin_cases i <;> simp [outputState, storedState, streamPorts,
        CollisionTupleProgram.baseState, CollisionTupleProgram.state]
    · intro j hj
      have h6 : j ≠ 6 := fun h => hj ⟨6, by simpa [streamRegs] using h.symm⟩
      simp [outputState, d, storedState, h6]
    · intro j hj
      have h16 : j ≠ 16 := fun h => hj ⟨16, by simpa [streamPorts] using h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, by simpa [streamPorts] using h.symm⟩
      simp [outputState, d, storedState, h16, h11]
  have he := eval_call_lifted CollisionTupleProgram.program streamRegs streamPorts d
    streamRegs_injective streamPorts_injective ht
  exact ⟨n, hn, by simpa only [hin, hout, streamCommand] using he⟩

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

def pairPrepared (ctx : Context) (tail stream : List Bool) (pair : PlanPair) : Data :=
  let d := RecordPrograms.state ports (baseState ctx stream) false true false tail []
  ⟨d.regs, Function.update (Function.update (Function.update d.stacks
      14 (CollisionStreamProgram.planBytes pair.1))
      15 (CollisionStreamProgram.planBytes pair.2)) 17 ctx.depth⟩

def pairFinished (ctx : Context) (tail stream : List Bool) (pair : PlanPair) : Data :=
  let d := RecordPrograms.state ports (baseState ctx (pairStream ctx pair stream))
    false true false tail []
  ⟨fun j => if j = 6 then true else d.regs j,
    Function.update (Function.update d.stacks 14 (CollisionStreamProgram.planBytes pair.1))
      15 (CollisionStreamProgram.planBytes pair.2)⟩

def generateCost (ctx : Context) (pair : PlanPair) : ℕ :=
  CollisionGenerateProgram.sourceBudget ctx.current.flatten ctx.width.length
    pair.1 pair.2 ctx.alphabet ctx.depth.length

def prepareCost (ctx : Context) (pair : PlanPair) : ℕ :=
  3 * (pairBytes pair).length +
    9 * ((CollisionStreamProgram.planBytes pair.1).length +
      (CollisionStreamProgram.planBytes pair.2).length) + 7 * ctx.depth.length + 32

theorem prepare_eval (ctx : Context) (pair : PlanPair) (tail stream : List Bool) :
    Eval prepare (prepareCost ctx pair)
      (RecordPrograms.state ports (baseState ctx stream)
        false true false tail (pairBytes pair).reverse)
      (pairPrepared ctx tail stream pair) := by
  let left := CollisionStreamProgram.planBytes pair.1
  let right := CollisionStreamProgram.planBytes pair.2
  let d0 := RecordPrograms.state ports (baseState ctx stream)
    false true false tail (pairBytes pair).reverse
  let d1 := transferred 21 22 d0
  let d2 := fieldRead left (Encoding.frame right) d1
  let d3 := transferred 25 14 d2
  let d4 := fieldRead right [] d3
  let d5 := transferred 25 15 d4
  let d6 := copiedDepth d5
  have h1 : Eval (transfer 21 22) (3 * (pairBytes pair).length + 3) d0 d1 := by
    simpa [d0, d1, RecordPrograms.state, ports] using
      transfer_eval 21 22 (by decide) d0
  have hs1 : d1.stacks 22 = Encoding.frame left ++ Encoding.frame right := by
    simp [d1, transferred, transferStacks, d0, RecordPrograms.state, ports,
      baseState, pairBytes, left, right]
  have h2 : Eval (RecordPrograms.reader fieldPorts) (6 * left.length + 4) d1 d2 :=
    readField_eval d1 left (Encoding.frame right) hs1
  have ho1 : d1.stacks 25 = [] := by
    simp [d1, transferred, transferStacks, d0, RecordPrograms.state, ports, baseState]
  have h3 : Eval (transfer 25 14) (3 * left.length + 3) d2 d3 := by
    simpa [d3, d2, fieldRead, RecordPrograms.state, fieldPorts, ho1] using
      transfer_eval 25 14 (by decide) d2
  have hs3 : d3.stacks 22 = Encoding.frame right ++ [] := by
    simp [d3, transferred, transferStacks, d2, fieldRead, RecordPrograms.state, fieldPorts]
  have h4 : Eval (RecordPrograms.reader fieldPorts) (6 * right.length + 4) d3 d4 :=
    readField_eval d3 right [] hs3
  have h5 : Eval (transfer 25 15) (3 * right.length + 3) d4 d5 := by
    simpa [d5, d4, fieldRead, RecordPrograms.state, fieldPorts, d3,
      transferred, transferStacks] using transfer_eval 25 15 (by decide) d4
  have ht : d5.stacks 24 = [] := by
    simp [d5, d4, d3, d2, d1, d0, transferred, transferStacks, fieldRead,
      RecordPrograms.state, fieldPorts, ports, baseState]
  have hd : d5.stacks 23 = ctx.depth := by
    simp [d5, d4, d3, d2, d1, d0, transferred, transferStacks, fieldRead,
      RecordPrograms.state, fieldPorts, ports, baseState]
  have h6 : Eval copyDepth (7 * ctx.depth.length + 5) d5 d6 := by
    simpa only [d6, hd] using copyDepth_eval d5 ht
  have hend : resetInnerAfter d6 = pairPrepared ctx tail stream pair := by
    apply state_ext
    · funext j; fin_cases j <;>
        simp [resetInnerAfter, d6, copiedDepth, d5, d4, d3, d2, d1, d0,
          transferred, fieldRead, RecordPrograms.state, fieldPorts, ports,
          baseState, pairPrepared, readRegs]
    · funext j; fin_cases j <;>
        simp [resetInnerAfter, d6, copiedDepth, copyStacks, d5, d4, d3, d2, d1, d0,
          transferred, transferStacks, fieldRead, RecordPrograms.state, fieldPorts, ports,
          baseState, pairPrepared, pairBytes, left, right]
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (resetInner_eval d6))))))
  rw [hend] at he
  convert he using 1 ; dsimp [prepare, prepareCost, left, right] ; ring

def cleanupCost (pair : PlanPair) : ℕ :=
  2 * ((CollisionStreamProgram.planBytes pair.1).length +
    (CollisionStreamProgram.planBytes pair.2).length) + 16

theorem cleanup_eval (ctx : Context) (pair : PlanPair) (tail stream : List Bool) :
    Eval cleanup (cleanupCost pair) (pairFinished ctx tail stream pair)
      (RecordPrograms.state ports (baseState ctx (pairStream ctx pair stream))
        false true false tail []) := by
  let d0 := pairFinished ctx tail stream pair
  let d1 := cleared 14 d0
  let d2 := cleared 15 d1
  have h1 : Eval (clear 14) (2 * (CollisionStreamProgram.planBytes pair.1).length + 3)
      d0 d1 := by simpa [d0, d1, pairFinished] using clear_eval 14 d0
  have h2 : Eval (clear 15) (2 * (CollisionStreamProgram.planBytes pair.2).length + 3)
      d1 d2 := by
    simpa [d2, d1, cleared, clearStacks, d0, pairFinished] using clear_eval 15 d1
  have hend : resetInnerAfter d2 =
      RecordPrograms.state ports (baseState ctx (pairStream ctx pair stream))
        false true false tail [] := by
    apply state_ext
    · funext j; fin_cases j <;>
        simp [resetInnerAfter, d2, d1, d0, cleared, pairFinished, readRegs,
          RecordPrograms.state, ports, baseState]
    · funext j; fin_cases j <;>
        simp [resetInnerAfter, d2, d1, d0, cleared, clearStacks, pairFinished,
          RecordPrograms.state, ports, baseState]
  have he := h1.seq (h2.seq (resetInner_eval d2))
  rw [hend] at he
  convert he using 1 ; dsimp [cleanup, cleanupCost] ; ring

def callbackCost (ctx : Context) (bits : List Bool) : ℕ :=
  prepareCost ctx (readPair bits) + generateCost ctx (readPair bits) +
    cleanupCost (readPair bits)

def effect (ctx : Context) (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 11 = pairStream ctx (readPair bits) (a.stacks 11)

theorem records_fold (ctx : Context) (pairs : List PlanPair) (stream : List Bool) :
    (pairs.map pairBytes).foldl (fun acc bits => pairStream ctx (readPair bits) acc) stream =
      streamedPairs ctx pairs stream := by
  induction pairs generalizing stream with
  | nil => rfl
  | cons pair pairs ih =>
    simpa only [List.map_cons, List.foldl_cons, readPair_pairBytes, streamedPairs] using
      ih (pairStream ctx pair stream)

def inputState (ctx : Context) (pairs : List PlanPair) : Data :=
  RecordPrograms.state ports (baseState ctx []) false false false (pairRecords pairs) []

theorem inputState_regs (ctx : Context) (pairs : List PlanPair) :
    (inputState ctx pairs).regs = fun _ => false := by
  funext j
  fin_cases j <;> simp [inputState, RecordPrograms.state, ports, baseState]

theorem inputState_stacks (ctx : Context) (pairs : List PlanPair) :
    (inputState ctx pairs).stacks = fun j =>
      if j = 3 then ctx.width else if j = 13 then ctx.current.flatten
      else if j = 19 then ProgramEncoding.encodeRecords ctx.alphabet
      else if j = 23 then ctx.depth else if j = 20 then pairRecords pairs else [] := by
  funext j
  fin_cases j <;> simp [inputState, RecordPrograms.state, ports, baseState]

theorem outputState_stacks (ctx : Context) (pairs : List PlanPair) :
    (outputState ctx pairs).stacks = fun j =>
      if j = 3 then ctx.width else if j = 13 then ctx.current.flatten
      else if j = 19 then ProgramEncoding.encodeRecords ctx.alphabet
      else if j = 23 then ctx.depth else if j = 18 then UnaryCompare.encode (score ctx pairs)
      else [] := by
  funext j
  fin_cases j <;> simp [outputState, afterTally, baseState, score, UnaryCompare.encode]

theorem outputState_regs (ctx : Context) (pairs : List PlanPair) :
    (outputState ctx pairs).regs = fun j => decide (j = 11) := by
  funext j
  fin_cases j <;> simp [outputState, afterTally, baseState, readRegs]

def sourceBudget (ctx : Context) (pairs : List PlanPair) : ℕ :=
  RecordPrograms.budget (callbackCost ctx) (pairs.map pairBytes) +
    5 * (pairs.length * ctx.alphabet.length ^ ctx.depth.length) + 7

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

def liftChecker (checker : Cmd 16 40) (input output : Fin 40) : Cmd 16 48 :=
  .call (ProgramLinking.liftProgram (compiled checker input output) id checkerPorts)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairRuntimeBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform bounds for the executed pair scorer

The polynomial parameter bounds physical input lengths.  The exponential
factor is the actual number of tuples emitted by each generator call.
-/

namespace SubexponentialSAT.Subexp.PairRuntimeBounds

open BitProgram PairScoreProgram PairScoreBounds

theorem pairRecords_length_le (pairs : List PlanPair) (B : ℕ)
    (h : ∀ pair ∈ pairs, (pairBytes pair).length ≤ B) :
    (pairRecords pairs).length ≤ 2 * pairs.length * B + 2 * pairs.length + 1 := by
  have he := encoded_length_le (pairs.map pairBytes) B (by
    intro bits hbits
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hbits
    exact h pair hpair)
  simpa only [List.length_map, pairRecords] using he

theorem pair_plan_bytes_le (pair : PlanPair) :
    (CollisionStreamProgram.planBytes pair.1).length ≤ (pairBytes pair).length ∧
      (CollisionStreamProgram.planBytes pair.2).length ≤ (pairBytes pair).length := by
  simp only [pairBytes, List.length_append, Encoding.length_frame]
  omega

theorem fixedCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hc : ctx.current.flatten.length ≤ B) (hw : ctx.width.length ≤ B)
    (hp : (pairBytes pair).length ≤ B) :
    CollisionTupleProgram.fixedCost ctx.current.flatten ctx.width.length pair.1 pair.2 ≤
      200 * (B + 1) ^ 2 := by
  have hb := pair_plan_bytes_le pair
  have hl := plan_sizes_le_bytes pair.1
  have hr := plan_sizes_le_bytes pair.2
  have hbl := hb.1.trans hp
  have hbr := hb.2.trans hp
  have hsl := hl.1.trans hbl
  have hsr := hr.1.trans hbr
  have hll := hl.2.trans hbl
  have hlr := hr.2.trans hbr
  unfold CollisionTupleProgram.fixedCost CollisionStreamProgram.planBudget
  calc
    _ ≤ 9 * B + 7 * B + 7 * B +
        (34 + (14 * B + 16) * (B + B) + (32 * B + 27) * B + (23 * B + 27) * B) + 21 := by
      gcongr
    _ ≤ 200 * (B + 1) ^ 2 := by nlinarith

theorem generateCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length)
    (ha : ∀ row ∈ ctx.alphabet, row.length ≤ ctx.width.length)
    (hc : ctx.current.flatten.length ≤ B) (hw : ctx.width.length ≤ B)
    (hd : ctx.depth.length ≤ B) (hp : (pairBytes pair).length ≤ B) :
    generateCost ctx pair ≤ 4000 * (B + 1) ^ 4 * ctx.alphabet.length ^ ctx.depth.length := by
  let s := B + 1
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have h12 : s ≤ s ^ 2 := le_self_pow₀ hs (by omega)
  have h34 : s ^ 3 ≤ s ^ 4 := pow_le_pow_right₀ hs (by omega)
  have hds : ctx.depth.length + 1 ≤ s := by dsimp [s]; omega
  have hws : ctx.width.length ≤ s := by dsimp [s]; omega
  have hwidth : (ctx.depth.length + 1) * ctx.width.length + 1 ≤ 2 * s ^ 2 := by
    have hmul := Nat.mul_le_mul hds hws
    nlinarith only [hmul, hs]
  have hpow := generated_powerCost_le ctx.alphabet ctx.depth.length ctx.width.length hA ha
  have hpow' : TupleProgram.powerCost ctx.alphabet ctx.depth.length [[]] ≤ 1600 * s ^ 3 * K := by
    calc
      _ ≤ 800 * s * K * (2 * s ^ 2) := hpow.trans (by gcongr)
      _ = _ := by ring
  have hf := fixedCost_le ctx pair B hc hw hp
  have hf' : CollisionTupleProgram.fixedCost ctx.current.flatten ctx.width.length pair.1 pair.2 + 22 ≤
      222 * s ^ 2 := by
    change _ ≤ 222 * (B + 1) ^ 2
    nlinarith only [hf, Nat.zero_le B]
  have he := encoded_generated_length_le ctx.alphabet ctx.depth.length ctx.width.length hA ha
  have he' : (ProgramEncoding.encodeRecords
      (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]])).length + 1 ≤ 6 * s ^ 2 * K := by
    have hm : ctx.depth.length * ctx.width.length ≤ s ^ 2 := by
      have h := Nat.mul_le_mul (show ctx.depth.length ≤ s by omega) hws
      nlinarith only [h]
    calc
      _ ≤ (2 * ctx.depth.length * ctx.width.length + 4) * K := he
      _ ≤ (6 * s ^ 2) * K := Nat.mul_le_mul_right _ (by nlinarith only [hm, hs])
  have ht := CollisionTupleProgram.sourceBudget_le_serialized ctx.current.flatten
    ctx.width.length pair.1 pair.2 (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]])
  have ht' : CollisionTupleProgram.sourceBudget ctx.current.flatten ctx.width.length
      pair.1 pair.2 (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]]) ≤ 1332 * s ^ 4 * K := by
    calc
      _ ≤ (222 * s ^ 2) * (6 * s ^ 2 * K) := ht.trans (Nat.mul_le_mul hf' he')
      _ = _ := by ring
  have hp4 : TupleProgram.powerCost ctx.alphabet ctx.depth.length [[]] ≤ 1600 * s ^ 4 * K :=
    hpow'.trans (by gcongr)
  have h1 : 1 ≤ s ^ 4 * K := Nat.mul_le_mul (one_le_pow₀ hs) hk
  change TupleProgram.powerCost ctx.alphabet ctx.depth.length [[]] +
    CollisionTupleProgram.sourceBudget ctx.current.flatten ctx.width.length pair.1 pair.2
      (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]]) + 25 ≤ 4000 * s ^ 4 * K
  nlinarith only [h1, hp4, ht']

theorem callbackCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length)
    (ha : ∀ row ∈ ctx.alphabet, row.length ≤ ctx.width.length)
    (hc : ctx.current.flatten.length ≤ B) (hw : ctx.width.length ≤ B)
    (hd : ctx.depth.length ≤ B) (hp : (pairBytes pair).length ≤ B) :
    callbackCost ctx (pairBytes pair) ≤ 4100 * (B + 1) ^ 4 * ctx.alphabet.length ^ ctx.depth.length := by
  have hg := generateCost_le ctx pair B hA ha hc hw hd hp
  have hb := pair_plan_bytes_le pair
  have hbl := hb.1.trans hp
  have hbr := hb.2.trans hp
  have hsmall : prepareCost ctx pair + cleanupCost pair ≤ 80 * (B + 1) := by
    unfold prepareCost cleanupCost
    omega
  have hpower : B + 1 ≤ (B + 1) ^ 4 := by
    exact le_self_pow₀ (by omega) (by omega)
  have hk : 1 ≤ ctx.alphabet.length ^ ctx.depth.length := one_le_pow₀ hA
  have hscale : B + 1 ≤ (B + 1) ^ 4 * ctx.alphabet.length ^ ctx.depth.length := by
    simpa using Nat.mul_le_mul hpower hk
  simp only [callbackCost, readPair_pairBytes]
  nlinarith

/-- A fixed polynomial in physical input size times the actual per-pair
tuple count.  This bounds the exact source budget of `program_run`. -/
theorem sourceBudget_le (ctx : Context) (pairs : List PlanPair) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length)
    (ha : ∀ row ∈ ctx.alphabet, row.length ≤ ctx.width.length)
    (hc : ctx.current.flatten.length ≤ B) (hw : ctx.width.length ≤ B)
    (hd : ctx.depth.length ≤ B) (hn : pairs.length ≤ B)
    (hp : ∀ pair ∈ pairs, (pairBytes pair).length ≤ B) :
    sourceBudget ctx pairs ≤ 5000 * (B + 1) ^ 5 * ctx.alphabet.length ^ ctx.depth.length := by
  let s := B + 1
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have h14 : s ≤ s ^ 4 := le_self_pow₀ hs (by omega)
  have hscale : s ≤ s ^ 4 * K := by simpa using Nat.mul_le_mul h14 hk
  have hb := budget_bounded (callbackCost ctx) (pairs.map pairBytes) B (4100 * s ^ 4 * K)
    (by intro bits h; obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp h; exact hp pair hpair)
    (by intro bits h; obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp h
        exact callbackCost_le ctx pair B hA ha hc hw hd (hp pair hpair))
  rw [List.length_map] at hb
  have hstep : 6 * B + 4100 * s ^ 4 * K + 7 ≤ 4113 * s ^ 4 * K := by
    dsimp [s] at hscale ⊢
    nlinarith
  have hbudget : RecordPrograms.budget (callbackCost ctx) (pairs.map pairBytes) ≤ 4113 * s ^ 5 * K := by
    calc
      _ ≤ pairs.length * (4113 * s ^ 4 * K) := hb.trans (Nat.mul_le_mul_left _ hstep)
      _ ≤ s * (4113 * s ^ 4 * K) := Nat.mul_le_mul_right _ (by dsimp [s]; omega)
      _ = _ := by ring
  have h15 : s ≤ s ^ 5 := le_self_pow₀ hs (by omega)
  have htail : pairs.length * K ≤ s ^ 5 * K := Nat.mul_le_mul_right _ (by dsimp [s] at *; omega)
  have hone : 1 ≤ s ^ 5 * K := Nat.mul_le_mul (one_le_pow₀ hs) hk
  change _ + 5 * (pairs.length * K) + 7 ≤ 5000 * s ^ 5 * K
  nlinarith

end SubexponentialSAT.Subexp.PairRuntimeBounds

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

/-- The membership phase copies the persistent pair plan, calls the existing
actual encoded-membership scanner, and clears every scan residual. -/
theorem member_eval (records : List (List Bool)) (query source threshold acc output : List Bool)
    (regs : Regs) :
    ∃ n ≤ (20 * query.length + 40) * (Encoding.encodeList id records).length + 20,
      ∃ rf : Regs, rf 4 = decide (query ∈ records) ∧
      (∀ j : Fin 10, 7 ≤ j.val → rf j = regs j) ∧
      Eval member n
        (state regs source (Encoding.encodeList id records) threshold acc query.reverse output)
        (state rf source (Encoding.encodeList id records) threshold acc query.reverse output) := by
  let start := state regs source (Encoding.encodeList id records) threshold acc query.reverse output
  let prepared := copied 6 0 start
  let inner : ExecCNFMembership.Data := ⟨prepared.regs ∘ low7, prepared.stacks ∘ low5⟩
  have hi : ExecCNFMembership.invariant query inner := by
    simp [ExecCNFMembership.invariant, inner, prepared, start, copyStacks, low5]
  obtain ⟨next, hnxt, n, hn, ht⟩ := ExecCNFMembership.membership_runsIn query records [] inner hi
    (inner.regs 5) (inner.regs 6) (inner.regs 4)
  let last := RecordPrograms.state ExecCNFMembership.ports next false true
    (decide (query ∈ records)) (RecordPrograms.unread (fun bits => decide (bits = query)) records [])
    [decide (query ∈ records)]
  have hinput : RecordPrograms.state ExecCNFMembership.ports inner
      (inner.regs 5) (inner.regs 6) (inner.regs 4)
      (Encoding.encodeList id records ++ []) [] = inner := by
    apply RecordPrograms.state_eq_self <;>
      simp [inner, prepared, start, copyStacks, low5 ]
  rw [hinput] at ht
  have hembed : embedState low7 low5 prepared inner = prepared := by
    apply embedState_eq_of_ports _ _ _ _ _ low7_injective low5_injective <;> intros <;> rfl
  let scanned := embedState low7 low5 prepared last
  have hscan : Eval membershipCall n prepared scanned := by
    have h := eval_call_lifted ExecCNFMembership.membershipProgram low7 low5 prepared
      low7_injective low5_injective ht
    simpa only [hembed, membershipCall, scanned, last] using h
  have hreg4 : scanned.regs 4 = decide (query ∈ records) := by
    change scanned.regs (low7 4) = _
    rw [embedState_register _ _ _ _ low7_injective]
    simp [last, RecordPrograms.state ]
  have hregs (j : Fin 10) (hj : 7 ≤ j.val) : scanned.regs j = regs j := by
    have hout : ¬ ∃ i, low7 i = j := by
      rintro ⟨i, h⟩
      have hv := congrArg Fin.val h
      change i.val = j.val at hv
      omega
    rw [embedState_register_frame _ _ _ _ j hout]
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simp [prepared, reset, start, readRegs, h0, h1]
  have hs (j : Fin 5) : scanned.stacks (low5 j) = last.stacks j :=
    embedState_stack _ _ _ _ low5_injective j
  have hframe (j : Fin 12) (hj : 5 ≤ j.val) : scanned.stacks j = start.stacks j := by
    have hout : ¬ ∃ i, low5 i = j := by
      rintro ⟨i, h⟩
      have hv := congrArg Fin.val h
      change i.val = j.val at hv
      omega
    rw [embedState_stack_frame _ _ _ _ j hout]
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    simp [prepared, copyStacks, h0]
  have hs0 := hs 0
  have hs1 := hs 1
  have hs2 := hs 2
  have hs3 := hs 3
  have hs4 := hs 4
  simp only [low5 ] at hs0 hs1 hs2 hs3 hs4
  simp [last, RecordPrograms.state, hnxt.1, hnxt.2.1,
    hnxt.2.2] at hs0 hs1 hs2 hs3 hs4
  let finish := cleared 1 (cleared 0 scanned)
  have hfinish : finish = state finish.regs source (Encoding.encodeList id records)
      threshold acc query.reverse output := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j
    all_goals simp [ clearStacks, hs2, hs3, hs4,
      hframe 5 (by decide), hframe 6 (by decide), hframe 7 (by decide),
      hframe 8 (by decide), hframe 9 (by decide), hframe 10 (by decide),
      hframe 11 (by decide), start ]
  have hc := copy_eval 6 0 4 start (by decide) (by decide) (by decide) rfl
  have hz0 := clear_eval 0 scanned
  have hz1 := clear_eval 1 (cleared 0 scanned)
  have hall := hc.seq (hscan.seq (hz0.seq hz1))
  change Eval member _ start finish at hall
  rw [hfinish] at hall
  refine ⟨_, ?_, finish.regs, ?_, ?_, hall⟩
  · have hu := unread_length_le (fun bits => decide (bits = query)) records
    simp only [start, List.length_cons, List.length_nil, hs0, clearStacks, hs1, Function.update_of_ne (by decide : (1 : Fin 12) ≠ 0)]
    dsimp
    nlinarith
  · simp [finish, reset, readRegs, hreg4]
  · intro j hj
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simpa [finish, cleared, reset, readRegs, h0, h1] using hregs j hj

theorem reverse_eval (records : List (List Bool)) (source plan threshold : List Bool) (regs : Regs) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length,
      Eval reverseCall n
        (state regs source plan threshold (Encoding.encodeList id records) [] [false])
        (state (flags regs false true false) source plan threshold [] []
          (Encoding.encodeList id records.reverse)) := by
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] threshold
    (regs 0) (regs 1) (regs 9)
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram emitRegs reverseStack
    (state regs source plan threshold (Encoding.encodeList id records) [] [false])
    emitRegs_injective reverseStack_injective ht
  refine ⟨n, hn, ?_⟩
  simpa only [List.append_nil, Encoding.encodeList, embed_reverse, flags_self, reverseCall] using he

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPlanPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual parsing and record-order preparation of the two plans in a pair
payload. Registers 0, 1, and 2 are scratch; all other registers are framed. -/

namespace SubexponentialSAT.Subexp.PairPlanPreparation

open BitProgram StackRoutines StructuredCalls

theorem reverse_eval (a : Data) (src dst : Fin 34)
    (hi : Function.Injective (reversePorts src dst)) (records acc : List (List Bool))
    (hin : a.stacks src = ProgramEncoding.encodeRecords records)
    (hacc : a.stacks dst = ProgramEncoding.encodeRecords acc) (h4 : a.stacks 4 = []) :
    ∃ n ≤ 10 * (ProgramEncoding.encodeRecords records).length,
      Eval (reverseRecords src dst) n a
        (reversed a src dst (ProgramEncoding.encodeRecords (records.reverse ++ acc))) := by
  have hs1 : src ≠ 1 := by simpa [reversePorts] using hi.ne (show (0 : Fin 4) ≠ 1 by decide)
  have hsd : src ≠ dst := by simpa [reversePorts] using hi.ne (show (0 : Fin 4) ≠ 2 by decide)
  have hs4 : src ≠ 4 := by simpa [reversePorts] using hi.ne (show (0 : Fin 4) ≠ 3 by decide)
  have hd1 : dst ≠ 1 := by simpa [reversePorts] using hi.ne (show (2 : Fin 4) ≠ 1 by decide)
  have hd4 : dst ≠ 4 := by simpa [reversePorts] using hi.ne (show (2 : Fin 4) ≠ 3 by decide)
  let x := SubexpNormalizeProgram.filterState (a.regs 0) (a.regs 1) (a.regs 2)
    (ProgramEncoding.encodeRecords records) (a.stacks 1) (ProgramEncoding.encodeRecords acc) []
  let y := SubexpNormalizeProgram.filterState false true false [] (a.stacks 1)
    (ProgramEncoding.encodeRecords (records.reverse ++ acc)) []
  have hx : embedState smallRegs (reversePorts src dst) a x = a := by
    apply embedState_eq _ _ smallRegs_injective hi
    · intro i; fin_cases i <;> simp [x, smallRegs, SubexpNormalizeProgram.filterState]
    · intro i; fin_cases i <;> simp [x, reversePorts, SubexpNormalizeProgram.filterState, hin, hacc, h4]
    · intros; rfl
    · intros; rfl
  have hy : embedState smallRegs (reversePorts src dst) a y =
      reversed a src dst (ProgramEncoding.encodeRecords (records.reverse ++ acc)) := by
    apply embedState_eq _ _ smallRegs_injective hi
    · intro i; fin_cases i <;> simp [y, smallRegs, reversed, SubexpNormalizeProgram.filterState]
    · intro i; fin_cases i <;> simp [y, reversePorts, reversed, SubexpNormalizeProgram.filterState,
        hsd, Ne.symm hs1, Ne.symm hs4, Ne.symm hd1, Ne.symm hd4, h4]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [smallRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [smallRegs] using h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, by simpa [smallRegs] using h.symm⟩
      simp [reversed, h0, h1, h2]
    · intro j hj
      have hs : j ≠ src := fun h => hj ⟨0, by simpa [reversePorts] using h.symm⟩
      have hd : j ≠ dst := fun h => hj ⟨2, by simpa [reversePorts] using h.symm⟩
      simp [reversed, hs, hd]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc [] (a.stacks 1)
    (a.regs 0) (a.regs 1) (a.regs 2)
  have ht' : Trace SubexpNormalizeProgram.reverseRecordsProgram n
      (x.withPC (some SubexpNormalizeProgram.reverseRecordsProgram.entry)) (y.withPC none) := by
    simpa only [x, y, ProgramEncoding.encodeRecords, Encoding.encodeList,
      List.append_nil] using ht
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram smallRegs
    (reversePorts src dst) a smallRegs_injective hi ht'
  exact ⟨n, hn, by simpa only [hx, hy, reverseRecords] using he⟩

theorem buildUnion_eval (a : Data) (left right : List (List Bool))
    (hl : a.stacks 24 = ProgramEncoding.encodeRecords left)
    (hr : a.stacks 25 = ProgramEncoding.encodeRecords right)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h4 : a.stacks 4 = []) (h6 : a.stacks 6 = []) :
    ∃ n ≤ 17 * (ProgramEncoding.encodeRecords left).length +
        7 * (ProgramEncoding.encodeRecords right).length + 10,
      Eval buildUnion n a (unionPrepared a left right) := by
  let a1 := copied a 25 6
  let a2 := copied a1 24 0
  have t0 := copy_eval a 25 6 (by decide) (by decide) (by decide) h1
  have t1 := copy_eval a1 24 0 (by decide) (by decide) (by decide)
    (by simp [a1, copied, copyStacks, h1])
  obtain ⟨n, hn, t2⟩ := reverse_eval a2 0 6 (by decide) left right
    (by simp [a2, a1, copied, copyStacks, hl, h0])
    (by simp [a2, a1, copied, copyStacks, hr, h6])
    (by simp [a2, a1, copied, copyStacks, h4])
  have he : reversed a2 0 6 (ProgramEncoding.encodeRecords (left.reverse ++ right)) =
      unionPrepared a left right := by
    apply state_ext
    · funext j; fin_cases j <;> simp [a2, a1, reversed, copied, readRegs, unionPrepared]
    · funext j; fin_cases j <;> simp [a2, a1, reversed, copied, copyStacks, unionPrepared, h0]
  rw [he] at t2
  refine ⟨_, ?_, t0.seq (t1.seq t2)⟩
  have he24 : a1.stacks 24 = ProgramEncoding.encodeRecords left := by
    simp [a1, copied, copyStacks, hl]
  rw [hr, he24]
  omega

theorem reverseQueries_eval (a : Data) (left right : List (List Bool))
    (hl : a.stacks 24 = ProgramEncoding.encodeRecords left)
    (hr : a.stacks 25 = ProgramEncoding.encodeRecords right)
    (h4 : a.stacks 4 = []) :
    ∃ n ≤ 2 * (a.stacks 6).length + 2 * (a.stacks 9).length +
        10 * (ProgramEncoding.encodeRecords left).length +
        10 * (ProgramEncoding.encodeRecords right).length + 9,
      Eval reverseQueries n a (queriesPrepared a left right) := by
  let a1 := cleared a 6
  let a2 := cleared a1 9
  let a3 := seeded a2
  let a4 := reversed a3 24 6 (ProgramEncoding.encodeRecords left.reverse)
  have t0 := clear_eval a 6
  have t1 := clear_eval a1 9
  have t2 := seedOutputs_eval a2
  obtain ⟨n3, hn3, t3⟩ := reverse_eval a3 24 6 (by decide) left []
    (by simp [a3, a2, a1, seeded, cleared, clearStacks, hl])
    (by simp [a3, a2, a1, seeded, cleared, clearStacks, ProgramEncoding.encodeRecords,
      Encoding.encodeList])
    (by simp [a3, a2, a1, seeded, cleared, clearStacks, h4])
  simp only [List.append_nil] at t3
  obtain ⟨n4, hn4, t4⟩ := reverse_eval a4 25 9 (by decide) right []
    (by simp [a4, a3, a2, a1, reversed, seeded, cleared, clearStacks, hr])
    (by simp [a4, a3, a2, a1, reversed, seeded, cleared, clearStacks,
      ProgramEncoding.encodeRecords, Encoding.encodeList])
    (by simp [a4, a3, a2, a1, reversed, seeded, cleared, clearStacks, h4])
  simp only [List.append_nil] at t4
  have he : reversed a4 25 9 (ProgramEncoding.encodeRecords right.reverse) =
      queriesPrepared a left right := by
    apply state_ext
    · funext j; fin_cases j <;> simp [a4, a3, a2, a1, reversed, seeded, cleared,
        readRegs, queriesPrepared]
    · funext j; fin_cases j <;> simp [a4, a3, a2, a1, reversed, seeded, cleared,
        clearStacks, queriesPrepared]
  rw [he] at t4
  refine ⟨_, ?_, t0.seq (t1.seq (t2.seq (t3.seq t4)))⟩
  have he9 : a1.stacks 9 = a.stacks 9 := by simp [a1, cleared, clearStacks]
  rw [he9]
  omega

end SubexponentialSAT.Subexp.PairPlanPreparation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectionTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Building the selector table at runtime

A fixed program scans framed unary seed indices, pairs each with the current
unary candidate-array position, and increments that position. The output is
the raw sequence `frame key ++ frame value`, with no outer list tags.
-/

namespace SubexponentialSAT.Subexp.SelectionTableProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem callback_eval (M n : ℕ) (source acc : List Bool) :
    Eval callback (callbackCost M n)
      (state false true false source (unary n).reverse (unary M) [] acc [])
      (state false true false source [] (unary (M + 1)) [] ((pairBytes n M).reverse ++ acc) []) := by
  let acc₁ := (Encoding.frame (unary n)).reverse ++ acc
  let acc₂ := (Encoding.frame (unary M)).reverse ++ acc₁
  have h₁ := emitToAcc_eval (unary n) source (unary M) acc false true false
  have h₂ := copy_eval (2 : Fin 6) 1 5 (by decide) (by decide) (by decide)
    (state false false false source [] (unary M) [] acc₁ []).regs
    (state false false false source [] (unary M) [] acc₁ []).stacks rfl
  have hcopy : (⟨readRegs (state false false false source [] (unary M) [] acc₁ []).regs 0 1 none,
      copyStacks 2 1 (state false false false source [] (unary M) [] acc₁ []).stacks⟩ : Data) =
      state false false false source (unary M) (unary M) [] acc₁ [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [state, copyStacks]
  rw [hcopy] at h₂
  have h₃ : Eval emitToAcc (11 * M + 14)
      (state false false false source (unary M) (unary M) [] acc₁ [])
      (state false false false source [] (unary M) [] acc₂ []) := by
    simpa [unary, acc₂] using emitToAcc_eval (unary M) source (unary M) acc₁ false false false
  have h₄ := advance_eval source (unary M) acc₂
  have ht := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp [ callbackCost, state, unary, pairBytes, acc₂, acc₁,
      List.reverse_append, List.append_assoc, List.replicate_succ]
  all_goals omega

/-- The actual framed-record loop preserves its growing counter and the raw
table accumulator in the exact input order. -/
theorem loop_eval (M : ℕ) (remaining : List ℕ) (suffix acc : List Bool) :
    Eval (RecordPrograms.loop ports callback) (loopCost M remaining)
      (RecordPrograms.afterTag ports (baseState M acc) (indexRecords remaining) suffix)
      (RecordPrograms.state ports
        (baseState (M + remaining.length) ((tableBytes M remaining).reverse ++ acc))
        false true false suffix []) := by
  induction remaining generalizing M acc with
  | nil =>
    simpa [loopCost, RecordPrograms.afterTag, indexRecords, tableBytes,
      ReadPlan.selectionTable, RecordPrograms.loop] using
      (Eval.while_false (test := ports.tag) (body := RecordPrograms.body ports callback)
        (a := RecordPrograms.state ports (baseState M acc) false true false suffix [])
        (by simp))
  | cons n remaining ih =>
    let tail := Encoding.encodeList id (indexRecords remaining) ++ suffix
    let nextAcc := (pairBytes n M).reverse ++ acc
    have hreader : Eval (RecordPrograms.reader ports) (6 * n + 4)
        (RecordPrograms.afterTag ports (baseState M acc) (indexRecords (n :: remaining)) suffix)
        (RecordPrograms.state ports (baseState M acc) false true false tail (unary n).reverse) := by
      simpa [RecordPrograms.afterTag, indexRecords, unary, tail] using
        RecordPrograms.reader_eval ports (baseState M acc) (unary n) tail [] true true false
    have hcallback : Eval callback (callbackCost M n)
        (RecordPrograms.state ports (baseState M acc) false true false tail (unary n).reverse)
        (RecordPrograms.state ports (baseState (M + 1) nextAcc) false true false tail []) := by
      simpa only [recordState_base] using callback_eval M n tail acc
    have hbranch : Eval
        (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
          (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
        (RecordPrograms.state ports (baseState (M + 1) nextAcc) false true false tail [])
        (RecordPrograms.afterTag ports (baseState (M + 1) nextAcc) (indexRecords remaining) suffix) := by
      apply Eval.ite_false (by simp)
      exact RecordPrograms.pop_list_eval ports (baseState (M + 1) nextAcc)
        (indexRecords remaining) suffix false true
    have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
    have hrest := ih (M + 1) nextAcc
    have hguard : (RecordPrograms.afterTag ports (baseState M acc)
        (indexRecords (n :: remaining)) suffix).regs ports.tag = true := by
      simp [RecordPrograms.afterTag, indexRecords]
    have ht := Eval.while_true hguard hbody hrest
    simpa [RecordPrograms.loop, RecordPrograms.body, loopCost, tableBytes_cons,
      List.length_cons, List.reverse_append, List.append_assoc, nextAcc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem command_eval (M : ℕ) (remaining : List ℕ) :
    Eval command (commandCost M remaining) (inputState M remaining) (outputState M remaining) := by
  have hinit := RecordPrograms.set_found_eval ports (baseState M []) false false false false
    (Encoding.encodeList id (indexRecords remaining) ++ []) []
  have hpop := RecordPrograms.pop_list_eval ports (baseState M []) (indexRecords remaining) [] false false
  have hloop := loop_eval M remaining [] []
  have hi := Eval.seq hinit (Eval.seq hpop hloop)
  let middle := state false true false [] [] (unary (M + remaining.length)) []
    (tableBytes M remaining).reverse []
  have hi' : Eval (RecordPrograms.iterate ports callback) (1 + (1 + loopCost M remaining))
      (inputState M remaining) middle := by
    simpa [RecordPrograms.iterate, inputState, ProgramEncoding.encodeRecords,
      recordState_base, middle] using hi
  have ht := transfer_eval (4 : Fin 6) 3 (by decide) middle.regs middle.stacks
  have hout : (⟨readRegs middle.regs 0 1 none, transferStacks 4 3 middle.stacks⟩ : Data) =
      outputState M remaining := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [middle, state, transferStacks]
  rw [hout] at ht
  simpa [command, commandCost, middle, state] using Eval.seq hi' ht

/-- Full halted trace of one fixed instruction table, with the table bytes
on output stack 3 and the incremented unary counter preserved on stack 2. -/
theorem program_trace (M : ℕ) (remaining : List ℕ) :
    Trace program (traceCost M remaining)
      ((inputState M remaining).withPC (some program.entry))
      ((outputState M remaining).withPC none) := by
  simpa [program, traceCost] using compiled_halt_trace (command_eval M remaining) 0 3

end SubexponentialSAT.Subexp.SelectionTableProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorPairProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Selecting and framing both read plans of a vertex pair

The two selector-map calls share a persistent table. Stack 6 initially holds
the left query records and stack 9 the right query records. Stack 11 is an
existing record accumulator. The result prepends one record whose payload is
`frame leftPlanBytes ++ frame rightPlanBytes`.
-/

namespace SubexponentialSAT.Subexp.SelectorPairProgram

open BitProgram StructuredCalls

theorem buildPayload_eval (regs : Fin 8 → Bool) (table left right acc : List Bool) :
    ∃ regs', Eval buildPayload (5 * left.length + 8 * right.length + 13)
      (state regs [] table right [] left.reverse acc)
      (state regs' [] table (payload left right) [] [] acc) := by
  let a := state regs [] table right [] left.reverse acc
  let b : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks 8 9 a.stacks⟩
  let c := TupleProgram.pushedState 8 0 false b
  let d := TupleProgram.escapedState rightPorts c
  let e := TupleProgram.pushedState 8 0 false d
  let f := TupleProgram.escapedState leftPorts e
  have h1 := TupleProgram.transfer_eval (8 : Fin 12) 9 (0 : Fin 8) 1
    (by decide) (by decide) a
  have h2 := TupleProgram.pushConst_eval (8 : Fin 12) (0 : Fin 8) false b
  have h3 := TupleProgram.escape_eval_state rightPorts c
  have h4 := TupleProgram.pushConst_eval (8 : Fin 12) (0 : Fin 8) false d
  have h5 := TupleProgram.escape_eval_state leftPorts e
  have hf : f = state f.regs [] table (payload left right) [] [] acc := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext k
      fin_cases k <;>
        simp [ e, d, c, b, a, state, leftPorts, rightPorts,
          StackRoutines.transferStacks,
          payload, TupleProgram.frame_eq_escaped, List.append_assoc]
  refine ⟨f.regs, ?_⟩
  rw [← hf]
  convert h1.seq (h2.seq (h3.seq (h4.seq h5))) using 1 ;
    simp [ e, d, c, b, a, state, leftPorts, rightPorts,
      StackRoutines.transferStacks ] ; omega

theorem emitPayload_eval (regs : Fin 8 → Bool) (table bits acc : List Bool) :
    ∃ regs', Eval emitPayload (8 * bits.length + 10)
      (state regs [] table bits [] [] acc)
      (state regs' [] table [] [] [] (TupleProgram.prependRecord bits acc)) := by
  let a := state regs [] table bits [] [] acc
  let b : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks 8 10 a.stacks⟩
  let c := TupleProgram.pushedState 11 0 false b
  let d := TupleProgram.escapedState outputPorts c
  let e := TupleProgram.pushedState 11 0 true d
  have h1 := TupleProgram.transfer_eval (8 : Fin 12) 10 (0 : Fin 8) 1
    (by decide) (by decide) a
  have h2 := TupleProgram.pushConst_eval (11 : Fin 12) (0 : Fin 8) false b
  have h3 := TupleProgram.escape_eval_state outputPorts c
  have h4 := TupleProgram.pushConst_eval (11 : Fin 12) (0 : Fin 8) true d
  have he : e = state e.regs [] table [] [] [] (TupleProgram.prependRecord bits acc) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp [ d, c, b, a, state, outputPorts, StackRoutines.transferStacks, TupleProgram.prependRecord,
          TupleProgram.frame_eq_escaped, List.append_assoc]
  refine ⟨e.regs, ?_⟩
  rw [← he]
  convert h1.seq (h2.seq (h3.seq h4)) using 1 ;
    simp [ c, b, a, state, outputPorts, StackRoutines.transferStacks
      ] ; omega

theorem framePair_eval (regs : Fin 8 → Bool) (table left right acc : List Bool) :
    ∃ regs', Eval framePair (frameCost left right)
      (state regs [] table right [] left.reverse acc)
      (state regs' [] table [] [] [] (TupleProgram.prependRecord (payload left right) acc)) := by
  obtain ⟨r1, h1⟩ := buildPayload_eval regs table left right acc
  obtain ⟨r2, h2⟩ := emitPayload_eval r1 table (payload left right) acc
  refine ⟨r2, ?_⟩
  convert h1.seq h2 using 1 ; simp [ frameCost] ; omega

/-- Polynomial in the actual table and two query encodings, including the
copies and both levels of output escaping. -/
theorem cost_bound (records : List (List Bool × List Bool))
    (left right : List (List Bool)) :
    cost records left right ≤
      1100 * ((SelectorProgram.rawRecords records).length + 1) *
        ((ProgramEncoding.encodeRecords left).length +
          (ProgramEncoding.encodeRecords right).length + 1) := by
  have hl := SelectorMapProgram.budget_bound records left
  have hr := SelectorMapProgram.budget_bound records right
  have hpl := planBytes_length_le records left
  have hpr := planBytes_length_le records right
  simp only [cost, frameCost, payload, List.length_append, Encoding.length_frame]
  nlinarith [Nat.zero_le ((SelectorProgram.rawRecords records).length *
    (ProgramEncoding.encodeRecords left).length),
    Nat.zero_le ((SelectorProgram.rawRecords records).length *
      (ProgramEncoding.encodeRecords right).length)]

end SubexponentialSAT.Subexp.SelectorPairProgram

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

def copied (a : Data) (src dst : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

def cleared (a : Data) (src : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

def moved (a : Data) (src dst : Fin 34) : Data := cleared (copied a src dst) src

theorem copy_eval (a : Data) (src dst : Fin 34) (hsd : src ≠ dst)
    (hs4 : src ≠ 4) (h4d : (4 : Fin 34) ≠ dst) (h4 : a.stacks 4 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 4 (0 : Fin 16) 1 hsd hs4 h4d (by decide) a h4

theorem clear_eval (a : Data) (src : Fin 34) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  TupleProgram.clear_eval src (0 : Fin 16) 1 a

theorem move_eval (a : Data) (src dst : Fin 34) (hsd : src ≠ dst)
    (hs4 : src ≠ 4) (h4d : (4 : Fin 34) ≠ dst) (h4 : a.stacks 4 = []) :
    Eval (move src dst) (9 * (a.stacks src).length + 8) a (moved a src dst) := by
  have h := (copy_eval a src dst hsd hs4 h4d h4).seq (clear_eval (copied a src dst) src)
  convert h using 1 <;> simp [moved, copied, copyStacks, hsd]
  omega

theorem resetList_eval (indices : List (Fin 16)) (a : Data) :
    StructuredProgram.Eval (resetList indices) indices.length a
      ⟨resetValues indices a.regs, a.stacks⟩ := by
  induction indices generalizing a with
  | nil => exact .skip a
  | cons i rest ih =>
    have h := (StructuredProgram.Eval.atom (.set i false) a).seq
      (ih ((StructuredProgram.Atom.set i false).eval a))
    simpa [resetList, resetValues, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC, execInstr, Nat.add_comm] using h

def innerReset (a : Data) : Data :=
  ⟨fun j => if j.val < 13 then false else a.regs j, a.stacks⟩

theorem resetInner_eval (a : Data) : Eval resetInner 13 a (innerReset a) := by
  have h := resetList_eval [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] a
  have hr : resetValues [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] a.regs =
      fun j => if j.val < 13 then false else a.regs j := by
    funext j
    fin_cases j <;> simp [resetValues]
  rw [hr] at h
  exact Eval.base h

def tableReset (a : Data) : Data :=
  ⟨fun j => if j.val < 3 then false else a.regs j, a.stacks⟩

theorem resetTable_eval (a : Data) : Eval resetTable 3 a (tableReset a) := by
  have h := resetList_eval [0, 1, 2] a
  have hr : resetValues [0, 1, 2] a.regs =
      fun j => if j.val < 3 then false else a.regs j := by
    funext j
    fin_cases j <;> simp [resetValues]
  rw [hr] at h
  exact Eval.base h

theorem resetAll_eval (a : Data) : Eval resetAll 16 a ⟨fun _ => false, a.stacks⟩ := by
  have h := resetList_eval (List.finRange 16) a
  have hr : resetValues (List.finRange 16) a.regs = fun _ => false := by
    funext j
    fin_cases j <;> rfl
  rw [hr] at h
  exact Eval.base h

def activeAfter (a : Data) (rf : Fin 10 → Bool) (seeds plan : List ℕ)
    (threshold : List Bool) : Data :=
  ⟨prefixRegs rf a.regs,
    Function.update (Function.update a.stacks 5 []) 11
      (ProgramEncoding.encodeRecords
        (ActivePlanProgram.indexRecords (ActivePlanProgram.active seeds plan threshold.length)))⟩

def tableAfter (a : Data) (M : ℕ) (remaining : List ℕ) : Data :=
  ⟨prefixRegs (fun _ : Fin 3 => false) a.regs,
    Function.update (Function.update (Function.update a.stacks 0 []) 2
      (SelectionTableProgram.unary (M + remaining.length))) 3
      (SelectionTableProgram.tableBytes M remaining)⟩

theorem tableCall_eval (a : Data) (M : ℕ) (remaining : List ℕ)
    (hr : ∀ i, a.regs (tableRegs i) = false)
    (hs : ∀ i, a.stacks (tableStacks i) = (SelectionTableProgram.inputState M remaining).stacks i) :
    Eval tableCall (SelectionTableProgram.traceCost M remaining) a (tableAfter a M remaining) := by
  have hin : embedState tableRegs tableStacks a (SelectionTableProgram.inputState M remaining) = a := by
    apply SelectorMapProgram.embed_eq _ _ tableRegs_injective tableStacks_injective
    · intro i
      have hi := hr i
      fin_cases i <;> simpa [SelectionTableProgram.inputState, SelectionTableProgram.baseState,
        SelectionTableProgram.ports, SelectionTableProgram.state, RecordPrograms.state] using hi
    · exact hs
    · intro j hj; rfl
    · intro j hj; rfl
  have hout : embedState tableRegs tableStacks a (SelectionTableProgram.outputState M remaining) =
      tableAfter a M remaining := by
    apply SelectorMapProgram.embed_eq _ _ tableRegs_injective tableStacks_injective
    · intro i
      fin_cases i <;> simp [tableAfter, prefixRegs, tableRegs, SelectionTableProgram.outputState,
        SelectionTableProgram.state]
    · intro i
      have hi := hs i
      fin_cases i <;>
        simp_all [tableAfter, tableStacks, SelectionTableProgram.inputState,
          SelectionTableProgram.outputState, SelectionTableProgram.baseState,
          SelectionTableProgram.state, SelectionTableProgram.ports, RecordPrograms.state]
    · intro j hj
      have hge : 3 ≤ j.val := by
        by_contra h
        have hlt : j.val < 3 := by omega
        exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
      simp [tableAfter, prefixRegs, Nat.not_lt.mpr hge]
    · intro j hj
      have h0 : j ≠ 0 := by intro h; subst j; exact hj ⟨0, rfl⟩
      have h2 : j ≠ 2 := by intro h; subst j; exact hj ⟨2, rfl⟩
      have h3 : j ≠ 3 := by intro h; subst j; exact hj ⟨3, rfl⟩
      simp [tableAfter, h0, h2, h3]
  have he := eval_call_lifted SelectionTableProgram.program tableRegs tableStacks a
    tableRegs_injective tableStacks_injective (SelectionTableProgram.program_trace M remaining)
  simpa only [tableCall, hin, hout] using he

def selectorAfter (a : Data) (rf : Fin 8 → Bool)
    (records : List (List Bool × List Bool)) (left right : List (List Bool)) : Data :=
  ⟨prefixRegs rf a.regs,
    Function.update (Function.update (Function.update a.stacks 6 []) 9 []) 29
      (TupleProgram.prependRecord
        (SelectorPairProgram.payload (SelectorPairProgram.planBytes records left)
          (SelectorPairProgram.planBytes records right)) (a.stacks 29))⟩

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Zero terms and append decomposition for the two concrete score producers. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.SqrtLog.PackingProgram

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceCount_headTerms_zero (alphabet : List (Word r Q))
    (heads : List (Fin Q × V × V)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (ω : ℕ → Word r Q) :
    (unweightedCounts ivar factor alphabet (heads.map Sum.inr) indices remaining ω).1 = 0 := by
  simp [unweightedCounts, commonNumerator, List.map_map, Function.comp_def,
    incidenceIndicator, scaledCount_zero]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem headCount_incidenceTerms_zero (alphabet : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (ω : ℕ → Word r Q) :
    (unweightedCounts ivar factor alphabet (pairs.map Sum.inl) indices remaining ω).2 = 0 := by
  simp [unweightedCounts, commonNumerator, List.map_map, Function.comp_def,
    headIndicator, scaledCount_zero]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem unweightedCounts_append (alphabet : List (Word r Q))
    (left right : List (ScoreTerm I V Q)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (ω : ℕ → Word r Q) :
    unweightedCounts ivar factor alphabet (left ++ right) indices remaining ω =
      ((unweightedCounts ivar factor alphabet left indices remaining ω).1 +
        (unweightedCounts ivar factor alphabet right indices remaining ω).1,
       (unweightedCounts ivar factor alphabet left indices remaining ω).2 +
        (unweightedCounts ivar factor alphabet right indices remaining ω).2) := by
  simp [unweightedCounts, commonNumerator_append]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem unweightedCounts_split (alphabet : List (Word r Q))
    (pairs : List (I × I)) (heads : List (Fin Q × V × V))
    (indices : List (V ⊕ E)) (remaining : List ℕ) (ω : ℕ → Word r Q) :
    unweightedCounts ivar factor alphabet (pairs.map Sum.inl ++ heads.map Sum.inr)
      indices remaining ω =
      ((unweightedCounts ivar factor alphabet (pairs.map Sum.inl) indices remaining ω).1,
       (unweightedCounts ivar factor alphabet (heads.map Sum.inr) indices remaining ω).2) := by
  rw [unweightedCounts_append, incidenceCount_headTerms_zero, headCount_incidenceTerms_zero]
  simp

end Scores
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramSize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input size, produced table size, and binary size of the exact numerator. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.LocalExpectation SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.SqrtLog.PackingProgram

section Sizes
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceCount_le (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (remaining : List ℕ) (hr : remaining.Nodup)
    (ω : ℕ → Word r Q) :
    (unweightedCounts ivar factor alphabet terms indices remaining ω).1 ≤
      terms.length * alphabet.length^4 := by
  have h := commonNumerator_bound alphabet terms
    (fun z η => incidenceIndicator ivar factor z (fun i => η (indexCode indices i)))
    (numberedScoreSupport ivar factor indices) 4 1 remaining
    (fun z => (active_length_le _ _ hr).trans (numberedScoreSupport_card_le ivar factor indices z))
    (by
      intro z η
      cases z with
      | inl p => rcases p with ⟨i,j⟩; simp only [incidenceIndicator]; split_ifs <;> omega
      | inr p => simp [incidenceIndicator]) ω
  simpa only [unweightedCounts, one_mul] using h

end Sizes
end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCombine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed two-call score combiner. Inputs are binary weights and canonical
false-unary collision counts. The only modified port is the score accumulator. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def combineBudget (d : CombineData) (ci ch : ℕ) :=
  scaleBudget (d.stacks 0) ci + scaleBudget (d.stacks 2) ch + 2

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramReplace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual dictionary replacement: delete all old matching keys, then prepend
one supplied coefficient. This is the storage phase of additive insertion;
the coefficient addition itself is a separately measured ring operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev ReplaceData := State 5 8

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-output physical calls in the assignment-input workspace. -/

namespace SubexponentialSAT.Subexp.AssignmentInputCall

open BitProgram StructuredCalls SubexpSetupStorage

noncomputable def callCost {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (q : Fin s) (dst : Fin 48)
    (a : Data) (out : State r s) (ticks : ℕ) : ℕ :=
  prepareCost 31 work inputs a + (ticks + finishCost work [(stack hs q, dst)]
    (embedState (register hr) (stack hs) (prepareState 31 work inputs a) out))

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end


