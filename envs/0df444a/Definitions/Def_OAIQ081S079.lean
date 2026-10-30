-- Prove2me | Definitions.Def_OAIQ081S079
-- name    : OAIQ081S079
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:01:30.150179+00:00
-- url     : https://prove2.me/theorems/fd37d477-2558-43db-bb6f-dd0a69dd94a3
-- title:
--   Definitions bundle OAIQ081S079 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 87 declarations of OpenAI's Lean: 32 definitions and 55 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental.priorOverlap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.projectInner`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.copied`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.inputStateThreshold`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.invariant`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.outputStateThreshold`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram.sourceBudget`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.baseState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.callbackCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.clearState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.copyState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.effect`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.fixedCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.invariant`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.sourceBudget`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.CollisionTupleProgram.transferState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.fieldRead`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.copiedDepth`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.fieldRead`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.invariant`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.resetInnerAfter`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.transferred`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.cost`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_PackingHeadIncremental`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyBasic`, `SubexponentialSAT_SqrtLog_PackingWeightProgramBasic`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter`, `SubexponentialSAT_SubexpInputZip`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_CandidateArrayProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_PairPlanPreparation`, `SubexponentialSAT_Subexp_PairRuntimeBounds`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ScoreBuilderPorts`, `SubexponentialSAT_Subexp_SelectionTableProgram`, `SubexponentialSAT_Subexp_SelectorPairProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S056`, `OAIQ081S060`, `OAIQ081S061`, `OAIQ081S062` and `OAIQ081S063` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S097`, `OAIQ081S098` and `OAIQ081S099`; the proofs of `OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram.command_eval` and `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S053
import Definitions.Def_OAIQ081S054
import Definitions.Def_OAIQ081S056
import Definitions.Def_OAIQ081S060
import Definitions.Def_OAIQ081S061
import Definitions.Def_OAIQ081S062
import Definitions.Def_OAIQ081S063

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

namespace Filter

@[simp] theorem decodeClause_clauseCode (C : Clause) : decodeClause (clauseCode C) = some C := by
  change (do
    let (fields, rest) ← ProgramEncoding.readRecords (ProgramEncoding.encodeRecords C)
    if rest.isEmpty then some fields else none) = some C
  simp


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncremental
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact candidate-dependent part of the head conditional score. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open scoped BigOperators

variable {r Q : ℕ}

def priorOverlap {V : Type*} [Fintype V] (position : V → ℕ)
    (remaining : List ℕ) (key : ℕ) (ω : ℕ → Word r Q) (z : Word r Q) : ℕ :=
  ∑ t : Fin Q, ∑ v : V,
    if position v = key ∨ position v ∈ remaining then 0
    else if z t = ω (position v) t then 1 else 0

end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateArrayProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A temporary candidate assignment with fixed control

The current assignment, candidate word, processed-position counter, and width
are preserved. The program copies the assignment and replaces precisely the
processed word in that copy. No restore of the original assignment is needed.
-/

namespace SubexponentialSAT.Subexp.CandidateArrayProgram

open BitProgram StructuredCalls StackRoutines

theorem embed_replace_eq (frame target : Data) (inner : State 2 8)
    (hr : ∀ i, target.regs i = inner.regs i)
    (hs : ∀ i, target.stacks (replacePorts i) = inner.stacks i)
    (hf : ∀ j, (¬ ∃ i, replacePorts i = j) → target.stacks j = frame.stacks j) :
    embedState id replacePorts frame inner = target := by
  apply state_ext
  · funext j
    exact (show (embedState id replacePorts frame inner).regs j = inner.regs j by
      simpa only [id_eq] using
        embedState_register id replacePorts frame inner Function.injective_id j).trans (hr j).symm
  · funext j
    by_cases hj : ∃ i, replacePorts i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_stack id replacePorts frame inner replacePorts_injective i).trans (hs i).symm
    · exact (embedState_stack_frame id replacePorts frame inner j hj).trans (hf j hj).symm

theorem copy_array_eval (regs : Fin 2 → Bool)
    (original candidate index width : List Bool) :
    Eval (.call (copyProgram 0 8 4 (0 : Fin 2) 1)) (7 * original.length + 5)
      (state regs original candidate index width [] [])
      (state (readRegs regs 0 1 none) original candidate index width original []) := by
  have h := TupleProgram.copy_eval (0 : Fin 10) 8 4 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (state regs original candidate index width [] []) (by rfl)
  have he : (⟨readRegs (state regs original candidate index width [] []).regs 0 1 none,
      copyStacks 0 8 (state regs original candidate index width [] []).stacks⟩ : Data) =
      state (readRegs regs 0 1 none) original candidate index width original [] := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;> simp [ copyStacks]
  rw [he] at h
  simpa [state] using h

theorem copy_index_eval (regs : Fin 2 → Bool)
    (original candidate index width work : List Bool) :
    Eval (.call (copyProgram 2 9 4 (0 : Fin 2) 1)) (7 * index.length + 5)
      (state regs original candidate index width work [])
      (state (readRegs regs 0 1 none) original candidate index width work index) := by
  have h := TupleProgram.copy_eval (2 : Fin 10) 9 4 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (state regs original candidate index width work []) (by rfl)
  have he : (⟨readRegs (state regs original candidate index width work []).regs 0 1 none,
      copyStacks 2 9 (state regs original candidate index width work []).stacks⟩ : Data) =
      state (readRegs regs 0 1 none) original candidate index width work index := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;> simp [ copyStacks]
  rw [he] at h
  simpa [state] using h

theorem replace_eval (regs : Fin 2 → Bool) (original : List Bool)
    (before : List (List Bool)) (old candidate rest index width : List Bool)
    (hi : index.length = before.length)
    (hrows : ∀ row ∈ before, row.length = width.length)
    (ho : old.length = width.length) (hc : candidate.length = width.length) :
    Eval replace (before.length * (14 * width.length + 10) + 20 * width.length + 21)
      (state regs original candidate index width (before.flatten ++ (old ++ rest)) index)
      (state (readRegs regs 0 1 none) original candidate index width
        (before.flatten ++ (candidate ++ rest)) []) := by
  let inner : State 2 8 := ⟨regs,
    ![before.flatten ++ (old ++ rest), candidate, index, width, [], [], [], []]⟩
  let base := state regs original candidate index width (before.flatten ++ (old ++ rest)) index
  have ht := ArrayUpdatePrograms.replaceProgram_trace (0 : Fin 2) 1 (by decide)
    before old candidate rest width index regs inner.stacks
    rfl rfl rfl rfl hi hrows ho hc rfl rfl rfl rfl
  change Trace (ArrayUpdatePrograms.replaceProgram (0 : Fin 2) 1) _
    (inner.withPC (some (ArrayUpdatePrograms.replaceProgram (0 : Fin 2) 1).entry))
    ((⟨readRegs regs 0 1 none,
      ArrayUpdatePrograms.replaceStacks before candidate rest inner.stacks⟩ : State 2 8).withPC none) at ht
  have he := eval_call_lifted (ArrayUpdatePrograms.replaceProgram (0 : Fin 2) 1)
    id replacePorts base Function.injective_id replacePorts_injective ht
  have hin : embedState id replacePorts base inner = base := by
    apply embed_replace_eq
    · intro j; rfl
    · intro j; fin_cases j <;> rfl
    · intro j hj; rfl
  have hout : embedState id replacePorts base
      (⟨readRegs regs 0 1 none,
        ArrayUpdatePrograms.replaceStacks before candidate rest inner.stacks⟩ : State 2 8) =
      state (readRegs regs 0 1 none) original candidate index width
        (before.flatten ++ (candidate ++ rest)) [] := by
    apply embed_replace_eq
    · intro j; rfl
    · intro j; fin_cases j <;> simp [replacePorts, inner, ArrayUpdatePrograms.replaceStacks]
    · intro j hj
      fin_cases j <;> simp_all [replacePorts, base, inner, state, Fin.exists_fin_succ]
  simpa only [hin, hout, replace, inner, base] using he

theorem command_eval (regs : Fin 2 → Bool) (before : List (List Bool))
    (old candidate rest index width : List Bool)
    (hi : index.length = before.length)
    (hrows : ∀ row ∈ before, row.length = width.length)
    (ho : old.length = width.length) (hc : candidate.length = width.length) :
    let original := before.flatten ++ (old ++ rest)
    Eval command (sourceCost original.length before.length width.length - 1)
      (state regs original candidate index width [] [])
      (state (readRegs regs 0 1 none) original candidate index width
        (before.flatten ++ (candidate ++ rest)) []) := by
  dsimp only
  have h := (copy_array_eval regs (before.flatten ++ (old ++ rest)) candidate index width).seq
    ((copy_index_eval (readRegs regs 0 1 none)
      (before.flatten ++ (old ++ rest)) candidate index width
      (before.flatten ++ (old ++ rest))).seq
        (replace_eval (readRegs (readRegs regs 0 1 none) 0 1 none)
          (before.flatten ++ (old ++ rest)) before old candidate rest index width hi hrows ho hc))
  convert h using 1 <;> simp [ sourceCost, hi, readRegs_reset] ; omega

theorem program_trace (regs : Fin 2 → Bool) (before : List (List Bool))
    (old candidate rest index width : List Bool)
    (hi : index.length = before.length)
    (hrows : ∀ row ∈ before, row.length = width.length)
    (ho : old.length = width.length) (hc : candidate.length = width.length) :
    let original := before.flatten ++ (old ++ rest)
    Trace program (sourceCost original.length before.length width.length)
      ((state regs original candidate index width [] []).withPC (some program.entry))
      ((state (readRegs regs 0 1 none) original candidate index width
        (before.flatten ++ (candidate ++ rest)) []).withPC none) := by
  dsimp only
  have ht := compiled_halt_trace
    (command_eval regs before old candidate rest index width hi hrows ho hc) 0 8
  have hp : 0 < sourceCost (before.flatten ++ (old ++ rest)).length before.length width.length := by
    simp [sourceCost]
  have htime : sourceCost (before.flatten ++ (old ++ rest)).length
        before.length width.length - 1 + 1 =
      sourceCost (before.flatten ++ (old ++ rest)).length before.length width.length :=
    Nat.sub_add_cancel hp
  rw [htime] at ht
  exact ht

end SubexponentialSAT.Subexp.CandidateArrayProgram

end OAI.Algorithms
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

theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

def sourceBudget (rows : List (List Bool)) (width : ℕ) (left right : List ℕ) : ℕ :=
  GatherProgram.traceCost rows width left + GatherProgram.traceCost rows width right +
    11 * (GatherProgram.gathered rows left).length +
    2 * (GatherProgram.gathered rows right).length + 20

theorem sourceBudget_eq_planBudget (rows : List (List Bool)) (width : ℕ)
    (left right : List ℕ) (hrows : ∀ row ∈ rows, row.length = width)
    (hleft : ∀ i ∈ left, i < rows.length) (hright : ∀ i ∈ right, i < rows.length) :
    sourceBudget rows width left right = planBudget width left right := by
  rw [sourceBudget, GatherProgram.traceCost, GatherProgram.traceCost,
    GatherProgram.iterator_budget_eq, GatherProgram.iterator_budget_eq,
    GatherProgram.gathered_length rows left width hrows hleft,
    GatherProgram.gathered_length rows right width hrows hright]
  unfold planBudget
  ring

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

abbrev Data := StructuredProgram.State 8 18

/-- Parser flags are false/true/false during a callback. All low registers are
scratch of the collision program. -/
def state (f : Frame) (table workLeft workRight stream payload : List Bool) : Data :=
  ⟨fun j => decide (j = 6), fun j =>
    if j = 0 then table else if j = 3 then f.width
    else if j = 8 then workLeft else if j = 10 then workRight else if j = 11 then stream
    else if j = 13 then f.current
    else if j = 14 then CollisionStreamProgram.planBytes f.left
    else if j = 15 then CollisionStreamProgram.planBytes f.right
    else if j = 16 then f.tail else if j = 17 then payload else []⟩

theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

def transferState (d : Data) (src dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

def copyState (d : Data) (src dst : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩

def clearState (d : Data) (src : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

theorem transfer_eval (d : Data) (src dst : Fin 18) (hsd : src ≠ dst) :
    Eval (.call (transferProgram src dst (0 : Fin 8) 1))
      (3 * (d.stacks src).length + 3) d (transferState d src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks) 3 rfl rfl
  simpa [transferState, StructuredProgram.State.withPC, transferResult, transferProgram,
    Nat.add_assoc] using h

theorem copy_eval (d : Data) (src dst : Fin 18)
    (hsd : src ≠ dst) (hs4 : src ≠ 4) (h4d : (4 : Fin 18) ≠ dst)
    (ht : d.stacks 4 = []) :
    Eval (.call (copyProgram src dst (4 : Fin 18) (0 : Fin 8) 1))
      (7 * (d.stacks src).length + 5) d (copyState d src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace src dst (4 : Fin 18) (0 : Fin 8) 1 hsd hs4 h4d
      (by decide) d.regs d.stacks ht) 7 rfl rfl
  simpa [copyState, StructuredProgram.State.withPC, copyResult, copyProgram,
    Nat.add_assoc] using h

theorem clear_eval (d : Data) (src : Fin 18) :
    Eval (.call (clearProgram src (0 : Fin 8) 1))
      (2 * (d.stacks src).length + 3) d (clearState d src) := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks) 2 rfl rfl
  simpa [clearState, StructuredProgram.State.withPC, clearResult, clearProgram,
    Nat.add_assoc] using h

def callbackCost (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuple : List Bool) : ℕ :=
  5 * tuple.length + 9 * current.length +
    7 * (CollisionStreamProgram.planBytes left).length +
    7 * (CollisionStreamProgram.planBytes right).length +
    CollisionStreamProgram.planBudget width left right + 21

def baseState (current : List Bool) (width : List Bool) (left right : List ℕ)
    (stream : List Bool) : Data :=
  state ⟨current, width, left, right, []⟩ [] [] [] stream []

def invariant (current : List Bool) (width : List Bool) (left right : List ℕ)
    (d : Data) : Prop := ∃ stream, d = baseState current width left right stream

def effect (current : List Bool) (width : ℕ) (left right : List ℕ)
    (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 11 = leafBit current width left right bits :: a.stacks 11

theorem parser_state_eq (current width : List Bool) (left right : List ℕ)
    (stream tail payload : List Bool) :
    RecordPrograms.state ports (baseState current width left right stream)
      false true false tail payload =
      state ⟨current, width, left, right, tail⟩ [] [] [] stream payload := by
  apply state_ext
  · funext j; fin_cases j <;> simp [RecordPrograms.state, ports, baseState, state]
  · funext j; fin_cases j <;> simp [RecordPrograms.state, ports, baseState, state]

def inputState (current width : List Bool) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) : Data :=
  RecordPrograms.state ports (baseState current width left right stream)
    false false false (ProgramEncoding.encodeRecords tuples) []

def sourceBudget (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) : ℕ :=
  4 + RecordPrograms.budget (callbackCost current width left right) tuples

def fixedCost (current : List Bool) (width : ℕ) (left right : List ℕ) : ℕ :=
  9 * current.length + 7 * (CollisionStreamProgram.planBytes left).length +
    7 * (CollisionStreamProgram.planBytes right).length +
    CollisionStreamProgram.planBudget width left right + 21

theorem sourceBudget_le_serialized (current : List Bool) (width : ℕ)
    (left right : List ℕ) (tuples : List (List Bool)) :
    sourceBudget current width left right tuples ≤
      (fixedCost current width left right + 22) *
        ((ProgramEncoding.encodeRecords tuples).length + 1) := by
  have h := RecordPrograms.program_budget_le_input (callbackCost current width left right)
    tuples 5 (fixedCost current width left right) (by
      intro bits _
      simp [callbackCost, fixedCost]
      omega)
  have hk : 5 + fixedCost current width left right + 17 =
      fixedCost current width left right + 22 := by omega
  simpa only [sourceBudget, hk] using h

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

theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

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

theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

def transferred (src dst : Fin 26) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

theorem transfer_eval (src dst : Fin 26) (hne : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred src dst d) := by
  apply Eval.call
  simpa [transfer, transferred, transferProgram, transferResult,
    StructuredProgram.State.withPC, Nat.add_assoc] using
    halt_after_trace _ (transferProgram_trace src dst (0 : Fin 13) 1 hne (by decide)
      d.regs d.stacks) 3 rfl rfl

def copiedDepth (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks (23 : Fin 26) 17 d.stacks⟩

theorem copyDepth_eval (d : Data) (htmp : d.stacks 24 = []) :
    Eval copyDepth (7 * (d.stacks 23).length + 5) d (copiedDepth d) := by
  apply Eval.call
  simpa [copyDepth, copiedDepth, copyProgram, copyResult,
    StructuredProgram.State.withPC, Nat.add_assoc] using
    halt_after_trace _ (copyProgram_trace (23 : Fin 26) 17 24 (0 : Fin 13) 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp) 7 rfl rfl

def fieldRead (bits tail : List Bool) (d : Data) : Data :=
  RecordPrograms.state fieldPorts d false true (d.regs 2) tail (bits.reverse ++ d.stacks 25)

theorem readField_eval (d : Data) (bits tail : List Bool)
    (hsrc : d.stacks 22 = Encoding.frame bits ++ tail) :
    Eval (RecordPrograms.reader fieldPorts) (6 * bits.length + 4) d (fieldRead bits tail d) := by
  have h := RecordPrograms.reader_eval fieldPorts d bits tail (d.stacks 25)
    (d.regs 0) (d.regs 1) (d.regs 2)
  have hd : RecordPrograms.state fieldPorts d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) (d.stacks 25) = d :=
    RecordPrograms.state_eq_self fieldPorts d _ _ _ _ _ rfl rfl rfl hsrc rfl
  simpa only [hd, fieldRead] using h

theorem resetList_eval (indices : List (Fin 13)) (d : Data) :
    StructuredProgram.Eval (resetList indices) indices.length d
      ⟨resetValues indices d.regs, d.stacks⟩ := by
  induction indices generalizing d with
  | nil => exact .skip d
  | cons i rest ih =>
    have h := (StructuredProgram.Eval.atom (.set i false) d).seq
      (ih ((StructuredProgram.Atom.set i false).eval d))
    simpa [resetList, resetValues, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC, execInstr, Nat.add_comm] using h

def resetInnerAfter (d : Data) : Data :=
  ⟨fun j => if j.val < 10 then false else d.regs j, d.stacks⟩

theorem resetInner_eval (d : Data) : Eval resetInner 10 d (resetInnerAfter d) := by
  have he := resetList_eval [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] d
  have hr : resetValues [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] d.regs =
      fun j => if j.val < 10 then false else d.regs j := by
    funext j
    fin_cases j <;> simp [resetValues]
  rw [hr] at he
  simpa [resetInner, resetInnerAfter] using Eval.base he

theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    change (embedState reg stack frame source).regs j = target.regs j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    change (embedState reg stack frame source).stacks j = target.stacks j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

def invariant (ctx : Context) (d : Data) : Prop :=
  ∃ stream : List Bool, d = baseState ctx stream

theorem tally_eval (d : Data) :
    Eval tally (UnaryTally.steps (d.stacks 11)) d (afterTally d) := by
  let a : StructuredProgram.State 2 2 :=
    ⟨d.regs ∘ tallyRegs, UnaryTally.pairStacks (d.stacks 11) (d.stacks 18)⟩
  let b : StructuredProgram.State 2 2 :=
    ⟨fun _ => false, UnaryTally.pairStacks []
      (List.replicate (PaddedCompletion.trueCount (d.stacks 11)) false ++ d.stacks 18)⟩
  have ha : embedState tallyRegs tallyPorts d a = d := by
    apply embedState_eq _ _ tallyRegs_injective tallyPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> simp [a, tallyPorts, UnaryTally.pairStacks]
    · intros; rfl
    · intros; rfl
  have hb : embedState tallyRegs tallyPorts d b = afterTally d := by
    apply embedState_eq _ _ tallyRegs_injective tallyPorts_injective
    · intro i; fin_cases i <;> simp [b, afterTally, tallyRegs, readRegs]
    · intro i; fin_cases i <;> simp [b, afterTally, tallyPorts, UnaryTally.pairStacks]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [tallyRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [tallyRegs] using h.symm⟩
      simp [afterTally, readRegs, h0, h1]
    · intro j hj
      have h11 : j ≠ 11 := fun h => hj ⟨0, by simpa [tallyPorts] using h.symm⟩
      have h18 : j ≠ 18 := fun h => hj ⟨1, by simpa [tallyPorts] using h.symm⟩
      simp [afterTally, h11, h18]
  have ht := UnaryTally.tally_trace (d.regs ∘ tallyRegs) (d.stacks 11) (d.stacks 18)
  have he := eval_call_lifted UnaryTally.program tallyRegs tallyPorts d
    tallyRegs_injective tallyPorts_injective (a := a) (b := b) ht
  simpa only [ha, hb, tally] using he

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

theorem reverseRecord_fold (records : List (List Bool)) (out : List Bool) :
    records.foldl (fun acc bits => reverseRecord bits acc) out =
      (TupleProgram.appendEncoded records []).reverse ++ out := by
  induction records generalizing out with
  | nil => simp [TupleProgram.appendEncoded]
  | cons bits rest ih =>
      rw [List.foldl_cons,ih]
      simp [reverseRecord,TupleProgram.appendEncoded,
        TupleProgram.prependRecord,List.reverse_append,List.reverse_cons,List.append_assoc]

theorem reverseRecord_finish (records : List (List Bool)) :
    (false :: (TupleProgram.appendEncoded records []).reverse).reverse =
      ProgramEncoding.encodeRecords records := by
  induction records with
  | nil => rfl
  | cons bits rest ih =>
      simpa [TupleProgram.appendEncoded,TupleProgram.prependRecord,
        ProgramEncoding.encodeRecords,Encoding.encodeList,List.reverse_append,
        List.reverse_cons,List.append_assoc] using congrArg (fun out => true :: (Encoding.frame bits ++ out)) ih

end SubexponentialSAT.Subexp.CandidateScoreProgram

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

def budget (rows candidates : List (List Bool)) : ℕ :=
  3+RecordPrograms.budget (callbackCost rows) candidates+
    (9*((TupleProgram.appendEncoded (scoreRecords rows candidates) []).length+1)+9)+1

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete stack transport for the combined packing score producer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

/-- Two actual transfers move a whole bit string without reversing it. -/
theorem move_eval (d : Data) (src dst tmp : Fin 48)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hd : d.stacks dst = []) (ht : d.stacks tmp = []) :
    Eval (move src dst tmp) (6*(d.stacks src).length+6) d (moved d src dst) := by
  let a := SubexponentialSAT.SubexpScanPrimitives.afterTransfer d src tmp 0 1
  have h₁ := SubexponentialSAT.SubexpScanPrimitives.transfer_eval d src tmp 0 1 hst (by decide)
  have h₂ := SubexponentialSAT.SubexpScanPrimitives.transfer_eval a tmp dst 0 1 htd (by decide)
  have ha : a.stacks tmp = (d.stacks src).reverse := by
    simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,transferStacks,ht]
  have he : SubexponentialSAT.SubexpScanPrimitives.afterTransfer a tmp dst 0 1 = moved d src dst := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,readRegs_reset]
    · funext j
      by_cases hjs : j=src
      · subst j
        simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,transferStacks,hsd,hst,Ne.symm hsd,Ne.symm htd]
      by_cases hjd : j=dst
      · subst j
        simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,transferStacks,Ne.symm hsd,Ne.symm htd,hd,ht]
      by_cases hjt : j=tmp
      · subst j
        simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,transferStacks,Ne.symm hsd,Ne.symm hst,htd,Ne.symm htd,hd,ht]
      · simp [a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,moved,transferStacks,hjs,hjd,hjt]
  rw [he] at h₂
  have h := h₁.seq h₂
  convert h using 1 ; simp [ha,List.length_reverse] ; omega

theorem moveMany_eval (moves : List (Fin 48 × Fin 48)) (d : Data) (h : MoveReady moves d) :
    Eval (moveMany moves) (moveCost moves d) d (moveState moves d) := by
  induction moves generalizing d with
  | nil => exact .base (.skip d)
  | cons p ps ih =>
    rcases p with ⟨src,dst⟩
    rcases h with ⟨hsd,hst,htd,hd,ht,hr⟩
    exact (move_eval d src dst 16 hsd hst htd hd ht).seq (ih _ hr)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed binary computation of the reciprocal-error packing coefficients.
Sources 0..3 hold n,s,M,r. Outputs 4,5 hold n²s² and 8M²r².
Ports 6,7 and 8..12 are temporary products and arithmetic scratch. -/
namespace SubexponentialSAT.SqrtLog.PackingWeightProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

def cleared (d : Data) (j : Fin 13) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks j []⟩

theorem clear_eval (d : Data) (j : Fin 13) :
    Eval (clear j) (2 * (d.stacks j).length + 3) d (cleared d j) :=
  .call _ (SubexponentialSAT.ListRegisterProgram.clear_run j 0 1 d.regs d.stacks)

def ready (d : Data) : Prop := ∀ j : Fin 13, 4 ≤ j.val → d.stacks j = []

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation and the finite total-variable table traversal. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

attribute [local simp] Fin.coe_ofNat_eq_mod

def projectInner (s : OuterStore) : Store := s ∘ innerPort

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete syntax routines for CNF normalization

This module begins the machine implementation of normalization with the
complement-query operation used in tautology testing. `negateProgram` is one
fixed finite instruction table. It scans a unary literal code in pairs and
emits the code with its polarity flipped. Unbounded data stays on the stacks.

The theorems count actual `BitProgram.step` transitions. Full formula
deduplication, tautology filtering, and absorption are separate obligations;
this routine is not presented as the completed normalization algorithm.
-/

namespace SubexponentialSAT.SubexpNormalizeProgram

open BitProgram
open ParserProgram (cfg)

/-! ## Actual record-filter output step

The predicate's result occupies register 2. The following fixed callback
consumes the reversed record on stack 3, prepends its framed representation to
stack 2 exactly when selected, and resets the iterator's flags. Its two other
stacks are preserved. Computing the selection bit is a separate operation.
-/

/-! ## A complete record-order reversal pass

Prepending accepted records reverses their order. This second, unconditional
pass restores the order required by `List.filter` and the executable
sparsifier. It reverses the records, never the bits within a record.
-/

/-! ## Exact-order contract for the full normalization filter

The selection callback in the following theorem is a fixed structured
program with measured executions. No procedure is manufactured from the
mathematical predicate. Once that callback is supplied, the theorem tracks
the output of the actual generic record iterator, including record order.
-/

theorem filterVisits_result {r s : ℕ} (output : Fin s) (keep : List Bool → Bool)
    {records : List (List Bool)} {before after : StructuredProgram.State r s}
    (h : RecordPrograms.Visits (fun _ => false) (FilterEffect output keep)
      records before after)
    (acc : List (List Bool)) (hacc : before.stacks output = Encoding.encodeList id acc) :
    after.stacks output = Encoding.encodeList id ((records.filter keep).reverse ++ acc) := by
  induction h generalizing acc with
  | nil base => simpa using hacc
  | hit ht _ => cases ht
  | @miss bits records before middle after _ he _ ih =>
      cases hkeep : keep bits with
      | false =>
          have hm : middle.stacks output = Encoding.encodeList id acc := by
            simpa [FilterEffect, hkeep, hacc] using he
          simpa [List.filter_cons, hkeep] using ih acc hm
      | true =>
          have hm : middle.stacks output = Encoding.encodeList id (bits :: acc) := by
            simpa [FilterEffect, hkeep, hacc, Encoding.encodeList] using he
          simpa [List.filter_cons, hkeep, List.reverse_cons, List.append_assoc] using
            ih (bits :: acc) hm

end SubexponentialSAT.SubexpNormalizeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpInputZip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical pairing of row and input-coordinate streams

Two ordinary framed lists are read on stacks 0 and 1. The fixed program builds
the exact paired-record stream consumed by `SubexpDotControl`, on stack 6.
No array lookup, pairing, or serialization is a semantic machine instruction.
-/

namespace SubexponentialSAT.SubexpInputZip

open BitProgram StructuredCalls SubexpScanPrimitives

theorem move_right (regs : Fin 8 → Bool)
    (row input left right pair acc output : List Bool) :
    Eval (move 3 7) (3 * right.length + 3)
      (state regs row input left right pair acc output [])
      (state (readRegs regs 0 1 none) row input left [] pair acc output right.reverse) := by
  have h := transfer_eval (state regs row input left right pair acc output []) 3 7 0 1
    (by decide) (by decide)
  have he : afterTransfer (state regs row input left right pair acc output []) 3 7 0 1 =
      state (readRegs regs 0 1 none) row input left [] pair acc output right.reverse := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks]
  change Eval (move 3 7) (3 * right.length + 3)
    (state regs row input left right pair acc output []) _ at h
  simpa only [he] using h

theorem move_left (regs : Fin 8 → Bool)
    (row input left right pair acc output : List Bool) :
    Eval (move 2 7) (3 * left.length + 3)
      (state regs row input left right pair acc output [])
      (state (readRegs regs 0 1 none) row input [] right pair acc output left.reverse) := by
  have h := transfer_eval (state regs row input left right pair acc output []) 2 7 0 1
    (by decide) (by decide)
  have he : afterTransfer (state regs row input left right pair acc output []) 2 7 0 1 =
      state (readRegs regs 0 1 none) row input [] right pair acc output left.reverse := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks]
  change Eval (move 2 7) (3 * left.length + 3)
    (state regs row input left right pair acc output []) _ at h
  simpa only [he] using h

theorem move_pair (regs : Fin 8 → Bool)
    (row input left right pair acc output : List Bool) :
    Eval (move 4 5) (3 * pair.length + 3)
      (state regs row input left right pair acc output [])
      (state (readRegs regs 0 1 none) row input left right [] (pair.reverse ++ acc) output []) := by
  have h := transfer_eval (state regs row input left right pair acc output []) 4 5 0 1
    (by decide) (by decide)
  have he : afterTransfer (state regs row input left right pair acc output []) 4 5 0 1 =
      state (readRegs regs 0 1 none) row input left right [] (pair.reverse ++ acc) output [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks]
  change Eval (move 4 5) (3 * pair.length + 3)
    (state regs row input left right pair acc output []) _ at h
  simpa only [he] using h

theorem tags_execute (regs : Fin 8 → Bool) (flag : Bool)
    (row input acc output : List Bool) :
    ∃ rf, Eval tags 2 (ready regs (flag :: row) (flag :: input) acc output)
      (ready rf row input acc output) ∧ rf 7 = flag := by
  let d := ready regs (flag :: row) (flag :: input) acc output
  obtain ⟨e, he, hs, hf⟩ := SubexpInputFrames.readTag_execute 0 d flag row rfl
  have heq : e = ready e.regs row (flag :: input) acc output := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [hs]; first | done | (first | done | (funext i; fin_cases i <;> rfl))
  let rf := readRegs e.regs 0 1 (some flag)
  have hp : Eval (.base (.atom (.pop 1 0 1))) 1
      (ready e.regs row (flag :: input) acc output) (ready rf row input acc output) := by
    have h := StructuredProgram.Eval.atom (.pop (1 : Fin 8) (0 : Fin 8) 1)
      (ready e.regs row (flag :: input) acc output)
    have ht : Function.update (![row,flag::input,[],[],[],acc,output,[]] : Fin 8 → List Bool)
        1 input = ![row,input,[],[],[],acc,output,[]] := by
      first | done | (first | done | (funext i; fin_cases i <;> rfl))
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, state, ready, rf, ht] using h
  refine ⟨rf, ?_, ?_⟩
  · rw [heq] at he
    exact Eval.seq he hp
  · simpa [rf, readRegs] using hf

theorem finish_execute (regs : Fin 8 → Bool) (row input acc output : List Bool) :
    ∃ rf, Eval finish (3 * acc.length + 8) (ready regs row input acc output)
      (ready rf row input [] (acc.reverse ++ [false] ++ output)) := by
  let r₁ := Function.update regs 0 false
  have h₁ : Eval (.base (.atom (.set 0 false))) 1 (ready regs row input acc output)
      (ready r₁ row input acc output) := by
    exact Eval.base (.atom _ _)
  have h₂ : Eval (.base (.atom (.push 5 0))) 1 (ready r₁ row input acc output)
      (ready r₁ row input (false :: acc) output) := by
    have h := StructuredProgram.Eval.atom (.push (5 : Fin 8) (0 : Fin 8))
      (ready r₁ row input acc output)
    have hs : Function.update (![row,input,[],[],[],acc,output,[]] : Fin 8 → List Bool)
        5 (false :: acc) = ![row,input,[],[],[],false::acc,output,[]] := by
      first | done | (first | done | (funext i; fin_cases i <;> rfl))
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, state, ready, r₁, hs] using h
  have h₃ := transfer_eval (ready r₁ row input (false :: acc) output) 5 6 0 1
    (by decide) (by decide)
  have he : afterTransfer (ready r₁ row input (false :: acc) output) 5 6 0 1 =
      ready (readRegs r₁ 0 1 none) row input [] (acc.reverse ++ [false] ++ output) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer,
        StackRoutines.transferStacks, List.reverse_cons, List.append_assoc]
  refine ⟨readRegs r₁ 0 1 none, ?_⟩
  have hlen : ((ready r₁ row input (false :: acc) output).stacks 5).length = acc.length + 1 := rfl
  rw [hlen, he] at h₃
  have h := Eval.seq h₁ (Eval.seq h₂ h₃)
  simpa only [finish, move,
    show 1 + (1 + (3 * (acc.length + 1) + 3)) = 3 * acc.length + 8 by omega] using h

end SubexponentialSAT.SubexpInputZip

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

abbrev state (regs : Regs) (source plan threshold acc query output : List Bool) : Data :=
  ⟨regs, ![[], [], query, [], [], source, plan, threshold, acc, [], [], output]⟩

abbrev copied (src dst : Fin 12) (d : Data) : Data :=
  ⟨reset d.regs, copyStacks src dst d.stacks⟩
abbrev cleared (src : Fin 12) (d : Data) : Data :=
  ⟨reset d.regs, clearStacks src d.stacks⟩

theorem copy_eval (src dst tmp : Fin 12) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (d.stacks src).length + 5) d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst tmp 0 1 hsd hst htd (by decide)
    d.regs d.stacks htmp)

theorem clear_eval (src : Fin 12) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

theorem unread_length_le (test : List Bool → Bool) (records : List (List Bool)) :
    (RecordPrograms.unread test records []).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.unread, Encoding.encodeList]
  | cons x xs ih =>
    simp only [RecordPrograms.unread]
    split
    · simp [Encoding.length_encodeList_cons]
    · exact ih.trans (by simp [Encoding.length_encodeList_cons])

/-- The threshold comparison uses fresh copies and preserves both its unary
inputs, the membership answer, and the outer parser registers. -/
theorem compare_eval (query source plan threshold acc output : List Bool) (regs : Regs) :
    ∃ n ≤ 30 * (threshold.length + query.length + 1), ∃ rf : Regs,
      rf 3 = decide (threshold.length ≤ query.length) ∧
      (∀ j : Fin 10, 4 ≤ j.val → rf j = regs j) ∧
      Eval compare n (state regs source plan threshold acc query.reverse output)
        (state rf source plan threshold acc query.reverse output) := by
  let start := state regs source plan threshold acc query.reverse output
  let first := copied 7 9 start
  let prepared := copied 2 10 first
  obtain ⟨n, hn, c, ht, hpc, hans⟩ :=
    UnaryCompare.runs (prepared.regs ∘ low4) threshold query.reverse
  let inner : State 4 2 := ⟨prepared.regs ∘ low4, UnaryCompare.pairStacks threshold query.reverse⟩
  let last : State 4 2 := ⟨c.regs, c.stacks⟩
  have hc : last.withPC none = c := by cases c; simp_all [last, StructuredProgram.State.withPC]
  have ht' : Trace UnaryCompare.program n
      (inner.withPC (some UnaryCompare.program.entry)) (last.withPC none) := by
    rw [hc]
    exact ht
  have hembed : embedState low4 compareStack prepared inner = prepared := by
    apply embedState_eq_of_ports _ _ _ _ _ low4_injective compareStack_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;>
        simp [inner, prepared, first, start, copyStacks, compareStack,
          UnaryCompare.pairStacks]
    · intros; rfl
  let scanned := embedState low4 compareStack prepared last
  have hscan : Eval compareCall n prepared scanned := by
    have h := eval_call_lifted UnaryCompare.program low4 compareStack prepared
      low4_injective compareStack_injective ht'
    simpa only [hembed, compareCall, scanned] using h
  have hreg3 : scanned.regs 3 = decide (threshold.length ≤ query.length) := by
    change scanned.regs (low4 3) = _
    rw [embedState_register _ _ _ _ low4_injective]
    simpa [last] using hans
  have hregs (j : Fin 10) (hj : 4 ≤ j.val) : scanned.regs j = regs j := by
    have hout : ¬ ∃ i, low4 i = j := by
      rintro ⟨i, h⟩
      have hv := congrArg Fin.val h
      change i.val = j.val at hv
      omega
    rw [embedState_register_frame _ _ _ _ j hout]
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simp [prepared, first, reset, start, readRegs, h0, h1]
  have hframe (j : Fin 12) (h9 : j ≠ 9) (h10 : j ≠ 10) :
      scanned.stacks j = start.stacks j := by
    have hout : ¬ ∃ i, compareStack i = j := by
      rintro ⟨i, h⟩
      fin_cases i <;> simp_all [compareStack]
    rw [embedState_stack_frame _ _ _ _ j hout]
    simp [prepared, first, copyStacks, h9, h10]
  have hlen9 : (scanned.stacks 9).length ≤ threshold.length := by
    have hh := UnaryCompare.trace_length_le ht 0
    change (scanned.stacks (compareStack 0)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStack_injective]
    simpa [last, UnaryCompare.start, UnaryCompare.pairStacks] using hh
  have hlen10 : (scanned.stacks 10).length ≤ query.length := by
    have hh := UnaryCompare.trace_length_le ht 1
    change (scanned.stacks (compareStack 1)).length ≤ _
    rw [embedState_stack _ _ _ _ compareStack_injective]
    simpa [last, UnaryCompare.start, UnaryCompare.pairStacks] using hh
  let finish := cleared 10 (cleared 9 scanned)
  have hfinish : finish = state finish.regs source plan threshold acc query.reverse output := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j
    all_goals simp [ clearStacks,
      hframe 0 (by decide) (by decide), hframe 1 (by decide) (by decide),
      hframe 2 (by decide) (by decide), hframe 3 (by decide) (by decide),
      hframe 4 (by decide) (by decide), hframe 5 (by decide) (by decide),
      hframe 6 (by decide) (by decide), hframe 7 (by decide) (by decide),
      hframe 8 (by decide) (by decide), hframe 11 (by decide) (by decide), start ]
  have h1 := copy_eval 7 9 4 start (by decide) (by decide) (by decide) rfl
  have h2 := copy_eval 2 10 4 first (by decide) (by decide) (by decide) rfl
  have hz9 := clear_eval 9 scanned
  have hz10 := clear_eval 10 (cleared 9 scanned)
  have hall := h1.seq (h2.seq (hscan.seq (hz9.seq hz10)))
  change Eval compare _ start finish at hall
  rw [hfinish] at hall
  refine ⟨_, ?_, finish.regs, ?_, ?_, hall⟩
  · simp only [List.length_reverse] at hn
    have hm := Nat.min_le_left threshold.length query.length
    simp [start, first, copyStacks, clearStacks]
    omega
  · simpa [finish, cleared, reset, readRegs] using hreg3
  · intro j hj
    have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
    have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
    simpa [finish, cleared, reset, readRegs, h0, h1] using hregs j hj

theorem recordState_state (regs : Regs) (v p f : Bool)
    (source plan threshold acc query output source' query' : List Bool) :
    RecordPrograms.state ports (state regs source plan threshold acc query output) v p f source' query' =
      state (outerFlags regs v p f) source' plan threshold acc query' output := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports ]

def invariant (records : List (List Bool)) (threshold : List Bool) (d : Data) : Prop :=
  ∃ regs source acc query, d = state regs source (Encoding.encodeList id records) threshold acc query []

theorem initAccumulator_eval (regs : Regs) (source plan threshold : List Bool) :
    Eval initAccumulator 2 (state regs source plan threshold [] [] [])
      (state (Function.update regs 0 false) source plan threshold [false] [] []) := by
  have h1 : Eval (RecordPrograms.atom (.set 0 false)) 1
      (state regs source plan threshold [] [] [])
      (state (Function.update regs 0 false) source plan threshold [] [] []) := .base (.atom _ _)
  have h2 : Eval (RecordPrograms.atom (.push 8 0)) 1
      (state (Function.update regs 0 false) source plan threshold [] [] [])
      (state (Function.update regs 0 false) source plan threshold [false] [] []) := by
    convert Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (8 : Fin 12) (0 : Fin 10))
      (state (Function.update regs 0 false) source plan threshold [] [] [])) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr ]
  exact h1.seq h2

theorem initializeOutput_eval (regs : Regs) (source plan threshold acc : List Bool) :
    Eval initializeOutput 2 (state regs source plan threshold acc [] [])
      (state (Function.update regs 0 false) source plan threshold acc [] [false]) := by
  have h1 : Eval (RecordPrograms.atom (.set 0 false)) 1
      (state regs source plan threshold acc [] [])
      (state (Function.update regs 0 false) source plan threshold acc [] []) := .base (.atom _ _)
  have h2 : Eval (RecordPrograms.atom (.push 11 0)) 1
      (state (Function.update regs 0 false) source plan threshold acc [] [])
      (state (Function.update regs 0 false) source plan threshold acc [] [false]) := by
    convert Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (11 : Fin 12) (0 : Fin 10))
      (state (Function.update regs 0 false) source plan threshold acc [] [])) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr ]
  exact h1.seq h2

/-- Raw counters are measured by length; their bit values are retained. -/
abbrev inputStateThreshold (regs : Regs) (seeds plan : List ℕ) (threshold : List Bool) : Data :=
  state regs (ProgramEncoding.encodeRecords (indexRecords seeds))
    (ProgramEncoding.encodeRecords (indexRecords plan)) threshold [] [] []

abbrev outputStateThreshold (regs : Regs) (seeds plan : List ℕ) (threshold : List Bool) : Data :=
  state regs [] (ProgramEncoding.encodeRecords (indexRecords plan)) threshold [] []
    (ProgramEncoding.encodeRecords (indexRecords (active seeds plan threshold.length)))

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPlanPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual parsing and record-order preparation of the two plans in a pair
payload. Registers 0, 1, and 2 are scratch; all other registers are framed. -/

namespace SubexponentialSAT.Subexp.PairPlanPreparation

open BitProgram StackRoutines StructuredCalls

theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

theorem clear_eval (a : Data) (src : Fin 34) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 16) 1 a.regs a.stacks) 2 rfl rfl
  simpa [clear, cleared, clearResult, clearProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using h

def fieldRead (a : Data) (bits tail : List Bool) : Data :=
  RecordPrograms.state fieldPorts a false true (a.regs 2) tail (bits.reverse ++ a.stacks 23)

theorem readField_eval (a : Data) (bits tail : List Bool)
    (hin : a.stacks 22 = Encoding.frame bits ++ tail) :
    Eval (RecordPrograms.reader fieldPorts) (6 * bits.length + 4) a (fieldRead a bits tail) := by
  have h := RecordPrograms.reader_eval fieldPorts a bits tail (a.stacks 23)
    (a.regs 0) (a.regs 1) (a.regs 2)
  have he : RecordPrograms.state fieldPorts a (a.regs 0) (a.regs 1) (a.regs 2)
      (Encoding.frame bits ++ tail) (a.stacks 23) = a :=
    RecordPrograms.state_eq_self fieldPorts a _ _ _ _ _ rfl rfl rfl hin rfl
  simpa only [he, fieldRead] using h

theorem parsePair_eval (a : Data) (left right : List (List Bool))
    (hin : a.stacks 21 = (pairPayload left right).reverse)
    (h22 : a.stacks 22 = []) (h23 : a.stacks 23 = [])
    (h24 : a.stacks 24 = []) (h25 : a.stacks 25 = []) :
    Eval parsePair (parseCost left right) a (parsed a left right) := by
  let l := ProgramEncoding.encodeRecords left
  let r := ProgramEncoding.encodeRecords right
  let a1 := transferred a 21 22
  let a2 := fieldRead a1 l (Encoding.frame r)
  let a3 := transferred a2 23 24
  let a4 := fieldRead a3 r []
  let a5 := transferred a4 23 25
  have t0 := transfer_eval a 21 22 (by decide)
  have t1 := readField_eval a1 l (Encoding.frame r)
    (by simp [a1, transferred, transferStacks, hin, h22, pairPayload, l, r])
  have t2 := transfer_eval a2 23 24 (by decide)
  have t3 := readField_eval a3 r []
    (by simp [a3, transferred, transferStacks, a2, fieldRead, RecordPrograms.state, fieldPorts])
  have t4 := transfer_eval a4 23 25 (by decide)
  have he : a5 = parsed a left right := by
    apply state_ext
    · funext j; fin_cases j <;> simp [a5, a4, a3, a2, a1, fieldRead, transferred,
        RecordPrograms.state, fieldPorts, readRegs, parsed]
    · funext j; fin_cases j <;> simp [a5, a4, a3, a2, a1, fieldRead, transferred,
        RecordPrograms.state, fieldPorts, transferStacks, parsed, h22, h23, h24, h25, l, r]
  have t := t0.seq (t1.seq (t2.seq (t3.seq t4)))
  change transferred a4 23 25 = parsed a left right at he
  rw [he] at t
  convert t using 1
  all_goals try with_reducible_and_instances rfl
  simp [a4, a3, a2, a1, fieldRead, transferred, RecordPrograms.state, fieldPorts,
    transferStacks, hin, h22, h23, h24, l, r, parseCost]
  ring

end SubexponentialSAT.Subexp.PairPlanPreparation

end OAI.Algorithms
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

theorem encoded_length_le (rows : List (List Bool)) (L : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ L) :
    (ProgramEncoding.encodeRecords rows).length ≤ 2 * rows.length * L + 2 * rows.length + 1 := by
  have hv := volume_le rows L h
  rw [ProgramEncoding.encodeRecords_length]
  change 2 * volume rows + 2 * rows.length + 1 ≤ _
  nlinarith

theorem encoded_generated_length_le (alphabet : List (List Bool)) (n W : ℕ)
    (hA : 1 ≤ alphabet.length) (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet n [[]])).length + 1 ≤
      (2 * n * W + 4) * alphabet.length ^ n := by
  have hw := powerRows_width alphabet [[]] n 0 W (by simp) ha
  have hv := volume_le (TupleProgram.powerRows alphabet n [[]]) (n * W) (by simpa using hw)
  rw [TupleProgram.generated_count] at hv
  have hk : 1 ≤ alphabet.length ^ n := one_le_pow₀ hA
  rw [ProgramEncoding.encodeRecords_length, TupleProgram.generated_count]
  change 2 * volume (TupleProgram.powerRows alphabet n [[]]) + 2 * alphabet.length ^ n + 1 + 1 ≤ _
  nlinarith

end SubexponentialSAT.Subexp.PairRuntimeBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ScoreBuilderPorts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The fixed global scorer stack layout

The preparation and candidate routines use the controller's 48 stacks through
explicit injective maps. The finalizer moves ordered score records to port 0
and clears the temporary selected-pair table, restoring the higher-stack
environment expected by the sequential controller.
-/

namespace SubexponentialSAT.Subexp.ScoreBuilderProgram

open BitProgram StructuredCalls StackRoutines

/-- A lifted actual subroutine that changes one local stack changes exactly
the corresponding caller stack. This proof does not execute an abstract map;
the premise is the concrete subroutine's instruction trace. -/
theorem call_lifted_update {r s S labels n : ℕ} (p : Program r s labels)
    (ports : Fin s → Fin S) (hinj : Function.Injective ports)
    (caller : State r S) (a b : State r s) (out : Fin s) (value : List Bool)
    (haRegs : a.regs = caller.regs)
    (haStacks : ∀ i, a.stacks i = caller.stacks (ports i))
    (hbStacks : b.stacks = Function.update a.stacks out value)
    (ht : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p id ports)) n caller
      ⟨b.regs, Function.update caller.stacks (ports out) value⟩ := by
  have hcall := eval_call_lifted p id ports caller Function.injective_id hinj ht
  have hstart : embedState id ports caller a = caller := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      exact (show (embedState id ports caller a).regs j = a.regs j by
        simpa only [id_eq] using embedState_register id ports caller a Function.injective_id j).trans
          (congrFun haRegs j)
    · funext j
      by_cases hj : ∃ i, ports i = j
      · obtain ⟨i, rfl⟩ := hj
        exact (embedState_stack id ports caller a hinj i).trans (haStacks i)
      · exact embedState_stack_frame id ports caller a j hj
  have hend : embedState id ports caller b =
      (⟨b.regs, Function.update caller.stacks (ports out) value⟩ : State r S) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      change (embedState id ports caller b).regs j = b.regs j
      exact embedState_register id ports caller b Function.injective_id j
    · funext j
      by_cases hj : ∃ i, ports i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [hinj.extend_apply, hbStacks]
        by_cases hi : i = out
        · subst i; simp
        · have hneq : ports i ≠ ports out := fun h => hi (hinj h)
          simp [hi, hneq, haStacks]
      · rw [Function.extend_apply' _ _ _ hj]
        have hneq : j ≠ ports out := fun h => hj ⟨out, h.symm⟩
        simp [hneq]
  simpa only [hstart, hend] using hcall

end SubexponentialSAT.Subexp.ScoreBuilderProgram

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

theorem embed_eq {r s R S : ℕ} (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (base target : State R S) (inner : State r s)
    (hreg : ∀ i, target.regs (reg i) = inner.regs i)
    (hstk : ∀ i, target.stacks (stk i) = inner.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = base.regs j)
    (hfs : ∀ j, (¬ ∃ i, stk i = j) → target.stacks j = base.stacks j) :
    embedState reg stk base inner = target := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_register reg stk base inner hr i).trans (hreg i).symm
    · exact (embedState_register_frame reg stk base inner j hj).trans (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stk i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_stack reg stk base inner hs i).trans (hstk i).symm
    · exact (embedState_stack_frame reg stk base inner j hj).trans (hfs j hj).symm

theorem advance_eval (source counter acc : List Bool) :
    Eval advance 4 (state false false false source [] counter [] acc [])
      (state false true false source [] (true :: counter) [] acc []) := by
  have h₁ : Eval (RecordPrograms.atom (.set 0 true)) 1
      (state false false false source [] counter [] acc [])
      (state true false false source [] counter [] acc []) := by
    apply atom_eval_to
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;> rfl
  have h₂ : Eval (RecordPrograms.atom (.push 2 0)) 1
      (state true false false source [] counter [] acc [])
      (state true false false source [] (true :: counter) [] acc []) := by
    apply atom_eval_to
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;> rfl
  have h₃ : Eval (RecordPrograms.atom (.set 0 false)) 1
      (state true false false source [] (true :: counter) [] acc [])
      (state false false false source [] (true :: counter) [] acc []) := by
    apply atom_eval_to
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;> rfl
  have h₄ : Eval (RecordPrograms.atom (.set 1 true)) 1
      (state false false false source [] (true :: counter) [] acc [])
      (state false true false source [] (true :: counter) [] acc []) := by
    apply atom_eval_to
    apply congrArg₂ StructuredProgram.State.mk <;> funext i <;> fin_cases i <;> rfl
  exact Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ h₄))

theorem recordState_base (M : ℕ) (acc source payload : List Bool) (v p f : Bool) :
    RecordPrograms.state ports (baseState M acc) v p f source payload =
      state v p f source payload (unary M) [] acc [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [ ports, baseState, state]
  · funext i; fin_cases i <;> simp [ ports, baseState, state]

abbrev inputState (M : ℕ) (remaining : List ℕ) : Data :=
  RecordPrograms.state ports (baseState M []) false false false
    (ProgramEncoding.encodeRecords (indexRecords remaining)) []

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

def cost (records : List (List Bool × List Bool)) (left right : List (List Bool)) : ℕ :=
  SelectorMapProgram.budget records left + SelectorMapProgram.budget records right +
    3 * (planBytes records left).length + 9 * (ProgramEncoding.encodeRecords right).length +
      11 + frameCost (planBytes records left) (planBytes records right) + 1

theorem planBytes_length_le (records : List (List Bool × List Bool))
    (queries : List (List Bool)) :
    (planBytes records queries).length ≤
      ((SelectorProgram.rawRecords records).length + 1) *
        (ProgramEncoding.encodeRecords queries).length := by
  have hsum : ((queries.map (SelectorMapProgram.selected records)).map List.length).sum ≤
      (queries.map List.length).sum + queries.length * (SelectorProgram.rawRecords records).length := by
    induction queries with
    | nil => simp
    | cons query queries ih =>
        have h := SelectorMapProgram.selected_length_le records query
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
  simp only [planBytes, SelectorMapProgram.mappedRecords, ProgramEncoding.encodeRecords_length,
    List.map_reverse, List.sum_reverse, List.length_reverse, List.length_map]
  nlinarith [Nat.zero_le ((SelectorProgram.rawRecords records).length *
    (queries.map List.length).sum)]

end SubexponentialSAT.Subexp.SelectorPairProgram

end OAI.Algorithms
end


