-- Prove2me | Definitions.Def_OAIQ081S062
-- name    : OAIQ081S062
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:51:11.465855+00:00
-- url     : https://prove2.me/theorems/55083bb4-6740-44af-8d54-241d2fb17a01
-- title:
--   Definitions bundle OAIQ081S062 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 98 declarations of OpenAI's Lean: 48 definitions and 50 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.MoveReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.headCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.headRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.moveCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.moveState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.moved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.overlap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.parked`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.unparked`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgram.inputLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Filter.decodeClause`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputCall.Clean`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputCall.Within`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateArrayProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateArrayProgram.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.cleared`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.copied`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.pairPayload`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.parseCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.parsed`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.queriesPrepared`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.reversed`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.seeded`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.transferred`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation.unionPrepared`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.ScoreBuilderProgram.finished`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.baseState`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.outputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.planBytes`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.mapRow`, `OAI.Algorithms.SubexponentialSAT.SubexpInputZip.Data` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLog_PackingHeadIncrementalSequential`, `SubexponentialSAT_SqrtLog_PackingHeadProgramAnd`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesRun`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramCounts`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyBasic`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyPrefix`, `SubexponentialSAT_SqrtLog_PackingProgramCounts`, `SubexponentialSAT_SqrtLog_PackingProgramScores`, `SubexponentialSAT_SqrtLog_PackingWeightProgramBasic`, `SubexponentialSAT_SubexpInputZip`, `SubexponentialSAT_SubexpNormalizeProgram`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_AssignmentInputCall`, `SubexponentialSAT_Subexp_AssignmentRecordViews`, `SubexponentialSAT_Subexp_CandidateArrayProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_CollisionTupleProgram`, `SubexponentialSAT_Subexp_LocalExpectation`, `SubexponentialSAT_Subexp_MinimumProgram`, `SubexponentialSAT_Subexp_PairPlanPreparation`, `SubexponentialSAT_Subexp_PairRuntimeBounds`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ReadPlan`, `SubexponentialSAT_Subexp_ScoreBuilderPorts`, `SubexponentialSAT_Subexp_SelectionTableProgram`, `SubexponentialSAT_Subexp_SelectorPairProgram`, `SubexponentialSAT_Subexp_UnaryCompare`, `SubexponentialSAT_Subexp_UnaryTally`, `SubexponentialSAT_Subexp_UniversalRowExecution`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S039`, `OAIQ081S040` and `OAIQ081S041` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S078`, `OAIQ081S079` and `OAIQ081S080`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S035
import Definitions.Def_OAIQ081S036
import Definitions.Def_OAIQ081S039
import Definitions.Def_OAIQ081S040
import Definitions.Def_OAIQ081S041

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

def decodeClause (bits : List Bool) : Option Clause := do
  let (fields, rest) ← ProgramEncoding.readRecords bits
  if rest.isEmpty then some fields else none


end Filter

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_LocalExpectation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform multi-color conditional expectation

All parameters remain visible. The local evaluator enumerates only each pair's
read support, and its total evaluation bound is a fixed polynomial in the
number of chunks and universal types. Natural completion counts also give a
common-denominator representation for the rational conditional scores.
-/

namespace SubexponentialSAT.Subexp.LocalExpectation

open SubexponentialSAT.LocalExpectation SubexponentialSAT.ConditionalExpectation
open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

/-- Exact numerator and denominator for an exhaustive local average. -/
theorem wordExpectation_eq_completionCount (alphabet : List W) (f : (I → W) → ℕ)
    (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun η => (f η : ℚ)) remaining ω =
      (completionCount alphabet f remaining ω : ℚ) /
        (alphabet.length : ℚ) ^ remaining.length := by
  induction remaining generalizing ω with
  | nil => simp [wordExpectation, completionCount]
  | cons i remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      unfold mean
      rw [sum_map_div, ← cast_sum_map]
      simp only [completionCount, List.length_cons, pow_succ, div_div, mul_comm]

theorem local_average_eq_scaledCount (alphabet : List W) (ha : alphabet ≠ [])
    (f : (I → W) → ℕ) (support : Finset I) (S : ℕ)
    (remaining : List I) (hS : (active support remaining).length ≤ S) (ω : I → W) :
    wordExpectation alphabet (fun η => (f η : ℚ)) (active support remaining) ω =
      (scaledCount alphabet f support S remaining ω : ℚ) / (alphabet.length : ℚ) ^ S := by
  rw [wordExpectation_eq_completionCount]
  have hq : (alphabet.length : ℚ) ≠ 0 := by
    exact_mod_cast (List.length_pos_iff.mpr ha).ne'
  have hp : (alphabet.length : ℚ) ^ S =
      (alphabet.length : ℚ) ^ (S - (active support remaining).length) *
        (alphabet.length : ℚ) ^ (active support remaining).length := by
    rw [← pow_add, Nat.sub_add_cancel hS]
  simp only [scaledCount, Nat.cast_mul, Nat.cast_pow, hp]
  exact (mul_div_mul_left _ _ (pow_ne_zero _ hq)).symm

end SubexponentialSAT.Subexp.LocalExpectation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScores
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Denominator-cleared scores for incidence/head conditional expectation. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section General
variable {A W J : Type*} [DecidableEq A]

theorem commonNumerator_bound (alphabet : List W) (terms : List J)
    (f : J → (A → W) → ℕ) (support : J → Finset A) (S B : ℕ)
    (remaining : List A) (hS : ∀ j, (active (support j) remaining).length ≤ S)
    (hf : ∀ j ω, f j ω ≤ B) (ω : A → W) :
    commonNumerator alphabet terms f support S remaining ω ≤
      terms.length * (B * alphabet.length ^ S) := by
  apply sum_map_le_bound
  intro j
  unfold scaledCount
  calc
    _ ≤ alphabet.length ^ (S - (active (support j) remaining).length) *
        (B * alphabet.length ^ (active (support j) remaining).length) :=
      Nat.mul_le_mul_left _ (completionCount_bound alphabet (f j) B (hf j) _ ω)
    _ = B * alphabet.length ^ S := by
      rw [← mul_assoc, mul_comm _ B, mul_assoc, ← pow_add, Nat.sub_add_cancel (hS j)]

end General

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Splitting all weighted completions into two unweighted integer counts. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section Linear
variable {A W J : Type*} [DecidableEq A]

theorem commonNumerator_linear (alphabet : List W) (terms : List J)
    (f g : J → (A → W) → ℕ) (support : J → Finset A) (S a b : ℕ)
    (remaining : List A) (ω : A → W) :
    commonNumerator alphabet terms (fun j η => a*f j η+b*g j η) support S remaining ω =
      a*commonNumerator alphabet terms f support S remaining ω +
      b*commonNumerator alphabet terms g support S remaining ω := by
  unfold commonNumerator
  have hlocal (j : J) : scaledCount alphabet (fun η => a*f j η+b*g j η)
      (support j) S remaining ω = a*scaledCount alphabet (f j) (support j) S remaining ω +
        b*scaledCount alphabet (g j) (support j) S remaining ω := by
    unfold scaledCount
    rw [completionCount_linear]
    ring
  simp_rw [hlocal]
  exact sum_linear _ _ _ _ _
end Linear

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ReadPlan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit local read plans

Read plans are lists of numeric positions in the explicit seed array. The
machine-facing data are fixed-width one-hot word records and unary indices.
Gathering them in head/slot order reproduces the actual type encoding.
-/

namespace SubexponentialSAT.Subexp.ReadPlan

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment
open SubexponentialSAT.Subexp.AssignmentEnumeration

section PartialAssignments

variable {W : Type*}

theorem completionPlan_valid (currentSize candidateSize : ℕ) (remaining plan : List ℕ)
    (hlen : remaining.length ≤ candidateSize) (hp : ∀ n ∈ plan, n < currentSize)
    (n : ℕ) (hn : n ∈ completionPlan currentSize remaining plan) :
    n < currentSize + candidateSize := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hn
  exact selected_valid currentSize candidateSize remaining hlen j (hp j hj)

end PartialAssignments

end SubexponentialSAT.Subexp.ReadPlan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalSequential
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Heads-first sequential ABI for the incremental physical head scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

section Sequential
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

omit [Fintype V] [Fintype E] in
theorem headPosition_injective (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) :
    Function.Injective (fun v : V => indexCode (headsFirstIndices vertices factors) (.inl v)) := by
  intro v u h
  apply idxOf_injective vertices hv
  simpa only [headsFirst_index_head vertices factors _ (hv _)] using h

omit [Fintype V] [Fintype E] in
theorem headPosition_exists (vertices : List V) (factors : List E)
    (hvn : vertices.Nodup) (p : ℕ) (hp : p < vertices.length) :
    ∃ v : V, indexCode (headsFirstIndices vertices factors) (.inl v) = p := by
  have hm : p ∈ vertices.map (indexCode vertices) := by
    rw [map_idxOf_eq_range vertices hvn]
    exact List.mem_range.mpr hp
  obtain ⟨v, hv, heq⟩ := List.mem_map.mp hm
  exact ⟨v, (headsFirst_index_head vertices factors v hv).trans heq⟩

end Sequential
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UnaryCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for exact conditional-score comparisons

The local conditional scores admit bounded natural numerators. Unary storage
is therefore already polynomial in the growing parameters. This module gives
an actual fixed finite instruction table comparing two stack lengths and
connects its measured execution to those conditional scores.
-/

namespace SubexponentialSAT.Subexp.UnaryCompare

open SubexponentialSAT.BitProgram

theorem nil_left (regs : Fin 4 → Bool) (ys : List Bool) :
    Trace program 5 (start regs [] ys)
      (finish (poppedRegs regs none ys.head?) [] ys.tail true) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, finish, poppedRegs, readRegs, pairStacks]
  funext i
  fin_cases i <;> simp [pairStacks]

theorem cons_nil (regs : Fin 4 → Bool) (x : Bool) (xs : List Bool) :
    Trace program 6 (start regs (x :: xs) [])
      (finish (poppedRegs regs (some x) none) xs [] false) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, finish, poppedRegs, readRegs, pairStacks]
  funext i
  fin_cases i <;> simp [pairStacks]

theorem cons_cons (regs : Fin 4 → Bool) (x y : Bool) (xs ys : List Bool) :
    Trace program 4 (start regs (x :: xs) (y :: ys))
      (start (poppedRegs regs (some x) (some y)) xs ys) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, poppedRegs, readRegs, pairStacks]
  funext i
  fin_cases i <;> simp [pairStacks]

/-- The cost counts actual instructions, including the halt instruction. -/
theorem runs (regs : Fin 4 → Bool) (xs ys : List Bool) :
    ∃ n ≤ 4 * min xs.length ys.length + 6, ∃ c : Cfg 4 2 7,
      Trace program n (start regs xs ys) c ∧
      c.pc = none ∧ c.regs 3 = decide (xs.length ≤ ys.length) := by
  induction xs generalizing regs ys with
  | nil =>
      refine ⟨5, by simp, finish (poppedRegs regs none ys.head?) [] ys.tail true,
        nil_left regs ys, rfl, ?_⟩
      simp [finish]
  | cons x xs ih =>
      cases ys with
      | nil =>
          refine ⟨6, by simp, finish (poppedRegs regs (some x) none) xs [] false,
            cons_nil regs x xs, rfl, ?_⟩
          simp [finish]
      | cons y ys =>
          obtain ⟨n, hn, c, ht, hpc, hout⟩ := ih (poppedRegs regs (some x) (some y)) ys
          refine ⟨4 + n, ?_, c, (cons_cons regs x y xs ys).trans ht, hpc, ?_⟩
          · simp only [List.length_cons]
            omega
          · simpa using hout

theorem step_length_le {c c' : Cfg 4 2 7}
    (h : step program c = some c') (i : Fin 2) :
    (c'.stacks i).length ≤ (c.stacks i).length := by
  cases hpc : c.pc with
  | none => simp [step, hpc] at h
  | some q =>
      have he : execInstr (program.code q) c = c' := by simpa [step, hpc] using h
      subst c'
      fin_cases q <;> simp [ execInstr]
      all_goals
        simp only [Function.update_apply]
        split <;> simp_all [List.length_tail]

theorem trace_length_le {c c' : Cfg 4 2 7} {n : ℕ}
    (h : Trace program n c c') (i : Fin 2) :
    (c'.stacks i).length ≤ (c.stacks i).length := by
  induction h with
  | refl => exact le_rfl
  | cons hs ht ih => exact ih.trans (step_length_le hs i)

end SubexponentialSAT.Subexp.UnaryCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UnaryTally
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program tallying padded collision leaves

Each successful leaf pushes one false bit. The resulting unary stack is the
exact common numerator used for conditional expectation. This file proves the
actual instruction trace from a prepared Boolean leaf list.
-/

namespace SubexponentialSAT.Subexp.UnaryTally

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.PaddedCompletion

theorem nil_trace (regs : Fin 2 → Bool) (out : List Bool) :
    Trace program 3 (start regs [] out) (finish out) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, finish, readRegs, pairStacks]
  all_goals (funext i; fin_cases i <;> simp)

theorem false_trace (regs : Fin 2 → Bool) (xs out : List Bool) :
    Trace program 3 (start regs (false :: xs) out) (start loopRegs xs out) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, readRegs, pairStacks ]
  constructor
  · funext i
    fin_cases i <;> simp [loopRegs]
  · funext i
    fin_cases i <;> simp [pairStacks]

theorem true_trace (regs : Fin 2 → Bool) (xs out : List Bool) :
    Trace program 5 (start regs (true :: xs) out) (start loopRegs xs (false :: out)) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, readRegs, pairStacks ]
  constructor
  · funext i
    fin_cases i <;> simp [loopRegs]
  · funext i
    fin_cases i <;> simp [pairStacks]

/-- Exact instruction trace, including the final halt. -/
theorem tally_trace (regs : Fin 2 → Bool) (xs out : List Bool) :
    Trace program (steps xs) (start regs xs out)
      (finish (List.replicate (trueCount xs) false ++ out)) := by
  induction xs generalizing regs out with
  | nil => simpa only [steps, trueCount_nil, List.replicate_zero, List.nil_append] using nil_trace regs out
  | cons b xs ih =>
      cases b with
      | false =>
          simpa only [steps, Bool.false_eq_true, ↓reduceIte, trueCount_false] using
            (false_trace regs xs out).trans (ih loopRegs out)
      | true =>
          simpa only [steps, ↓reduceIte, trueCount_true, replicate_append_bit] using
            (true_trace regs xs out).trans (ih loopRegs (false :: out))

end SubexponentialSAT.Subexp.UnaryTally

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramAnd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit zipper counts coordinate matches of one-hot words by counting
true bitwise intersections. It consumes one candidate copy and the same number
of table bits, preserving the remaining table suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramAnd
open SubexponentialSAT BitProgram StructuredCalls

theorem nil_trace (regs : Fin 5 → Bool) (ys out : List Bool) :
    Trace program 6 (start regs [] ys out) (finish ys out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply,step,program,execInstr,start,finish,readRegs,stackData]
  all_goals (funext i; fin_cases i <;> simp)

theorem cycle (regs : Fin 5 → Bool) (a b : Bool) (xs ys out : List Bool) :
    Trace program (weight a b) (start regs (a::xs) (b::ys) out)
      (start (nextRegs regs a b) xs ys (if a && b then false::out else out)) := by
  cases a <;> cases b <;> apply Computation.Trace.of_iterate <;>
    simp [weight,Function.iterate_succ_apply,step,program,execInstr,start,readRegs,stackData,nextRegs]
  all_goals
    first
    | (constructor <;> (funext i; fin_cases i <;> simp))
    | (funext i; fin_cases i <;> simp)

theorem trace (regs : Fin 5 → Bool) (xs ys tail out : List Bool) (hlen : xs.length=ys.length) :
    Trace program (steps xs ys) (start regs xs (ys++tail) out)
      (finish tail (List.replicate (jointTrue xs ys) false++out)) := by
  induction xs generalizing ys regs out with
  | nil =>
    have hy : ys=[] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simpa [steps,jointTrue] using nil_trace regs tail out
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have hh : xs.length=ys.length := by simpa using hlen
      have hc := cycle regs a b xs (ys++tail) out
      have hi := ih (nextRegs regs a b) ys (if a && b then false::out else out) hh
      have h := hc.trans hi
      cases a <;> cases b <;>
        simpa [steps,jointTrue,List.replicate_succ',List.append_assoc,Nat.add_comm] using h

end SubexponentialSAT.SqrtLog.PackingHeadProgramAnd

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

abbrev Data := State 2 10

abbrev state (regs : Fin 2 → Bool) (original candidate index width work indexWork : List Bool) : Data :=
  ⟨regs, ![original, candidate, index, width, [], [], [], [], work, indexWork]⟩

theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

end SubexponentialSAT.Subexp.CandidateArrayProgram

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

theorem streamed_length (current : List Bool) (width : ℕ) (left right : List ℕ)
    (tuples : List (List Bool)) (stream : List Bool) :
    (streamed current width left right tuples stream).length = tuples.length + stream.length := by
  rw [streamed_eq_reverse_map]
  simp

theorem unread_false (records : List (List Bool)) :
    RecordPrograms.unread (fun _ => false) records [] = [] := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa only [RecordPrograms.unread, Bool.false_eq_true, ite_false] using ih

end SubexponentialSAT.Subexp.CollisionTupleProgram

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

theorem unread_false (records : List (List Bool)) :
    RecordPrograms.unread (fun _ => false) records [] = [] := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa only [RecordPrograms.unread, Bool.false_eq_true, ite_false] using ih

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem reverseEscape_core (bits out : List Bool) (v pr : Bool) :
    Trace reverseEscapeProgram (4 * bits.length + 3)
      (writerState (some 0) v pr true bits out)
      (writerState none false false true [] ((TupleProgram.escaped bits).reverse ++ out)) := by
  induction bits generalizing out v pr with
  | nil =>
      refine .cons (b := writerState (some 1) false false true [] out) ?_ ?_
      · simp [step,writerState,execInstr,readRegs]
        first | done | (funext i; fin_cases i <;> simp)
      refine .cons (b := writerState (some 4) false false true [] out) ?_ ?_
      · simp [step,writerState,execInstr]
      refine .cons ?_ (.refl _)
      simp [step,writerState,execInstr]
  | cons bit bits ih =>
      have cycle : Trace reverseEscapeProgram 4
          (writerState (some 0) v pr true (bit :: bits) out)
          (writerState (some 0) bit true true bits (bit :: true :: out)) := by
        refine .cons (b := writerState (some 1) bit true true bits out) ?_ ?_
        · simp [step,writerState,execInstr,readRegs]
          first | done | (funext i; fin_cases i <;> simp)
        refine .cons (b := writerState (some 2) bit true true bits out) ?_ ?_
        · simp [step,writerState,execInstr]
        refine .cons (b := writerState (some 3) bit true true bits (true :: out)) ?_ ?_
        · simp [step,writerState,execInstr]
        refine .cons ?_ (.refl _)
        simp [step,writerState,execInstr]
      have h := cycle.trans (ih (bit :: true :: out) bit true)
      convert h using 1 <;>
        simp [TupleProgram.escaped_cons,List.reverse_cons,List.append_assoc] ; omega

theorem reverseEscape_trace (bits out : List Bool) (v pr tag : Bool) :
    Trace reverseEscapeProgram (4 * bits.length + 4)
      (writerState (some reverseEscapeProgram.entry) v pr tag bits out)
      (writerState none false false true [] ((TupleProgram.escaped bits).reverse ++ out)) := by
  have first : step reverseEscapeProgram
      (writerState (some reverseEscapeProgram.entry) v pr tag bits out) =
      some (writerState (some 0) v pr true bits out) := by
    simp [step,writerState,execInstr]
    first | done | (funext i; fin_cases i <;> simp)
  simpa only [Nat.add_assoc] using SubexponentialSAT.Computation.Trace.cons first (reverseEscape_core bits out v pr)

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

theorem unread_false (records : List (List Bool)) :
    RecordPrograms.unread (fun _ => false) records [] = [] := by
  induction records with
  | nil => rfl
  | cons b bs ih => simpa only [RecordPrograms.unread,Bool.false_eq_true,ite_false] using ih

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

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

theorem powerRows_width (alphabet rows : List (List Bool)) (n L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    ∀ row ∈ TupleProgram.powerRows alphabet n rows, row.length ≤ L + n * W := by
  induction n generalizing rows L with
  | zero => simpa only [TupleProgram.powerRows, Nat.zero_mul, Nat.add_zero] using hr
  | succ n ih =>
    have h := ih (TupleProgram.cartesianOutput rows alphabet) (L + W)
      (cartesian_width rows alphabet L W hr ha)
    simpa only [TupleProgram.powerRows, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

end SubexponentialSAT.Subexp.PairRuntimeBounds

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

def FilterEffect {r s : ℕ} (output : Fin s) (keep : List Bool → Bool)
    (bits : List Bool) (before after : StructuredProgram.State r s) : Prop :=
  after.stacks output =
    if keep bits then true :: (Encoding.frame bits ++ before.stacks output)
    else before.stacks output

end SubexponentialSAT.SubexpNormalizeProgram

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

theorem encoded_reverse_length (records : List (List Bool)) :
    (Encoding.encodeList id records.reverse).length = (Encoding.encodeList id records).length := by
  have ha := ProgramEncoding.encodeRecords_length records.reverse
  have hb := ProgramEncoding.encodeRecords_length records
  change (ProgramEncoding.encodeRecords records.reverse).length =
    (ProgramEncoding.encodeRecords records).length
  rw [ha, hb]
  simp

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

abbrev Data := StructuredProgram.State 16 34

theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

def transferred (a : Data) (src dst : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, transferStacks src dst a.stacks⟩

theorem transfer_eval (a : Data) (src dst : Fin 34) (hne : src ≠ dst) :
    Eval (transfer src dst) (3 * (a.stacks src).length + 3) a (transferred a src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (transferProgram_trace src dst (0 : Fin 16) 1 hne (by decide) a.regs a.stacks) 3 rfl rfl
  simpa [transfer, transferred, transferResult, transferProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using h

def cleared (a : Data) (src : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

def copied (a : Data) (src dst : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

theorem copy_eval (a : Data) (src dst : Fin 34) (hsd : src ≠ dst)
    (hs1 : src ≠ 1) (h1d : (1 : Fin 34) ≠ dst) (ht : a.stacks 1 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace src dst (1 : Fin 34) (0 : Fin 16) 1 hsd hs1 h1d
      (by decide) a.regs a.stacks ht) 7 rfl rfl
  simpa [copy, copied, copyResult, copyProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using h

def pairPayload (left right : List (List Bool)) : List Bool :=
  Encoding.frame (ProgramEncoding.encodeRecords left) ++
    Encoding.frame (ProgramEncoding.encodeRecords right)

def parsed (a : Data) (left right : List (List Bool)) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update (Function.update (Function.update
      (Function.update a.stacks 21 []) 22 []) 23 []) 24 (ProgramEncoding.encodeRecords left))
      25 (ProgramEncoding.encodeRecords right)⟩

def parseCost (left right : List (List Bool)) : ℕ :=
  3 * (pairPayload left right).length +
    9 * ((ProgramEncoding.encodeRecords left).length + (ProgramEncoding.encodeRecords right).length) + 17

def reversed (a : Data) (src dst : Fin 34) (out : List Bool) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 true) 2 false,
    Function.update (Function.update a.stacks src []) dst out⟩

def unionPrepared (a : Data) (left right : List (List Bool)) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 true) 2 false,
    Function.update a.stacks 6 (ProgramEncoding.encodeRecords (left.reverse ++ right))⟩

def seeded (a : Data) : Data :=
  ⟨Function.update a.regs 0 false,
    Function.update (Function.update a.stacks 6 (false :: a.stacks 6)) 9 (false :: a.stacks 9)⟩

theorem seedOutputs_eval (a : Data) : Eval seedOutputs 3 a (seeded a) := by
  have t0 := StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 false) a
  have t1 := StructuredProgram.Eval.atom (StructuredProgram.Atom.push 6 0)
    ((StructuredProgram.Atom.set 0 false).eval a)
  have t2 := StructuredProgram.Eval.atom (StructuredProgram.Atom.push 9 0)
    ((StructuredProgram.Atom.push 6 0).eval ((StructuredProgram.Atom.set 0 false).eval a))
  simpa [seedOutputs, seeded, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
    Eval.base (t0.seq (t1.seq t2))

def queriesPrepared (a : Data) (left right : List (List Bool)) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 true) 2 false,
    Function.update (Function.update (Function.update (Function.update a.stacks
      6 (ProgramEncoding.encodeRecords left.reverse))
      9 (ProgramEncoding.encodeRecords right.reverse)) 24 []) 25 []⟩

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

abbrev Data := State 3 6

def state (value present found : Bool)
    (source payload counter output acc scratch : List Bool) : Data :=
  ⟨![value, present, found], ![source, payload, counter, output, acc, scratch]⟩

theorem transfer_eval (src dst : Fin 6) (hne : src ≠ dst)
    (regs : Fin 3 → Bool) (stk : Stacks (Fin 6)) :
    Eval (.call (transferProgram src dst (0 : Fin 3) 1)) (3 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 0 1 none, transferStacks src dst stk⟩ := by
  apply Eval.call
  have ht := halt_after_trace _
    (transferProgram_trace src dst (0 : Fin 3) 1 hne (by decide) regs stk) 3 rfl rfl
  simpa [StructuredProgram.State.withPC, transferResult, transferProgram, Nat.add_assoc] using ht

theorem copy_eval (src dst tmp : Fin 6) (hsd : src ≠ dst)
    (hst : src ≠ tmp) (htd : tmp ≠ dst) (regs : Fin 3 → Bool) (stk : Stacks (Fin 6))
    (htmp : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp (0 : Fin 3) 1)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs 0 1 none, copyStacks src dst stk⟩ := by
  apply Eval.call
  have ht := halt_after_trace _
    (copyProgram_trace src dst tmp (0 : Fin 3) 1 hsd hst htd (by decide) regs stk htmp) 7 rfl rfl
  simpa [StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using ht

theorem pop_tag_eval (bits source counter acc : List Bool) (f : Bool) :
    Eval (RecordPrograms.atom (.pop 3 0 1)) 1
      (state true false f source [] counter (true :: Encoding.frame bits) acc [])
      (state true true f source [] counter (Encoding.frame bits) acc []) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (3 : Fin 6) (0 : Fin 3) 1)
    (state true false f source [] counter (true :: Encoding.frame bits) acc []) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem atom_eval_to (op : StructuredProgram.Atom 3 6) (a b : Data)
    (h : op.eval a = b) : Eval (RecordPrograms.atom op) 1 a b := by
  rw [← h]
  exact .base (.atom op a)

theorem tableBytes_eq_rawRecords (M : ℕ) (remaining : List ℕ) :
    tableBytes M remaining =
      SelectorProgram.rawRecords (SelectorProgram.selectionEntries M remaining) := by
  simp [tableBytes, SelectorProgram.rawRecords, SelectorProgram.selectionEntries,
    SelectorProgram.encodeEntries, List.flatMap_map, pairBytes, unary,
    SelectorProgram.unaryIndex ]

abbrev baseState (M : ℕ) (acc : List Bool) : Data :=
  state false false false [] [] (unary M) [] acc []

abbrev outputState (M : ℕ) (remaining : List ℕ) : Data :=
  state false false false [] [] (unary (M + remaining.length)) (tableBytes M remaining) [] []

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

abbrev Data := State 8 12

def state (regs : Fin 8 → Bool) (queries table output right saved acc : List Bool) : Data :=
  ⟨regs, ![[], [], [], [], [], [], queries, table, output, right, saved, acc]⟩

def planBytes (records : List (List Bool × List Bool)) (queries : List (List Bool)) : List Bool :=
  ProgramEncoding.encodeRecords (SelectorMapProgram.mappedRecords records queries)

theorem planBytes_selection (currentSize : ℕ) (remaining plan : List ℕ) :
    planBytes (SelectorProgram.selectionEntries currentSize remaining)
      (plan.reverse.map SelectorProgram.unaryIndex) =
    ProgramEncoding.encodeRecords (plan.map (fun n => SelectorProgram.unaryIndex
      (ReadPlan.selectPosition currentSize remaining n))) := by
  rw [planBytes, SelectorMapProgram.mappedRecords_selection]

end SubexponentialSAT.Subexp.SelectorPairProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MinimumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program selecting the first minimum unary score

The input is a framed list of prepared unary scores. Scores are represented
by list lengths. The program returns the selected zero-based index in unary.
All control, registers, and stack ports are fixed independently of the input.
-/

namespace SubexponentialSAT.Subexp.MinimumProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.StackRoutines

theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

end SubexponentialSAT.Subexp.MinimumProgram

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

abbrev Data := State 16 48

def finished (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update (Function.update (Function.update d.stacks
      0 (d.stacks 41)) 40 []) 41 []) 42 []⟩

end SubexponentialSAT.Subexp.ScoreBuilderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Zero terms and append decomposition for the two concrete score producers. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.SqrtLog.PackingProgram

section General
variable {A W J : Type*} [DecidableEq A]

theorem scaledCount_zero (alphabet : List W) (support : Finset A) (S : ℕ)
    (remaining : List A) (ω : A → W) :
    scaledCount alphabet (fun _ => 0) support S remaining ω = 0 := by
  simp [scaledCount, completionCount_zero]

theorem commonNumerator_append (alphabet : List W) (left right : List J)
    (f : J → (A → W) → ℕ) (support : J → Finset A) (S : ℕ)
    (remaining : List A) (ω : A → W) :
    commonNumerator alphabet (left ++ right) f support S remaining ω =
      commonNumerator alphabet left f support S remaining ω +
      commonNumerator alphabet right f support S remaining ω := by
  simp [commonNumerator]
end General

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

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

abbrev Data := State 16 48

def moved (d : Data) (src dst : Fin 48) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst (d.stacks src)⟩

def moveState : List (Fin 48 × Fin 48) → Data → Data
  | [], d => d
  | (src,dst)::rest, d => moveState rest (moved d src dst)

def moveCost : List (Fin 48 × Fin 48) → Data → ℕ
  | [], _ => 0
  | (src,dst)::rest, d => 6*(d.stacks src).length+6 + moveCost rest (moved d src dst)

def MoveReady : List (Fin 48 × Fin 48) → Data → Prop
  | [], _ => True
  | (src,dst)::rest,d => src ≠ dst ∧ src ≠ 16 ∧ (16 : Fin 48) ≠ dst ∧
      d.stacks dst = [] ∧ d.stacks 16 = [] ∧ MoveReady rest (moved d src dst)

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid parking of four runtime integer parameters around the incidence scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def parked (d : Data) : Data := moveState metadata d
def unparked (d : Data) : Data := moveState (metadata.map Prod.swap) d

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact correspondence between the physical gated prefix and prior heads. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp

def headRows {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) : List (List Bool) :=
  if fixed.length < heads then fixed.reverse.map ReadPlan.encodeWord else []

def overlap {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) (candidate : Word r Q) : ℕ :=
  PackingHeadProgramPrefix.score (ReadPlan.encodeWord candidate) (headRows heads fixed)

def headCount {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) : ℕ :=
  if fixed.length < heads then fixed.length else 0

theorem encodedWords_length {r Q : ℕ} (ws : List (Word r Q)) :
    (ws.map ReadPlan.encodeWord).flatten.length=ws.length*ReadPlan.wordWidth r Q := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp [List.flatten_cons,ih,Nat.add_mul,Nat.add_comm]

theorem headRows_length {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) :
    (headRows heads fixed).length=headCount heads fixed := by
  unfold headRows headCount
  split <;> simp

theorem headRows_width {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q))
    (row : List Bool) (h : row ∈ headRows heads fixed) : row.length=ReadPlan.wordWidth r Q := by
  unfold headRows at h
  split at h
  · obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
    exact ReadPlan.encodeWord_length w
  · simp at h

theorem headCount_le {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q)) :
    headCount heads fixed ≤ fixed.length := by
  unfold headCount
  split <;> omega

theorem take_headRows {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q))
    (suffix : List Bool) :
    ((fixed.reverse.map ReadPlan.encodeWord).flatten ++ suffix).take
      (headCount heads fixed*ReadPlan.wordWidth r Q) = (headRows heads fixed).flatten := by
  unfold headCount headRows
  split
  · exact List.take_left' (by simpa using encodedWords_length fixed.reverse)
  · simp

theorem overlap_cases {r Q : ℕ} (heads : ℕ) (fixed : List (Word r Q))
    (candidate : Word r Q) : overlap heads fixed candidate =
      if fixed.length < heads then PackingHeadProgramPrefix.score (ReadPlan.encodeWord candidate)
        (fixed.reverse.map ReadPlan.encodeWord) else 0 := by
  unfold overlap headRows
  split <;> simp [PackingHeadProgramPrefix.score]

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

abbrev Data := State 8 13

def inputLength (d : Data) : ℕ :=
  (d.stacks 0).length + (d.stacks 1).length + (d.stacks 2).length + (d.stacks 3).length

end SubexponentialSAT.SqrtLog.PackingWeightProgram

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

abbrev Data := State 8 8

abbrev state (regs : Fin 8 → Bool)
    (row input left right pair acc output tmp : List Bool) : Data :=
  ⟨regs, ![row, input, left, right, pair, acc, output, tmp]⟩

abbrev ready (regs : Fin 8 → Bool) (row input acc output : List Bool) : Data :=
  state regs row input [] [] [] acc output []

def afterWriter (d : Data) (bits : List Bool) : Data :=
  ⟨finishedRegs d.regs, Function.update (Function.update d.stacks 7 []) 4
    (true :: (Encoding.frame bits ++ d.stacks 4))⟩

theorem popPair_eval (regs : Fin 8 → Bool)
    (row input left right pair acc output tmp : List Bool) :
    Eval popPair 1 (state regs row input left right (true :: pair) acc output tmp)
      (state (readRegs regs 0 1 (some true)) row input left right pair acc output tmp) := by
  have h := StructuredProgram.Eval.atom (.pop (4 : Fin 8) (0 : Fin 8) 1)
    (state regs row input left right (true :: pair) acc output tmp)
  have hs : Function.update (![row,input,left,right,true::pair,acc,output,tmp] : Fin 8 → List Bool)
      4 pair = ![row,input,left,right,pair,acc,output,tmp] := by
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  apply Eval.base
  simpa [popPair, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, state, hs] using h

end SubexponentialSAT.SubexpInputZip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete scope-membership subroutine for incidence-plan preparation.
The reversed scope record occupies stack 8 and the reversed query stack 2.
Stacks 0,1,3,4 are empty work ports; all remaining stacks are framed.
-/
namespace SubexponentialSAT.SubexpScopeMembershipProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 10 10

def restrict (d : Data) : ExecCNFSubset.Data := ⟨d.regs, d.stacks ∘ stackMap⟩

theorem embed_restrict (d : Data) : embedState id stackMap d (restrict d) = d := by
  apply embedState_eq_of_ports id stackMap d d (restrict d)
    Function.injective_id stackMap_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; rfl
  · intros; rfl

def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 8 0 d.stacks⟩

def cleared (i : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks i []⟩

end SubexponentialSAT.SubexpScopeMembershipProgram

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

def Clean (a : Data) : Prop := (∀ j ∈ work, a.stacks j = []) ∧ a.stacks 31 = []

/-- A uniform bound on the contents of each physical stack. -/
def Within {r s : ℕ} (a : State r s) (B : ℕ) : Prop :=
  ∀ j, (a.stacks j).length ≤ B

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentRecordViews
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

open BitProgram StructuredCalls TupleProgram

abbrev Data := State 3 3

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word pushWord operator popTag emitOperator countOne drain )

def mapRow {A B : Type*} (f : A → B) (a : Row A) : Row B :=
  ⟨f a.delta, a.terms.map (mapTerm f)⟩

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end


