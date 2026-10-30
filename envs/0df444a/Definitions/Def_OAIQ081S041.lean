-- Prove2me | Definitions.Def_OAIQ081S041
-- name    : OAIQ081S041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:33:33.534735+00:00
-- url     : https://prove2.me/theorems/f9605274-5e6e-4197-b172-732d955817bf
-- title:
--   Definitions bundle OAIQ081S041 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 128 declarations of OpenAI's Lean: 50 definitions and 78 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramAnd.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramAnd.start`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.ArithmeticData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.afterSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.flag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.loopBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.pairBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.pairsBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.payload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.resultBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.scores`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.streamBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Streams.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Zip.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.arithmeticInputLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.arithmeticReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.scaleBudget`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.callbackCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.reset`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.sourceBound`, `OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram.traceBoundThreshold`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputCall.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.reverseRecord`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.writerState`, `OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram.poppedRegs`, `OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram.Context.Valid`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.commandCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.indexRecords`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.pairBytes`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.tableBytes`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram.traceCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.frameCost`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram.payload`, `OAI.Algorithms.SubexponentialSAT.Subexp.UnaryCompare.finish`, `OAI.Algorithms.SubexponentialSAT.Subexp.UnaryCompare.poppedRegs`, `OAI.Algorithms.SubexponentialSAT.Subexp.UnaryCompare.start`, `OAI.Algorithms.SubexponentialSAT.Subexp.UnaryTally.finish`, `OAI.Algorithms.SubexponentialSAT.Subexp.UnaryTally.start`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.mapFactor` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_PackingHeadIncrementalCounts`, `SubexponentialSAT_SqrtLog_PackingHeadProgramAnd`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates`, `SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesBounds`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix`, `SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramCounts`, `SubexponentialSAT_SqrtLog_PackingPrefixProgram`, `SubexponentialSAT_SqrtLog_PackingProgramArithmetic`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads`, `SubexponentialSAT_SqrtLog_PackingProgramCounts`, `SubexponentialSAT_SqrtLog_PackingProgramEmit`, `SubexponentialSAT_SqrtLog_PackingProgramOrdering`, `SubexponentialSAT_SqrtLog_PackingProgramScale`, `SubexponentialSAT_SqrtLog_PackingProgramScores`, `SubexponentialSAT_SqrtLog_PackingProgramStreamBounds`, `SubexponentialSAT_SqrtLog_PackingProgramStreamLoop`, `SubexponentialSAT_SqrtLog_PackingProgramStreams`, `SubexponentialSAT_SqrtLog_PackingProgramZip`, `SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic`, `SubexponentialSAT_SubexpDotControl`, `SubexponentialSAT_SubexpInputZip`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_Subexp_ActivePlanProgram`, `SubexponentialSAT_Subexp_AssignmentInputCall`, `SubexponentialSAT_Subexp_AssignmentInputState`, `SubexponentialSAT_Subexp_AssignmentRecordViews`, `SubexponentialSAT_Subexp_BasisTransposePlanProgram`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_CollisionGenerateProgram`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_MinimumProgram`, `SubexponentialSAT_Subexp_OneHotAlphabetProgram`, `SubexponentialSAT_Subexp_PairPreparationProgram`, `SubexponentialSAT_Subexp_PairRuntimeBounds`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_ReadPlan`, `SubexponentialSAT_Subexp_SelectionTableProgram`, `SubexponentialSAT_Subexp_SelectorIndices`, `SubexponentialSAT_Subexp_SelectorMapProgram`, `SubexponentialSAT_Subexp_SelectorPairProgram`, `SubexponentialSAT_Subexp_UnaryCompare`, `SubexponentialSAT_Subexp_UnaryTally`, `SubexponentialSAT_Subexp_UniversalRowExecution`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S005`, `OAIQ081S009`, `OAIQ081S012`, `OAIQ081S013`, `OAIQ081S014`, `OAIQ081S015`, `OAIQ081S018` and `OAIQ081S019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S062` and `OAIQ081S063`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S009
import Definitions.Def_OAIQ081S012
import Definitions.Def_OAIQ081S013
import Definitions.Def_OAIQ081S014
import Definitions.Def_OAIQ081S015
import Definitions.Def_OAIQ081S018
import Definitions.Def_OAIQ081S019

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScores
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
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

theorem completionCount_bound (alphabet : List W) (f : (A → W) → ℕ)
    (B : ℕ) (hf : ∀ ω, f ω ≤ B) (remaining : List A) (ω : A → W) :
    completionCount alphabet f remaining ω ≤ B * alphabet.length ^ remaining.length := by
  induction remaining generalizing ω with
  | nil => simpa [completionCount] using hf ω
  | cons i remaining ih =>
    simp only [completionCount, List.length_cons]
    calc
      _ ≤ alphabet.length * (B * alphabet.length ^ remaining.length) :=
        sum_map_le_bound alphabet _ _ (fun w => ih _)
      _ = _ := by rw [pow_succ]; ring

end General

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
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

theorem completionCount_linear (alphabet : List W) (f g : (A → W) → ℕ)
    (a b : ℕ) (remaining : List A) (ω : A → W) :
    completionCount alphabet (fun η => a*f η+b*g η) remaining ω =
      a*completionCount alphabet f remaining ω + b*completionCount alphabet g remaining ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
    simp only [completionCount]
    simp_rw [ih]
    exact sum_linear _ _ _ _ _

end Linear

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ReadPlan
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

open SubexponentialSAT.MulticolorTypes

section PartialAssignments

variable {W : Type*}

theorem selectionTable_lookup_default (currentSize : ℕ) (remaining : List ℕ) (n : ℕ) :
    ((selectionTable currentSize remaining).lookup n).getD n =
      selectPosition currentSize remaining n := by
  rw [selectionTable_lookup]
  unfold selectPosition
  split_ifs <;> rfl

end PartialAssignments

end SubexponentialSAT.Subexp.ReadPlan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite head sum is exactly the actual numbered completion numerator. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

theorem completionCount_zero {A W : Type*} [DecidableEq A]
    (alphabet : List W) (remaining : List A) (ω : A → W) :
    completionCount alphabet (fun _ => 0) remaining ω = 0 := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons a remaining ih => simp [completionCount, ih]

end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UnaryCompare
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

def start (regs : Fin 4 → Bool) (xs ys : List Bool) : Cfg 4 2 7 :=
  ⟨some 0, regs, pairStacks xs ys⟩

def poppedRegs (regs : Fin 4 → Bool) (x y : Option Bool) : Fin 4 → Bool :=
  readRegs (readRegs regs 0 1 x) 0 2 y

def finish (regs : Fin 4 → Bool) (xs ys : List Bool) (answer : Bool) : Cfg 4 2 7 :=
  ⟨none, Function.update regs 3 answer, pairStacks xs ys⟩

end SubexponentialSAT.Subexp.UnaryCompare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UnaryTally
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

def start (regs : Fin 2 → Bool) (xs out : List Bool) : Cfg 2 2 6 :=
  ⟨some 0, regs, pairStacks xs out⟩

def finish (out : List Bool) : Cfg 2 2 6 :=
  ⟨none, fun _ => false, pairStacks [] out⟩

theorem trueCount_nil : trueCount [] = 0 := rfl
theorem trueCount_false (xs : List Bool) : trueCount (false :: xs) = trueCount xs := rfl
theorem trueCount_true (xs : List Bool) : trueCount (true :: xs) = trueCount xs + 1 := rfl

theorem steps_eq (xs : List Bool) : steps xs = 3 * xs.length + 2 * trueCount xs + 3 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b <;> simp only [steps, trueCount_false, trueCount_true, List.length_cons, ih,
        Bool.false_eq_true, ↓reduceIte] <;> omega

theorem steps_le (xs : List Bool) : steps xs ≤ 5 * xs.length + 3 := by
  have h : trueCount xs ≤ xs.length := List.length_filter_le id xs
  rw [steps_eq]
  omega

end SubexponentialSAT.Subexp.UnaryTally

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramAnd
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

def start (regs : Fin 5 → Bool) (xs ys out : List Bool) : Cfg 5 3 11 :=
  ⟨some 0,regs,stackData xs ys out⟩

def finish (ys out : List Bool) : Cfg 5 3 11 :=
  ⟨none,fun _ => false,stackData [] ys out⟩

end SubexponentialSAT.SqrtLog.PackingHeadProgramAnd

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed counted loop over the existing flattened head prefix. Every
iteration copies the candidate and counts its true bitwise intersections with
one prefix word. No per-coordinate metadata or selected-pair stream is supplied. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem zipPorts_injective : Function.Injective zipPorts := by decide

end SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramPreserve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A source-preserving wrapper for the actual prefix scan. The only input
streams are one candidate, the flattened prior words, and their unary count. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve
open SubexponentialSAT BitProgram StructuredCalls StackRoutines
open scoped BigOperators

theorem ports_injective : Function.Injective ports := by decide

end SubexponentialSAT.SqrtLog.PackingHeadProgramPreserve

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionStreamProgram
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

theorem equalityPorts_injective : Function.Injective equalityPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [equalityPorts]

end SubexponentialSAT.Subexp.CollisionStreamProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionGenerateProgram
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

theorem generatorPorts_injective : Function.Injective generatorPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [generatorPorts]

theorem cartesian_schema (alphabet rows : List (List Bool)) (count : ℕ)
    (hrows : ∀ bits ∈ rows, TupleSchema alphabet count bits) :
    ∀ bits ∈ TupleProgram.cartesianOutput rows alphabet, TupleSchema alphabet (count + 1) bits := by
  intro bits hbits
  simp only [TupleProgram.cartesianOutput, List.mem_reverse, List.mem_flatMap, List.mem_map] at hbits
  obtain ⟨pre, hp, word, hw, rfl⟩ := hbits
  obtain ⟨items, hn, hf, hi⟩ := hrows pre hp
  refine ⟨items ++ [word], by simp [hn], by simp [hf], ?_⟩
  intro item hitem
  simp only [List.mem_append, List.mem_singleton] at hitem
  rcases hitem with hitem | rfl
  · exact hi item hitem
  · exact hw

theorem power_schema (alphabet rows : List (List Bool)) (count depth : ℕ)
    (hrows : ∀ bits ∈ rows, TupleSchema alphabet count bits) :
    ∀ bits ∈ TupleProgram.powerRows alphabet depth rows,
      TupleSchema alphabet (count + depth) bits := by
  induction depth generalizing rows count with
  | zero => simpa [TupleProgram.powerRows] using hrows
  | succ depth ih =>
    have h := ih (TupleProgram.cartesianOutput rows alphabet) (count + 1)
      (cartesian_schema alphabet rows count hrows)
    simpa [TupleProgram.powerRows, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Every emitted tuple consists of exactly depth original alphabet words,
even when distinct word tuples have identical concatenated payloads. -/
theorem generated_schema (alphabet : List (List Bool)) (depth : ℕ) :
    ∀ bits ∈ TupleProgram.powerRows alphabet depth [[]], TupleSchema alphabet depth bits := by
  have h := power_schema alphabet [[]] 0 depth (by
    intro bits hbits
    simp only [List.mem_singleton] at hbits
    subst bits
    exact ⟨[], rfl, rfl, by simp⟩)
  simpa using h

theorem generated_validPayload (current alphabet : List (List Bool)) (width depth : ℕ)
    (left right : List ℕ) (hc : ∀ row ∈ current, row.length = width)
    (ha : ∀ row ∈ alphabet, row.length = width)
    (hl : ∀ i ∈ left, i < current.length + depth)
    (hr : ∀ i ∈ right, i < current.length + depth) :
    ∀ bits ∈ TupleProgram.powerRows alphabet depth [[]],
      CollisionTupleProgram.validPayload current width left right bits := by
  intro bits hbits
  obtain ⟨rows, hn, hf, hm⟩ := generated_schema alphabet depth bits hbits
  refine ⟨rows, hf, ?_, ?_, ?_⟩
  · intro row hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · exact hc row hrow
    · exact ha row (hm row hrow)
  · simpa [hn] using hl
  · simpa [hn] using hr

end SubexponentialSAT.Subexp.CollisionGenerateProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreProgram
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

def Context.Valid (ctx : Context) : Prop :=
  (∀ row ∈ ctx.current, row.length = ctx.width.length) ∧
    (∀ row ∈ ctx.alphabet, row.length = ctx.width.length)

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
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

def writerState {l : ℕ} (pc : Option (Fin l)) (v pr tag : Bool)
    (input output : List Bool) : Cfg 3 2 l :=
  ⟨pc, ![v,pr,tag], ParserProgram.pair input output⟩

theorem lowRegisters_injective : Function.Injective lowRegisters := Fin.castAdd_injective _ _
theorem lowStacks_injective : Function.Injective lowStacks := Fin.castAdd_injective _ _

theorem writerRegisters_injective : Function.Injective writerRegisters := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [writerRegisters]
theorem writerStacks_injective : Function.Injective writerStacks := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [writerStacks]

def reverseRecord (bits out : List Bool) : List Bool :=
  (true :: Encoding.frame bits).reverse ++ out

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed serialization primitives for weighted candidate-score streams. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem reg_injective : Function.Injective reg := Fin.castAdd_injective _ _
theorem writerStack_injective : Function.Injective writerStack := by decide

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed producer of all incremental head scores from the candidate alphabet
and actual flattened prior-head table. No selected pair records are inputs. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines
open Subexp

theorem reg_injective : Function.Injective reg := Fin.castAdd_injective _ _
theorem low_injective : Function.Injective low := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadProgramCandidatesBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates
open SubexponentialSAT BitProgram StructuredCalls StackRoutines Subexp
open scoped BigOperators

theorem recordBudget_le (rows candidates : List (List Bool)) (W : ℕ)
    (hlen : ∀ candidate ∈ candidates,candidate.length=W) :
    RecordPrograms.budget (callbackCost rows) candidates ≤
      candidates.length*(rows.length*(25*W+20)+17*W+48) := by
  induction candidates with
  | nil => simp [RecordPrograms.budget]
  | cons candidate candidates ih =>
    have hc := score_le candidate rows
    have hl := hlen candidate (by simp)
    have hi := ih (by intro x hx; exact hlen x (by simp [hx]))
    simp only [RecordPrograms.budget,callbackCost,List.length_cons]
    rw [hl] at hc ⊢
    nlinarith

end SubexponentialSAT.SqrtLog.PackingHeadProgramCandidates

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairRuntimeBounds
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

open BitProgram PairScoreProgram

theorem budget_bounded (cost : List Bool → ℕ) (rows : List (List Bool)) (B C : ℕ)
    (hb : ∀ row ∈ rows, row.length ≤ B) (hc : ∀ row ∈ rows, cost row ≤ C) :
    RecordPrograms.budget cost rows ≤ rows.length * (6 * B + C + 7) := by
  induction rows with
  | nil => simp [RecordPrograms.budget]
  | cons row rows ih =>
    have hr := hb row (by simp)
    have hc' := hc row (by simp)
    have ht := ih (fun x hx => hb x (by simp [hx])) (fun x hx => hc x (by simp [hx]))
    simp only [RecordPrograms.budget, List.length_cons]
    nlinarith

end SubexponentialSAT.Subexp.PairRuntimeBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ActivePlanProgram
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

def reset (regs : Regs) : Regs := readRegs regs 0 1 none

def callbackCost (records : List (List Bool)) (threshold bits : List Bool) : ℕ :=
  (20 * bits.length + 40) * (Encoding.encodeList id records).length +
    30 * (threshold.length + bits.length + 1) + 5 * bits.length + 40

theorem encoded_filter_length_le (records : List (List Bool)) (test : List Bool → Bool) :
    (Encoding.encodeList id (records.filter test)).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp
  | cons x xs ih =>
    cases h : test x <;> simp [ h, Encoding.length_encodeList_cons] <;> omega

def sourceBound (records seeds : List (List Bool)) (threshold : List Bool) : ℕ :=
  8 + RecordPrograms.budget (callbackCost records threshold) seeds +
    10 * (Encoding.encodeList id seeds).length

theorem filter_indexRecords (seeds plan : List ℕ) (fixedCount : ℕ) :
    (indexRecords seeds).filter (keep (indexRecords plan) (unary fixedCount)) =
      indexRecords (active seeds plan fixedCount) := by
  simp only [indexRecords, active, List.filter_map]
  congr 1
  apply List.filter_congr
  intro n hn
  simp [keep, unary, List.mem_map ]

theorem active_nodup (seeds plan : List ℕ) (fixedCount : ℕ) (h : seeds.Nodup) :
    (active seeds plan fixedCount).Nodup := h.filter _

theorem callbackCost_le (records : List (List Bool)) (threshold bits : List Bool) :
    callbackCost records threshold bits ≤
      200 * ((Encoding.encodeList id records).length + threshold.length + 1) * (bits.length + 1) := by
  unfold callbackCost
  nlinarith [Nat.zero_le (bits.length * (Encoding.encodeList id records).length),
    Nat.zero_le (bits.length * threshold.length)]

theorem budget_le (records seeds : List (List Bool)) (threshold : List Bool) :
    RecordPrograms.budget (callbackCost records threshold) seeds ≤
      200 * ((Encoding.encodeList id records).length + threshold.length + 1) *
        (Encoding.encodeList id seeds).length := by
  let B := (Encoding.encodeList id records).length + threshold.length + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  induction seeds with
  | nil => simp [RecordPrograms.budget]
  | cons bits seeds ih =>
    have hc := callbackCost_le records threshold bits
    change callbackCost records threshold bits ≤ 200 * B * (bits.length + 1) at hc
    change RecordPrograms.budget (callbackCost records threshold) seeds ≤
      200 * B * (Encoding.encodeList id seeds).length at ih
    change _ ≤ 200 * B * (Encoding.encodeList id (bits :: seeds)).length
    rw [Encoding.length_encodeList_cons]
    simp only [RecordPrograms.budget, id_eq]
    have hprod : bits.length + 1 ≤ B * (bits.length + 1) := by nlinarith
    nlinarith

theorem sourceBound_le (records seeds : List (List Bool)) (threshold : List Bool) :
    sourceBound records seeds threshold ≤
      256 * ((Encoding.encodeList id records).length + threshold.length + 1) *
        ((Encoding.encodeList id seeds).length + 1) := by
  have hb := budget_le records seeds threshold
  have hB : 1 ≤ (Encoding.encodeList id records).length + threshold.length + 1 := by omega
  unfold sourceBound
  nlinarith [Nat.mul_le_mul_right (Encoding.encodeList id seeds).length hB]

def traceBoundThreshold (seeds plan : List ℕ) (threshold : List Bool) : ℕ :=
  sourceBound (indexRecords plan) (indexRecords seeds) threshold

theorem filter_indexRecords_threshold (seeds plan : List ℕ) (threshold : List Bool) :
    (indexRecords seeds).filter (keep (indexRecords plan) threshold) =
      indexRecords (active seeds plan threshold.length) := by
  have hk : keep (indexRecords plan) threshold =
      keep (indexRecords plan) (unary threshold.length) := by
    funext bits
    simp [keep, unary]
  rw [hk]
  exact filter_indexRecords seeds plan threshold.length

end SubexponentialSAT.Subexp.ActivePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The encoded first-match selector implements the actual local read-plan
index map, using an explicit table and a unary query. -/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram

theorem selectionEntries_lookup_default (currentSize : ℕ) (remaining : List ℕ) (n : ℕ) :
    ((selectionEntries currentSize remaining).lookup (unaryIndex n)).getD (unaryIndex n) =
      unaryIndex (ReadPlan.selectPosition currentSize remaining n) := by
  unfold selectionEntries
  rw [encodeEntries_lookup]
  have h := congrArg unaryIndex (ReadPlan.selectionTable_lookup_default currentSize remaining n)
  cases he : (ReadPlan.selectionTable currentSize remaining).lookup n <;>
    simpa [he] using h

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectionTableProgram
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

def pairBytes (key value : ℕ) : List Bool := Encoding.frame (unary key) ++ Encoding.frame (unary value)

def tableBytes (M : ℕ) (remaining : List ℕ) : List Bool :=
  (ReadPlan.selectionTable M remaining).flatMap (fun p => pairBytes p.1 p.2)

@[simp] theorem tableBytes_nil (M : ℕ) : tableBytes M [] = [] := rfl

@[simp] theorem tableBytes_cons (M n : ℕ) (remaining : List ℕ) :
    tableBytes M (n :: remaining) = pairBytes n M ++ tableBytes (M + 1) remaining := rfl

def indexRecords (remaining : List ℕ) : List (List Bool) := remaining.map unary

def commandCost (M : ℕ) (remaining : List ℕ) : ℕ :=
  1 + (1 + loopCost M remaining) + (3 * (tableBytes M remaining).length + 3)

def traceCost (M : ℕ) (remaining : List ℕ) : ℕ := commandCost M remaining + 1

@[simp] theorem pairBytes_length (key value : ℕ) :
    (pairBytes key value).length = 2 * key + 2 * value + 2 := by
  simp [pairBytes, unary]
  omega

theorem tableBytes_length_le (M : ℕ) (remaining : List ℕ) :
    (tableBytes M remaining).length ≤
      remaining.length * (2 * remaining.sum + 2 * (M + remaining.length) + 2) := by
  induction remaining generalizing M with
  | nil => simp
  | cons n remaining ih =>
    let B := 2 * (n + remaining.sum) + 2 * (M + (remaining.length + 1)) + 2
    have htail : (tableBytes (M + 1) remaining).length ≤ remaining.length * B :=
      (ih (M + 1)).trans (Nat.mul_le_mul_left _ (by dsimp [B]; omega))
    have hstep : 2 * n + 2 * M + 2 ≤ B := by dsimp [B]; omega
    simp only [tableBytes_cons, List.length_append, pairBytes_length,
      List.length_cons, List.sum_cons]
    calc
      _ ≤ B + remaining.length * B := Nat.add_le_add hstep htail
      _ = _ := by dsimp [B]; ring

theorem loopCost_le (M : ℕ) (remaining : List ℕ) :
    loopCost M remaining ≤
      1 + remaining.length * (17 * remaining.sum + 18 * (M + remaining.length) + 44) := by
  induction remaining generalizing M with
  | nil => simp [loopCost]
  | cons n remaining ih =>
    let B := 17 * (n + remaining.sum) + 18 * (M + (remaining.length + 1)) + 44
    have htail : loopCost (M + 1) remaining ≤ 1 + remaining.length * B :=
      (ih (M + 1)).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by dsimp [B]; omega)) _)
    have hstep : 17 * n + 18 * M + 44 ≤ B := by dsimp [B]; omega
    simp only [loopCost, callbackCost, List.length_cons, List.sum_cons]
    calc
      _ = (17 * n + 18 * M + 44) + loopCost (M + 1) remaining := by ring
      _ ≤ B + (1 + remaining.length * B) := Nat.add_le_add hstep htail
      _ = _ := by dsimp [B]; ring

/-- A fixed quadratic bound in the unary input size parameters. -/
theorem traceCost_quadratic (M : ℕ) (remaining : List ℕ) :
    traceCost M remaining ≤ 128 * (M + remaining.sum + remaining.length + 1) ^ 2 := by
  let t := M + remaining.sum + remaining.length + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hl : remaining.length ≤ t := by dsimp [t]; omega
  have hs : remaining.sum ≤ t := by dsimp [t]; omega
  have hm : M + remaining.length ≤ t := by dsimp [t]; omega
  have hloop : loopCost M remaining ≤ 1 + t * (17 * t + 18 * t + 44) :=
    (loopCost_le M remaining).trans (by gcongr)
  have htable : (tableBytes M remaining).length ≤ t * (2 * t + 2 * t + 2) :=
    (tableBytes_length_le M remaining).trans (by gcongr)
  dsimp [traceCost, commandCost]
  change _ ≤ 128 * t ^ 2
  have ht2 : t ≤ t ^ 2 := by nlinarith
  nlinarith

end SubexponentialSAT.Subexp.SelectionTableProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

open BitProgram StructuredCalls

theorem mappedRecords_selection (currentSize : ℕ) (remaining plan : List ℕ) :
    mappedRecords (SelectorProgram.selectionEntries currentSize remaining)
      (plan.reverse.map SelectorProgram.unaryIndex) =
    plan.map (fun n => SelectorProgram.unaryIndex
      (ReadPlan.selectPosition currentSize remaining n)) := by
  simp [mappedRecords, selected, List.map_map, Function.comp_def,
    SelectorProgram.selectionEntries_lookup_default, List.map_reverse]

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorPairProgram
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

def payload (left right : List Bool) : List Bool :=
  Encoding.frame left ++ Encoding.frame right

def frameCost (left right : List Bool) : ℕ :=
  5 * left.length + 8 * right.length + 8 * (payload left right).length + 23

end SubexponentialSAT.Subexp.SelectorPairProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationProgram
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

theorem activeUnary_eq : ActivePlanProgram.unary = SelectionTableProgram.unary := rfl

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MinimumProgram
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

theorem choose_pick (a b : ℕ × ℕ) (xs : List (ℕ × ℕ)) :
    NaturalAssignment.chooseMinNat Prod.fst (pick a b) xs =
      pick a (NaturalAssignment.chooseMinNat Prod.fst b xs) := by
  cases xs with
  | nil => rfl
  | cons c cs =>
      change pick (pick a b) (NaturalAssignment.chooseMinNat Prod.fst c cs) =
        pick a (pick b (NaturalAssignment.chooseMinNat Prod.fst c cs))
      exact pick_assoc _ _ _

theorem scan_eq_chooseMin (current : ℕ × ℕ) (next : ℕ) (records : List (List Bool)) :
    scan current next records =
      NaturalAssignment.chooseMinNat Prod.fst current (tagged next records) := by
  induction records generalizing current next with
  | nil => rfl
  | cons bits rest ih =>
      rw [scan, ih, tagged, choose_pick]
      rfl

theorem firstMinimum_eq_chooseMin (first : List Bool) (rest : List (List Bool)) :
    firstMinimum first rest =
      NaturalAssignment.chooseMinNat Prod.fst (first.length, 0) (tagged 1 rest) :=
  scan_eq_chooseMin _ _ _

theorem indexChoice_value {A : Type*} (score : A → ℕ)
    (next : ℕ) (a : A) (tail : List A) :
    (indexChoice score next a tail).2 = NaturalAssignment.chooseMinNat score a tail := by
  induction tail generalizing next a with
  | nil => rfl
  | cons b bs ih =>
      simp only [indexChoice, NaturalAssignment.chooseMinNat, ih]
      split <;> simp_all only []

theorem chooseTagged_indexChoice {A : Type*} (score : A → ℕ)
    (next : ℕ) (a : A) (tail : List A) :
    NaturalAssignment.chooseMinNat Prod.fst (score a, next)
      (tagged (next + 1) (tail.map (fun x => UnaryCompare.encode (score x)))) =
      (score (indexChoice score next a tail).2, (indexChoice score next a tail).1) := by
  induction tail generalizing next a with
  | nil => rfl
  | cons b bs ih =>
      have hlen (x : A) : (UnaryCompare.encode (score x)).length = score x := by
        simp [UnaryCompare.encode]
      simp only [List.map_cons, tagged, hlen, NaturalAssignment.chooseMinNat, ih, indexChoice]
      split <;> simp_all

end SubexponentialSAT.Subexp.MinimumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramCounts
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

theorem completionCount_zero (alphabet : List W) (remaining : List A) (ω : A → W) :
    completionCount alphabet (fun _ => 0) remaining ω = 0 := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i rest ih => simp [completionCount, ih]

end General

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BasisTransposePlanProgram
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

theorem multiply_output (N n : ℕ) (out : List Bool) :
    downOutput (fun _ acc => unary N ++ acc) n out = unary (n * N) ++ out := by
  induction n generalizing out with
  | zero => simp [downOutput, unary]
  | succ n ih =>
    rw [downOutput, ih]
    simp only [unary, Nat.add_mul, one_mul]
    rw [← List.append_assoc, ← List.replicate_add]

end SubexponentialSAT.Subexp.BasisTransposePlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefixProgram
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

theorem mulStack_injective : Function.Injective mulStack := by decide

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed binary machine combines the two collision counts. Its instruction
count and every output length are charged in terms of actual input bit lengths. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

abbrev ArithmeticData := SubexponentialSAT.StructuredProgram.State 8 12

def arithmeticInputLength (d : ArithmeticData) : ℕ :=
  (d.stacks 0).length + (d.stacks 1).length +
    (d.stacks 2).length + (d.stacks 3).length

def arithmeticReady (d : ArithmeticData) : Prop :=
  ∀ j : Fin 12, 4 ≤ j.val → d.stacks j = []

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramGateBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem unaryRegisters_injective : Function.Injective unaryRegisters := Fin.castAdd_injective _ _
theorem unaryStacks_injective : Function.Injective unaryStacks := by decide
theorem compareStacks_injective : Function.Injective compareStacks := by decide

end SubexponentialSAT.SqrtLog.PackingWeightProgram.Gate

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeadSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native head-stage gate and paid extraction of its prior-word prefix. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem gateRegisters_injective : Function.Injective gateRegisters := Fin.castAdd_injective _ _
theorem gatePorts_injective : Function.Injective gatePorts := by decide

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyHeads
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual head-score production from the controller table and alphabet. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

theorem headRegisters_injective : Function.Injective headRegisters := Fin.castAdd_injective _ _

theorem headPorts_injective : Function.Injective headPorts := by decide

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Dropping a candidate-independent offset is justified by an exact ordering
proof. The real controller remains unchanged, and its score builder must still
satisfy an actual execution contract. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 theorem chooseMinNat_eq_of_order {A : Type*} (f g : A → ℕ)
    (h : ∀ a b, f a ≤ f b ↔ g a ≤ g b) (a : A) (tail : List A) :
    NaturalAssignment.chooseMinNat f a tail = NaturalAssignment.chooseMinNat g a tail := by
  induction tail generalizing a with
  | nil => rfl
  | cons b tail ih => simp only [NaturalAssignment.chooseMinNat, ih, h]

 theorem assignNat_eq_of_order {A : Type*} (a : A) (tail : List A)
    (f g : ℕ → List A → ℕ) (total : ℕ)
    (h : ∀ n fixed, n+1+fixed.length = total → ∀ x y,
      f n (x::fixed) ≤ f n (y::fixed) ↔ g n (x::fixed) ≤ g n (y::fixed))
    (n : ℕ) (fixed : List A) (hs : n+fixed.length = total) :
    NaturalAssignment.assignNat a tail f n fixed =
      NaturalAssignment.assignNat a tail g n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih =>
    have ho := h n fixed (by omega)
    have hc := chooseMinNat_eq_of_order (fun x => f n (x::fixed))
      (fun x => g n (x::fixed)) ho a tail
    simp only [NaturalAssignment.assignNat, hc]
    apply ih
    simp only [List.length_cons]
    omega

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary-counted copier scales a unary score, preserving both inputs.
The loop count is read from the multiplier stack and every copied bit is paid. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 def scaleBudget (bits : List Bool) (count : ℕ) : ℕ :=
  9*bits.length+8 + SubexponentialSAT.CounterPrograms.value bits*(7*count+5) +
    (SubexponentialSAT.CounterPrograms.value bits+1)*(16*bits.length+16)

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramStreams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp


 def value (wi wh : List Bool) (p : ℕ × ℕ) :=
  SubexponentialSAT.CounterPrograms.value wi*p.1 + SubexponentialSAT.CounterPrograms.value wh*p.2
 def payload (p : ℕ × ℕ) : List Bool :=
  SubexponentialSAT.Encoding.frame (List.replicate p.1 false) ++
    SubexponentialSAT.Encoding.frame (List.replicate p.2 false)
 def pairBudget (wi wh : List Bool) (p : ℕ × ℕ) :=
  scaleBudget wi p.1 + scaleBudget wh p.2 + 8*(p.1+p.2) + 4*value wi wh p + 25

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramStreamLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The real dynamic loop over paired candidate counts. The pair list occurs
only in the input specification; the finite program reads runtime list tags. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

 def pairsBytes : List (ℕ × ℕ) → List Bool
  | [] => [false]
  | p::ps => true :: (payload p ++ pairsBytes ps)
 def afterSource : List (ℕ × ℕ) → List Bool
  | [] => []
  | p::ps => payload p ++ pairsBytes ps
 def flag : List (ℕ × ℕ) → Bool
  | [] => false
  | _::_ => true
 def resultBody (wi wh : List Bool) : List (ℕ × ℕ) → List Bool
  | [] => []
  | p::ps => (true :: SubexponentialSAT.Encoding.frame (List.replicate (value wi wh p) false)) ++ resultBody wi wh ps
 def loopBudget (wi wh : List Bool) : List (ℕ × ℕ) → ℕ
  | [] => 1
  | p::ps => pairBudget wi wh p + loopBudget wi wh ps + 2

 theorem bytes_tag (ps : List (ℕ × ℕ)) : pairsBytes ps = flag ps :: afterSource ps := by
  cases ps <;> rfl

 def scores (wi wh : List Bool) (ps : List (ℕ × ℕ)) : List (List Bool) :=
  ps.map (fun p => List.replicate (value wi wh p) false)

 def streamBudget (wi wh : List Bool) (ps : List (ℕ × ℕ)) :=
  loopBudget wi wh ps + 3*(resultBody wi wh ps).length + 10

end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramStreamBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial bounds for every bit moved by the weighted stream
combiner. The bounds include unary value lengths, not only input bit widths. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams

 theorem scaleBudget_bound (bits : List Bool) (count B W C : ℕ)
    (hb : bits.length ≤ B) (hw : SubexponentialSAT.CounterPrograms.value bits ≤ W) (hc : count ≤ C) :
    scaleBudget bits count ≤ 64*(W+1)*(B+C+1) := by
  have h1 : SubexponentialSAT.CounterPrograms.value bits*(7*count+5) ≤ W*(7*C+5) :=
    Nat.mul_le_mul hw (by omega)
  have h2 : (SubexponentialSAT.CounterPrograms.value bits+1)*(16*bits.length+16) ≤
      (W+1)*(16*B+16) := Nat.mul_le_mul (by omega) (by omega)
  unfold scaleBudget
  nlinarith

 theorem value_bound (wi wh : List Bool) (p : ℕ × ℕ) (W C : ℕ)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : p.1 ≤ C) (hd : p.2 ≤ C) : value wi wh p ≤ 2*W*C := by
  have h1 := Nat.mul_le_mul hi hc
  have h2 := Nat.mul_le_mul hh hd
  unfold value
  nlinarith

 theorem pairBudget_bound (wi wh : List Bool) (p : ℕ × ℕ) (B W C : ℕ)
    (hbi : wi.length ≤ B) (hbh : wh.length ≤ B)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : p.1 ≤ C) (hd : p.2 ≤ C) :
    pairBudget wi wh p ≤ 200*(W+1)*(B+C+1) := by
  have h1 := scaleBudget_bound wi p.1 B W C hbi hi hc
  have h2 := scaleBudget_bound wh p.2 B W C hbh hh hd
  have h3 := value_bound wi wh p W C hi hh hc hd
  unfold pairBudget
  nlinarith

 theorem resultBody_length_bound (wi wh : List Bool) (ps : List (ℕ × ℕ)) (W C : ℕ)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    (resultBody wi wh ps).length ≤ ps.length*(4*W*C+2) := by
  induction ps with
  | nil => simp [resultBody]
  | cons p ps ih =>
    have hp := hc p (by simp)
    have hv := value_bound wi wh p W C hi hh hp.1 hp.2
    have ht := ih (fun a ha => hc a (by simp [ha]))
    simp only [resultBody,List.length_append,List.length_cons,SubexponentialSAT.Encoding.length_frame,
      List.length_replicate]
    nlinarith

 theorem loopBudget_bound (wi wh : List Bool) (ps : List (ℕ × ℕ)) (B W C : ℕ)
    (hbi : wi.length ≤ B) (hbh : wh.length ≤ B)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    loopBudget wi wh ps ≤ ps.length*(200*(W+1)*(B+C+1)+2)+1 := by
  induction ps with
  | nil => simp [loopBudget]
  | cons p ps ih =>
    have hp := hc p (by simp)
    have h1 := pairBudget_bound wi wh p B W C hbi hbh hi hh hp.1 hp.2
    have h2 := ih (fun a ha => hc a (by simp [ha]))
    simp only [loopBudget,List.length_cons]
    nlinarith

 theorem streamBudget_bound (wi wh : List Bool) (ps : List (ℕ × ℕ)) (B W C : ℕ)
    (hbi : wi.length ≤ B) (hbh : wh.length ≤ B)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    streamBudget wi wh ps+1 ≤ 300*(ps.length+1)*(W+1)*(B+C+1) := by
  have h1 := loopBudget_bound wi wh ps B W C hbi hbh hi hh hc
  have h2 := resultBody_length_bound wi wh ps W C hi hh hc
  unfold streamBudget
  nlinarith [Nat.zero_le (ps.length*W*B), Nat.zero_le (ps.length*W*C),
    Nat.zero_le (ps.length*B), Nat.zero_le (ps.length*C), Nat.zero_le (W*B), Nat.zero_le (W*C)]
end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDotControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control dot products on serialized field elements

The multiplication and addition interfaces below are actual finite-program
trace contracts. The concrete endpoint instantiates them with flat quartic
arithmetic at modulus p. Stack 77 is the accumulator and stack 78 is the stream
of row/input pairs; both remain outside the 77-stack multiplication service.
-/

namespace SubexponentialSAT.SubexpDotControl

open BitProgram StructuredCalls
open scoped BigOperators

def payload {C : Type*} (encode : C → List Bool) (pair : C × C) : List Bool :=
  Encoding.frame (encode pair.1).reverse ++ Encoding.frame (encode pair.2).reverse

abbrev encodePairs {C : Type*} (encode : C → List Bool) : List (C × C) → List Bool
  | [] => [false]
  | pair :: rest => true :: (payload encode pair ++ encodePairs encode rest)

def listFlag {C : Type*} : List (C × C) → Bool
  | [] => false
  | _ :: _ => true

end SubexponentialSAT.SubexpDotControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpInputZip
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

open BitProgram StructuredCalls

def record (left right : List Bool) : List Bool :=
  true :: (Encoding.frame left.reverse ++ Encoding.frame right.reverse)

theorem record_length (left right : List Bool) :
    (record left right).length = 2 * left.length + 2 * right.length + 3 := by
  simp [record, Encoding.length_frame]
  omega

def rowAfter : List (List Bool × List Bool) → List Bool → List Bool
  | [], suffix => suffix
  | (left, _) :: rest, suffix => Encoding.frame left ++ Encoding.encodeList id (rowWords rest) ++ suffix

def inputAfter : List (List Bool × List Bool) → List Bool → List Bool
  | [], suffix => suffix
  | (_, right) :: rest, suffix => Encoding.frame right ++ Encoding.encodeList id (inputWords rest) ++ suffix

theorem row_tag (pairs : List (List Bool × List Bool)) (suffix : List Bool) :
    Encoding.encodeList id (rowWords pairs) ++ suffix =
      SubexpDotControl.listFlag pairs :: rowAfter pairs suffix := by
  cases pairs <;> simp [rowWords, Encoding.encodeList, rowAfter, SubexpDotControl.listFlag, List.append_assoc]

theorem input_tag (pairs : List (List Bool × List Bool)) (suffix : List Bool) :
    Encoding.encodeList id (inputWords pairs) ++ suffix =
      SubexpDotControl.listFlag pairs :: inputAfter pairs suffix := by
  cases pairs <;> simp [inputWords, Encoding.encodeList, inputAfter, SubexpDotControl.listFlag, List.append_assoc]

def pairBody : List (List Bool × List Bool) → List Bool
  | [] => []
  | (left, right) :: rest => record left right ++ pairBody rest

def inputBits : List (List Bool × List Bool) → ℕ
  | [] => 0
  | (left, right) :: rest => left.length + right.length + inputBits rest

def scanCost : List (List Bool × List Bool) → ℕ
  | [] => 1
  | (left, right) :: rest => 20 * left.length + 20 * right.length + 44 + scanCost rest

theorem pairBody_length (pairs : List (List Bool × List Bool)) :
    (pairBody pairs).length = 2 * inputBits pairs + 3 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    simp only [pairBody, List.length_append, record_length, inputBits, List.length_cons, ih]
    omega

theorem scanCost_eq (pairs : List (List Bool × List Bool)) :
    scanCost pairs = 20 * inputBits pairs + 44 * pairs.length + 1 := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    simp only [scanCost, inputBits, List.length_cons, ih]
    omega

theorem pairBody_encodePairs (pairs : List (List Bool × List Bool)) :
    pairBody pairs ++ [false] = SubexpDotControl.encodePairs id pairs := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    simp only [pairBody, record, List.cons_append, List.append_assoc, ih,
      SubexpDotControl.encodePairs, SubexpDotControl.payload, id_eq]

end SubexponentialSAT.SubexpInputZip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramZip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual pairing and weighting of two candidate-ordered unary score streams.
This is one fixed finite program; no precomputed pair list is an input premise. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Zip
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem rawPairs_bytes (ps : List (ℕ × ℕ)) :
    SubexponentialSAT.SubexpDotControl.encodePairs id (rawPairs ps) = Streams.pairsBytes ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp [rawPairs,SubexponentialSAT.SubexpDotControl.encodePairs,SubexponentialSAT.SubexpDotControl.payload,
      Streams.pairsBytes,Streams.payload]
    exact ih

 def budget (wi wh : List Bool) (ps : List (ℕ × ℕ)) :=
  26*SubexponentialSAT.SubexpInputZip.inputBits (rawPairs ps)+53*ps.length+12 +
    Streams.streamBudget wi wh ps+1

 theorem inputBits_bound (ps : List (ℕ × ℕ)) (C : ℕ)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    SubexponentialSAT.SubexpInputZip.inputBits (rawPairs ps) ≤ 2*C*ps.length := by
  induction ps with
  | nil => simp [rawPairs,SubexponentialSAT.SubexpInputZip.inputBits]
  | cons p ps ih =>
    have hp := hc p (by simp)
    have ht := ih (fun a ha => hc a (by simp [ha]))
    simp only [rawPairs,List.map_cons,SubexponentialSAT.SubexpInputZip.inputBits,
      List.length_replicate,List.length_cons]
    simp only [rawPairs] at ht
    nlinarith

 theorem budget_bound (wi wh : List Bool) (ps : List (ℕ × ℕ)) (B W C : ℕ)
    (hbi : wi.length ≤ B) (hbh : wh.length ≤ B)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    budget wi wh ps+1 ≤ 500*(ps.length+1)*(W+1)*(B+C+1) := by
  have hz := inputBits_bound ps C hc
  have hs := Streams.streamBudget_bound wi wh ps B W C hbi hbh hi hh hc
  unfold budget
  nlinarith [Nat.zero_le (ps.length*W*B),Nat.zero_le (ps.length*W*C),
    Nat.zero_le (ps.length*B),Nat.zero_le (ps.length*C),Nat.zero_le (W*B),Nat.zero_le (W*C)]
end SubexponentialSAT.SqrtLog.PackingProgram.Zip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
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

theorem encodeNat_mem (v : ℕ) (scope : List ℕ) :
    Encoding.encodeNat v ∈ scope.map Encoding.encodeNat ↔ v ∈ scope := by
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := List.mem_map.mp h
    exact Encoding.encodeNat_injective he ▸ hx
  · intro h
    exact List.mem_map.mpr ⟨v, h, rfl⟩

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-output physical calls in the assignment-input workspace. -/

namespace SubexponentialSAT.Subexp.AssignmentInputCall

open BitProgram StructuredCalls

abbrev Data := State 16 48

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical input boundary for assignment-alphabet construction. -/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls

abbrev Data := State 16 48

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentRecordViews
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

open BitProgram StructuredCalls TupleProgram

theorem firstTwo_injective : Function.Injective firstTwo := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 3 => x.val) h)

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_OneHotAlphabetProgram
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

def poppedRegs (regs : Fin 5 → Bool) (n : ℕ) : Fin 5 → Bool :=
  readRegs regs 3 4 (unary n).head?

end SubexponentialSAT.Subexp.OneHotAlphabetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls


def mapFactor {A B : Type*} (f : A → B) (a : Factor A) : Factor B :=
  ⟨f a.inverseDifference, f a.negativeNode⟩

def mapTerm {A B : Type*} (f : A → B) (a : Term A) : Term B :=
  ⟨f a.value, f a.inverseNode, a.factors.map (mapFactor f)⟩

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end


